use petgraph::algo::is_cyclic_directed;
use petgraph::stable_graph::NodeIndex;
use petgraph::stable_graph::StableDiGraph;
use regex::Regex;
use std::collections::HashMap;
use std::iter::Peekable;

#[derive(Debug, Clone, PartialEq)]
pub enum Associativity {
    Left,
    Right,
    None,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Fixity {
    Prefix,
    Infix(Associativity),
    Postfix,
    Closed,
}

#[derive(Debug, PartialEq)]
pub struct Operator {
    pub fixity: Fixity,
    pub name: String,
}

#[derive(Debug, PartialEq)]
pub struct NamePart(Vec<Option<String>>);

#[derive(Debug)]
pub struct OperatorPart {
    pub fixity: Fixity,
    pub name: String,
    pub part: NamePart,
}

impl Operator {
    pub fn new(fixity: Fixity, name: &str) -> Operator {
        let re = Regex::new("_+").unwrap();
        let name = re.replace_all(name, "_").to_string();
        Operator { fixity, name }
    }
}

impl From<&str> for NamePart {
    fn from(s: &str) -> Self {
        let mut result = Vec::new();
        let mut last = 0;
        for (index, matched) in s.match_indices('_') {
            if last != index {
                result.push(Some(s[last..index].to_string()));
            }
            result.push(None);
            last = index + matched.len();
        }
        if last < s.len() {
            result.push(Some(s[last..].to_string()));
        }
        NamePart(result)
    }
}

impl OperatorPart {
    pub fn new(op: &Operator) -> Self {
        let name = op.name.to_string();
        let fixity = op.fixity.clone();
        let part = op.name.as_str().into();
        Self { fixity, name, part }
    }
}

#[derive(Debug)]
pub enum PrecedenceRelation {
    Tighter,
    Looser,
    Equal,
    Undefined,
}

#[derive(Debug)]
pub struct PrecedenceGraph {
    graph: StableDiGraph<Vec<OperatorPart>, ()>,
    map: HashMap<String, NodeIndex>,
}

impl PrecedenceGraph {
    pub fn new() -> Self {
        Self {
            graph: StableDiGraph::new(),
            map: HashMap::new(),
        }
    }

    pub fn compare(&self, lhs: &Operator, rhs: &Operator) -> Option<PrecedenceRelation> {
        let &lhs_index = self.map.get(&lhs.name)?;
        let &rhs_index = self.map.get(&rhs.name)?;
        match (
            self.graph.find_edge(lhs_index, rhs_index),
            self.graph.find_edge(rhs_index, lhs_index),
        ) {
            (Some(_), Some(_)) if lhs == rhs => Some(PrecedenceRelation::Equal),
            (Some(_), Some(_)) => None, // cyclic
            (Some(_), None) => Some(PrecedenceRelation::Tighter),
            (None, Some(_)) => Some(PrecedenceRelation::Looser),
            (None, None) => Some(PrecedenceRelation::Undefined),
        }
    }

    fn get_or_insert_operator_node_index(&mut self, op: &Operator) -> &mut NodeIndex {
        return self
            .map
            .entry(op.name.to_string())
            .or_insert_with(|| self.graph.add_node(vec![OperatorPart::new(op)]));
    }

    fn add_tighter(&mut self, new_op: &Operator, another_op: &Operator) {
        let &mut new_op_index = self.get_or_insert_operator_node_index(new_op);
        let &mut another_op_index = self.get_or_insert_operator_node_index(another_op);
        if self
            .graph
            .find_edge(another_op_index, new_op_index)
            .is_none()
        {
            self.graph.add_edge(another_op_index, new_op_index, ());
        }
    }

    pub fn is_acyclic(&self) -> bool {
        !is_cyclic_directed(&self.graph)
    }

    pub fn add(&mut self, new: &Operator, prec: PrecedenceRelation, another: &Operator) -> bool {
        if new != another {
            match prec {
                PrecedenceRelation::Tighter => self.add_tighter(new, another),
                PrecedenceRelation::Looser => self.add_tighter(another, new),
                PrecedenceRelation::Equal => {
                    let &index = match (self.map.get(&new.name), self.map.get(&another.name)) {
                        (Some(v1), Some(v2)) if v1 == v2 => v1,
                        (Some(_), Some(_)) => return false,
                        (None, None) => self.get_or_insert_operator_node_index(another),
                        (None, Some(v)) => v,
                        (Some(v), None) => v,
                    };
                    self.graph[index].push(OperatorPart::new(new));
                    self.map.entry(new.name.to_string()).or_insert(index);
                    self.map.entry(another.name.to_string()).or_insert(index);
                }
                PrecedenceRelation::Undefined => panic!("undefined precedence relation"),
            }
            return true;
        }
        false
    }
}

pub type ParserResult<I, O, E> = Result<(I, O), E>;

#[derive(Debug, PartialEq)]
pub enum ParseError {
    UnexpectedToken(usize),
    UnexpectedEndOfInput,
}

pub trait Input: Sized {
    fn take(&self, n: usize) -> Self;
    fn take_split(&self, n: usize) -> (Self, Self);
}

pub trait Parser {
    type I: Input;
    type O;
    fn parse(&self, i: Self::I) -> ParserResult<Self::I, Self::O, ParseError>;
}

impl<P: Parser> Parser for &P {
    type I = P::I;
    type O = P::O;
    fn parse(&self, i: Self::I) -> ParserResult<Self::I, Self::O, ParseError> {
        (*self).parse(i)
    }
}

#[cfg(test)]
mod tests {
    use petgraph::dot::Config;
    use petgraph::dot::Dot;

    use super::*;
    #[test]
    fn test() {
        let mut graph = PrecedenceGraph::new();
        let parenthesis = Operator::new(Fixity::Closed, "(_)");
        let add = Operator::new(Fixity::Infix(Associativity::Left), "_+_");
        let sub = Operator::new(Fixity::Infix(Associativity::Left), "_-_");
        let eq = Operator::new(Fixity::Infix(Associativity::Left), "_==_");
        let land = Operator::new(Fixity::Infix(Associativity::Left), "_&&_");
        let fact = Operator::new(Fixity::Postfix, "_!");
        let if_then_else = Operator::new(Fixity::Prefix, "if_then_else_");

        graph.add(&add, PrecedenceRelation::Equal, &sub);
        graph.add(&parenthesis, PrecedenceRelation::Tighter, &add);
        graph.add(&parenthesis, PrecedenceRelation::Tighter, &fact);
        graph.add(&parenthesis, PrecedenceRelation::Tighter, &if_then_else);
        graph.add(&add, PrecedenceRelation::Tighter, &eq);
        graph.add(&eq, PrecedenceRelation::Looser, &fact);
        graph.add(&eq, PrecedenceRelation::Tighter, &land);
        graph.add(&land, PrecedenceRelation::Looser, &parenthesis);
        graph.add(&eq, PrecedenceRelation::Looser, &parenthesis);

        assert!(graph.is_acyclic());
        println!(
            "{:?}",
            Dot::with_config(&graph.graph, &[Config::EdgeNoLabel])
        );
        println!("{:?}", graph.map);
    }
}
