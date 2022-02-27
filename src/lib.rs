use either::Either;
use either::Left;
use either::Right;
use petgraph::algo::is_cyclic_directed;
use petgraph::stable_graph::NodeIndex;
use petgraph::stable_graph::StableDiGraph;
use petgraph::visit::Bfs;
use regex::Regex;
use std::collections::HashMap;
use std::fmt::Debug;

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum Associativity {
    Left,
    Right,
    None,
}

#[derive(Debug, Clone, PartialEq, Copy)]
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

#[derive(Debug, PartialEq, Clone)]
pub struct NamePart(Vec<Option<String>>);

#[derive(Debug, Clone)]
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
        let mut result = vec![];
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

        if let Some(None) = result.last() {
            result.pop();
        }

        if let Some(None) = result.first() {
            result.remove(0);
        }

        NamePart(result)
    }
}

impl OperatorPart {
    pub fn new(op: &Operator) -> Self {
        let name = op.name.to_string();
        let fixity = op.fixity;
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

pub trait PrecedenceGraph {
    type P: Copy;
    fn ops(&self, prec: Self::P, fix: Fixity) -> Vec<&OperatorPart>;
    fn succ(&self, prec: Self::P) -> Vec<Self::P>;
    fn all(&self) -> Vec<Self::P>;
}

impl PrecedenceGraph for StableDiGraph<Vec<OperatorPart>, ()> {
    type P = NodeIndex;

    fn ops(&self, prec: Self::P, fix: Fixity) -> Vec<&OperatorPart> {
        self[prec].iter().filter(|o| o.fixity == fix).collect()
    }

    fn succ(&self, prec: Self::P) -> Vec<Self::P> {
        let mut succ = vec![];
        let mut bfs = Bfs::new(self, prec);
        while let Some(n) = bfs.next(self) {
            if n != prec {
                succ.push(n);
            }
        }
        succ
    }

    fn all(&self) -> Vec<Self::P> {
        self.node_indices().collect()
    }
}

#[derive(Debug)]
pub struct MappedPrecedenceGraph {
    graph: StableDiGraph<Vec<OperatorPart>, ()>,
    map: HashMap<String, NodeIndex>,
}

impl Default for MappedPrecedenceGraph {
    fn default() -> Self {
        Self::new()
    }
}

impl MappedPrecedenceGraph {
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

pub trait ParserInput: PartialEq + Clone + Debug {
    fn take(&self, n: usize) -> Option<Self>;
    fn take_split(&self, n: usize) -> Option<(Self, Self)>;
    fn take_split_if(&self, f: impl FnOnce(Self) -> bool, n: usize) -> Option<(Self, Self)>;
    fn size(&self) -> usize;
}

#[derive(Debug, PartialEq)]
pub enum ParseError {
    UnexpectedToken(usize),
    UnexpectedEndOfInput,
    UnparsedInput,
}

pub trait Compare<T> {
    fn compare(&self, other: T) -> bool;
}

impl<'a> ParserInput for &'a str {
    fn take(&self, n: usize) -> Option<Self> {
        if self.len() >= n {
            Some(&self[..n])
        } else {
            None
        }
    }
    fn take_split(&self, n: usize) -> Option<(Self, Self)> {
        if self.len() >= n {
            Some((&self[..n], &self[n..]))
        } else {
            None
        }
    }
    fn take_split_if(&self, f: impl FnOnce(Self) -> bool, n: usize) -> Option<(Self, Self)> {
        if self.len() >= n && f(&self[..n]) {
            Some((&self[..n], &self[n..]))
        } else {
            None
        }
    }
    fn size(&self) -> usize {
        self.len()
    }
}

pub trait Parser<I, O>
where
    I: ParserInput,
{
    fn parse(&self, i: I) -> ParserResult<I, O, ParseError>;
}

impl<I, O, P> Parser<I, O> for &P
where
    I: ParserInput,
    P: Parser<I, O>,
{
    fn parse(&self, i: I) -> ParserResult<I, O, ParseError> {
        (*self).parse(i)
    }
}

impl<I, O> Parser<I, O> for &dyn Parser<I, O>
where
    I: ParserInput,
{
    fn parse(&self, i: I) -> ParserResult<I, O, ParseError> {
        (*self).parse(i)
    }
}

pub struct SkipSpace();
impl<'a, I> Parser<I, ()> for SkipSpace
where
    I: ParserInput + Compare<&'a str>,
{
    fn parse(&self, i: I) -> ParserResult<I, (), ParseError> {
        let mut i = i;
        while let Some((_, rest)) = i.take_split_if(
            |s| s.compare(" ") || s.compare("\n") || s.compare("\r") || s.compare("\t"),
            1,
        ) {
            i = rest;
        }
        Ok((i, ()))
    }
}

pub struct Tag<T>(T);
impl<I, T> Parser<I, ()> for Tag<T>
where
    I: ParserInput + Compare<T>,
    T: ParserInput,
{
    fn parse(&self, i: I) -> ParserResult<I, (), ParseError> {
        let t = self.0.clone();
        if let Some((tok, rest)) = i.take_split(self.0.size()) {
            if tok.compare(t) {
                Ok((rest, ()))
            } else {
                Err(ParseError::UnexpectedToken(rest.size()))
            }
        } else {
            Err(ParseError::UnexpectedEndOfInput)
        }
    }
}

impl<I, O1, O2, P1, P2> Parser<I, (O1, O2)> for (P1, P2)
where
    I: ParserInput,
    P1: Parser<I, O1>,
    P2: Parser<I, O2>,
{
    fn parse(&self, i: I) -> ParserResult<I, (O1, O2), ParseError> {
        let (p1, p2) = self;
        let (rest, o1) = p1.parse(i)?;
        let (rest, o2) = p2.parse(rest)?;
        Ok((rest, (o1, o2)))
    }
}
impl<I, O1, O2, O3, P1, P2, P3> Parser<I, (O1, O2, O3)> for (P1, P2, P3)
where
    I: ParserInput,
    P1: Parser<I, O1>,
    P2: Parser<I, O2>,
    P3: Parser<I, O3>,
{
    fn parse(&self, i: I) -> ParserResult<I, (O1, O2, O3), ParseError> {
        let (p1, p2, p3) = self;
        let (rest, o1) = p1.parse(i)?;
        let (rest, o2) = p2.parse(rest)?;
        let (rest, o3) = p3.parse(rest)?;
        Ok((rest, (o1, o2, o3)))
    }
}

struct Or<P1, P2>(P1, P2);
impl<I, O1, O2, P1, P2> Parser<I, Either<O1, O2>> for Or<P1, P2>
where
    I: ParserInput,
    P1: Parser<I, O1>,
    P2: Parser<I, O2>,
{
    fn parse(&self, i: I) -> ParserResult<I, Either<O1, O2>, ParseError> {
        let (p1, p2) = (&self.0, &self.1);
        match (p1.parse(i.clone()), p2.parse(i.clone())) {
            (Ok((rest1, o1)), Ok((rest2, o2))) => {
                if rest1.size() < rest2.size() {
                    Ok((rest1, Left(o1)))
                } else {
                    Ok((rest2, Right(o2)))
                }
            }
            (Ok((rest, o1)), _) => Ok((rest, Left(o1))),
            (_, Ok((rest, o2))) => Ok((rest, Right(o2))),
            _ => Err(ParseError::UnexpectedToken(i.size())),
        }
    }
}

struct Alt<P>(Vec<P>);
impl<I, O, P> Parser<I, O> for Alt<P>
where
    I: ParserInput,
    P: Parser<I, O>,
{
    fn parse(&self, i: I) -> ParserResult<I, O, ParseError> {
        let mut oks = vec![];
        for p in &self.0 {
            if let Ok(ok) = p.parse(i.clone()) {
                oks.push(ok);
            }
        }
        let r = oks.into_iter().min_by_key(|(rest, _)| rest.size());
        r.ok_or_else(|| ParseError::UnexpectedToken(i.size()))
    }
}

struct Seq<P>(Vec<P>);
impl<I, O, P> Parser<I, Vec<O>> for Seq<P>
where
    I: ParserInput,
    P: Parser<I, O>,
{
    fn parse(&self, i: I) -> ParserResult<I, Vec<O>, ParseError> {
        let mut s = i;
        let mut r = vec![];
        for p in &self.0 {
            let (i, o) = p.parse(s)?;
            r.push(o);
            s = i;
        }
        Ok((s, r))
    }
}

struct Many1<P>(P);
impl<I, O, P> Parser<I, Vec<O>> for Many1<P>
where
    I: ParserInput,
    P: Parser<I, O>,
{
    fn parse(&self, i: I) -> ParserResult<I, Vec<O>, ParseError> {
        let (mut s, o) = self.0.parse(i)?;
        let mut v = vec![o];
        while let Ok((rest, o)) = self.0.parse(s.clone()) {
            s = rest;
            v.push(o);
        }
        Ok((s, v))
    }
}

#[derive(Debug)]
pub struct Tree {
    pub op: OperatorPart,
    pub input: Vec<Tree>,
}

struct Expr<'a, G: PrecedenceGraph>(&'a G);
impl<'a, I, G> Parser<I, Tree> for Expr<'a, G>
where
    I: ParserInput + Compare<&'a str>,
    G: PrecedenceGraph,
{
    fn parse(&self, i: I) -> ParserResult<I, Tree, ParseError> {
        Precs(self.0, self.0.all()).parse(i)
    }
}

struct Precs<'a, G: PrecedenceGraph>(&'a G, Vec<G::P>);
impl<'a, I, G> Parser<I, Tree> for Precs<'a, G>
where
    I: ParserInput + Compare<&'a str>,
    G: PrecedenceGraph,
{
    fn parse(&self, i: I) -> ParserResult<I, Tree, ParseError> {
        let prec = self.1.iter().map(|&p| Prec(self.0, p)).collect();
        Alt(prec).parse(i)
    }
}

struct Op<'a, G: PrecedenceGraph>(&'a G, &'a OperatorPart);
impl<'a, I, G> Parser<I, Tree> for Op<'a, G>
where
    I: ParserInput + Compare<&'a str>,
    G: PrecedenceGraph,
{
    fn parse(&self, i: I) -> ParserResult<I, Tree, ParseError> {
        let op = self.1;
        let parts = &op.part.0;
        let mut vec = vec![];
        let mut next = i;
        for part in parts {
            if let Some(s) = part {
                let (rest, _) = SkipSpace().parse(next)?;
                let (rest, _) = Tag(s.as_str()).parse(rest)?;
                next = rest;
            } else {
                // hole
                let (rest, o) = Expr(self.0).parse(next)?;
                vec.push(o);
                next = rest;
            }
        }

        Ok((
            next,
            Tree {
                op: op.clone(),
                input: vec,
            },
        ))
    }
}

struct Inner<'a, G: PrecedenceGraph>(&'a G, G::P, Fixity);
impl<'a, I, G> Parser<I, Tree> for Inner<'a, G>
where
    I: ParserInput + Compare<&'a str>,
    G: PrecedenceGraph,
{
    fn parse(&self, i: I) -> ParserResult<I, Tree, ParseError> {
        Alt(self
            .0
            .ops(self.1, self.2)
            .into_iter()
            .map(|op| Op(self.0, op))
            .collect())
        .parse(i)
    }
}

struct Prec<'a, G: PrecedenceGraph>(&'a G, G::P);
impl<'a, I, G> Parser<I, Tree> for Prec<'a, G>
where
    I: ParserInput + Compare<&'a str>,
    G: PrecedenceGraph,
{
    fn parse(&self, i: I) -> ParserResult<I, Tree, ParseError> {
        Alt::<&dyn Parser<I, Tree>>(vec![
            &Closed(self.0, self.1),
            &InfixNonAssoc(self.0, self.1),
            &PreRight(self.0, self.1),
            &PostLeft(self.0, self.1),
        ])
        .parse(i)
    }
}

struct InfixNonAssoc<'a, G: PrecedenceGraph>(&'a G, G::P);
impl<'a, I, G> Parser<I, Tree> for InfixNonAssoc<'a, G>
where
    I: ParserInput + Compare<&'a str>,
    G: PrecedenceGraph,
{
    fn parse(&self, i: I) -> ParserResult<I, Tree, ParseError> {
        let succ = Precs(self.0, self.0.succ(self.1));
        let (i, left) = succ.parse(i)?;
        let (i, mut expr) = Inner(self.0, self.1, Fixity::Infix(Associativity::None)).parse(i)?;
        let (i, right) = succ.parse(i)?;
        expr.input.insert(0, left);
        expr.input.push(right);
        Ok((i, expr))
    }
}

struct Closed<'a, G: PrecedenceGraph>(&'a G, G::P);
impl<'a, I, G> Parser<I, Tree> for Closed<'a, G>
where
    I: ParserInput + Compare<&'a str>,
    G: PrecedenceGraph,
{
    fn parse(&self, i: I) -> ParserResult<I, Tree, ParseError> {
        Inner(self.0, self.1, Fixity::Closed).parse(i)
    }
}

struct PreRight<'a, G: PrecedenceGraph>(&'a G, G::P);
impl<'a, I, G> Parser<I, Tree> for PreRight<'a, G>
where
    I: ParserInput + Compare<&'a str>,
    G: PrecedenceGraph,
{
    fn parse(&self, i: I) -> ParserResult<I, Tree, ParseError> {
        let succ = Precs(self.0, self.0.succ(self.1));
        let pre = Or(
            Inner(self.0, self.1, Fixity::Prefix),
            (
                &succ,
                Inner(self.0, self.1, Fixity::Infix(Associativity::Right)),
            ),
        );
        let (rest, inners) = Many1(pre).parse(i)?;
        let (rest, succ) = succ.parse(rest)?;
        let mut expr = inners
            .into_iter()
            .map(|e| {
                e.map_right(|(first, mut rest)| {
                    rest.input.insert(0, first);
                    rest
                })
                .into_inner()
            })
            .rev()
            .reduce(|right, mut left| {
                left.input.push(right);
                left
            })
            .unwrap();

        expr.input.push(succ);
        Ok((rest, expr))
    }
}

struct PostLeft<'a, G: PrecedenceGraph>(&'a G, G::P);
impl<'a, I, G> Parser<I, Tree> for PostLeft<'a, G>
where
    I: ParserInput + Compare<&'a str>,
    G: PrecedenceGraph,
{
    fn parse(&self, i: I) -> ParserResult<I, Tree, ParseError> {
        let succ = Precs(self.0, self.0.succ(self.1));
        let post = Or(
            Inner(self.0, self.1, Fixity::Postfix),
            (
                Inner(self.0, self.1, Fixity::Infix(Associativity::Left)),
                &succ,
            ),
        );
        let (rest, succ) = succ.parse(i)?;
        let (rest, inners) = Many1(post).parse(rest)?;
        let mut expr = inners
            .into_iter()
            .map(|e| {
                e.map_right(|(mut rest, last)| {
                    rest.input.push(last);
                    rest
                })
                .into_inner()
            })
            .rev()
            .reduce(|left, mut right| {
                right.input.insert(0, left);
                right
            })
            .unwrap();

        expr.input.insert(0, succ);
        Ok((rest, expr))
    }
}

impl<'a> Compare<&'a str> for &'a str {
    fn compare(&self, other: &'a str) -> bool {
        *self == other
    }
}

pub fn parse<'a, G: PrecedenceGraph>(graph: &'a G, input: &'a str) -> Result<Tree, ParseError> {
    let (rest, expr) = Expr(graph).parse(input)?;
    let (unparsed, _) = SkipSpace().parse(rest)?;
    if unparsed.is_empty() {
        Ok(expr)
    } else {
        Err(ParseError::UnparsedInput)
    }
}

#[cfg(test)]
mod tests {
    use petgraph::dot::Config;
    use petgraph::dot::Dot;

    use super::*;

    fn make_graph() -> MappedPrecedenceGraph {
        let mut graph = MappedPrecedenceGraph::new();
        let parenthesis = Operator::new(Fixity::Closed, "(_)");
        let b = Operator::new(Fixity::Closed, "b");
        let n = Operator::new(Fixity::Closed, "n");
        let add = Operator::new(Fixity::Infix(Associativity::Left), "_+_");
        let sub = Operator::new(Fixity::Infix(Associativity::Left), "_-_");
        let eq = Operator::new(Fixity::Infix(Associativity::Left), "_==_");
        let land = Operator::new(Fixity::Infix(Associativity::Left), "_&&_");
        let fact = Operator::new(Fixity::Postfix, "_!");
        let if_then_else = Operator::new(Fixity::Prefix, "if_then_else_");
        let semicolon = Operator::new(Fixity::Infix(Associativity::Left), "_;_");
        let tuple_2 = Operator::new(Fixity::Closed, "(_,_)");
        let tuple_3 = Operator::new(Fixity::Closed, "(_,_,_)");

        graph.add(&add, PrecedenceRelation::Equal, &sub);
        graph.add(&parenthesis, PrecedenceRelation::Tighter, &add);
        graph.add(&parenthesis, PrecedenceRelation::Tighter, &fact);
        graph.add(&parenthesis, PrecedenceRelation::Tighter, &if_then_else);
        graph.add(&add, PrecedenceRelation::Tighter, &eq);
        graph.add(&eq, PrecedenceRelation::Looser, &fact);
        graph.add(&eq, PrecedenceRelation::Tighter, &land);
        graph.add(&land, PrecedenceRelation::Looser, &parenthesis);
        graph.add(&eq, PrecedenceRelation::Looser, &parenthesis);
        graph.add(&b, PrecedenceRelation::Equal, &parenthesis);
        graph.add(&n, PrecedenceRelation::Equal, &parenthesis);
        graph.add(&semicolon, PrecedenceRelation::Looser, &land);
        graph.add(&semicolon, PrecedenceRelation::Looser, &if_then_else);
        graph.add(&tuple_2, PrecedenceRelation::Looser, &parenthesis);
        graph.add(&tuple_2, PrecedenceRelation::Tighter, &land);
        graph.add(&tuple_3, PrecedenceRelation::Looser, &parenthesis);
        graph.add(&tuple_3, PrecedenceRelation::Tighter, &land);
        graph
    }
    #[test]
    fn test_graph_shape() {
        let graph = make_graph();
        assert!(graph.is_acyclic());
        println!(
            "{:?}",
            Dot::with_config(&graph.graph, &[Config::EdgeNoLabel])
        );
        println!("{:?}", graph.map);
    }

    #[test]
    fn test_graph_trait() {
        let graph = make_graph();
        let (graph, map) = (graph.graph, graph.map);
        println!("{:?}", map);
        for prec in graph.node_indices() {
            println!("{:?} {:?}", prec, graph.succ(prec));
        }
    }

    #[test]
    fn test_combinator() {
        let i = "ab  b b a ab ab";

        println!("{:?}", (Tag("ab"), SkipSpace(), Tag("b")).parse(i).unwrap());
        println!("{:?}", Alt(vec![Tag("ab"), Tag("b")]).parse(i).unwrap());
        println!(
            "{:?}",
            Many1(Alt(vec![
                (SkipSpace(), Tag("ab")),
                (SkipSpace(), Tag("b")),
                (SkipSpace(), Tag("a"))
            ]))
            .parse(i)
            .unwrap()
        );
    }

    #[test]
    fn test_parser() {
        let graph = make_graph();
        let i = r#"if ( b , ( n , n , n ) ) && n + n == n ! then n else ( n + n ) ; n + n ; if b then b else n"#;
        let tree = parse(&graph.graph, i);
        if let Err(ParseError::UnexpectedToken(n)) = tree {
            let n = i.chars().count() - n;
            println!("{:#?}", &i[n..]);
        }
        println!("{:#?}", tree);
    }
}
