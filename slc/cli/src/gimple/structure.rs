//! The structuring of a function's control-flow graph into nested `if`s and
//! `loop`s (readable GIMPLE): one routine over the blocks and their jumps,
//! its decisions a tree (`Node`) -- the readable text rendered from it, and
//! the structured form's correspondence with the CFG proven along it (the
//! cut points: its joins and loop heads).
//!
//! A block: its statements (lines of readable GIMPLE), then a return, a
//! jump, or a branch on a condition; an edge carries the copies a jump
//! makes (the phis of its target). A condition block's statements total
//! (defined whatever they compute) let a branch combine it into an `&&` /
//! `||`.

use std::collections::{BTreeMap, BTreeSet};

/// A function's control-flow graph: its blocks, the first one's index
pub struct Graph {
    pub blocks: Vec<Block>,
    pub entry: usize,
}

pub struct Block {
    /// GCC's number of the block
    pub num: u64,
    /// its statements (a `return` the last when it returns)
    pub stmts: Vec<String>,
    /// its statements all total (a condition block an `&&` may combine)
    pub total: bool,
    pub term: Jump,
}

/// How a block ends
pub enum Jump {
    Return,
    Goto(Edge),
    /// the condition and its negation, the two ways
    If { cond: Cond, yes: Edge, no: Edge },
}

/// A branch's condition: its readable text, and its negation's
#[derive(Clone)]
pub struct Cond {
    pub text: String,
    pub neg: String,
}

#[derive(Clone)]
pub struct Edge {
    pub to: usize,
    /// the copies made on the way (the target's phis)
    pub copies: Vec<String>,
}

/// The structuring's decisions
pub enum Node {
    /// a block's statements written in place
    Stmts(usize, Vec<String>),
    /// lines written as they are (an edge's copies, `break`)
    Lines(Vec<String>),
    /// a branch: the combined condition, the blocks it combines (their
    /// statements first), the two ways (an empty one left out); then the
    /// join (a cut point), if any
    If { cond: String, hoist: Vec<usize>, yes: Vec<Node>, no: Vec<Node> },
    /// a loop: its head (a cut point), its body
    Loop { head: usize, body: Vec<Node> },
    /// the join of the branch before (a cut point): the code goes on there
    Join(usize),
}

/// A combined condition: a block's, or an `&&` / `||` of them
#[derive(Clone)]
enum CT {
    Leaf(usize),
    And(Box<CT>, Box<CT>),
    Or(Box<CT>, Box<CT>),
    Not(Box<CT>),
}

struct Chain {
    tree: CT,
    hoist: Vec<usize>,
    yes: Edge,
    yes_from: usize,
    no: Edge,
    no_from: usize,
}

/// The structuring of g: its tree; an error when the control flow is not
/// structured (or too much would be written twice)
pub fn structure(g: &Graph) -> Result<Vec<Node>, String> {
    let mut s = St::new(g);
    let mut out = Vec::new();
    s.emit(&mut out, g.entry, None, &[])?;
    let total: usize = g.blocks.iter().map(|b| b.stmts.len()).sum();
    if s.emitted > 4 * total + 8 {
        return Err("unstructured control flow (too much duplication)".into());
    }
    Ok(out)
}

/// The tree's readable text, at indentation depth `depth`
pub fn render(g: &Graph, nodes: &[Node], depth: usize, out: &mut Vec<String>) {
    let ind = |d: usize| "  ".repeat(d);
    for n in nodes {
        match n {
            Node::Stmts(_, ls) | Node::Lines(ls) => out.extend(ls.iter().map(|l| format!("{}{}", ind(depth), l))),
            Node::If { cond, hoist, yes, no } => {
                for &h in hoist {
                    out.extend(g.blocks[h].stmts.iter().map(|l| format!("{}{}", ind(depth), l)));
                }
                // (both ways empty: nothing)
                if yes.is_empty() && no.is_empty() {
                    continue;
                }
                out.push(format!("{}if {} {{", ind(depth), cond));
                render(g, yes, depth + 1, out);
                if !no.is_empty() {
                    out.push(format!("{}}} else {{", ind(depth)));
                    render(g, no, depth + 1, out);
                }
                out.push(format!("{}}}", ind(depth)));
            }
            Node::Loop { body, .. } => {
                out.push(format!("{}loop {{", ind(depth)));
                render(g, body, depth + 1, out);
                out.push(format!("{}}}", ind(depth)));
            }
            Node::Join(_) => {}
        }
    }
}

/// The structuring's state: the graph's analyses, the statements written
struct St<'g> {
    g: &'g Graph,
    succ: Vec<Vec<usize>>,
    /// immediate post-dominators
    ipdom: Vec<Option<usize>>,
    /// loops: head -> (its blocks, the exit `break` goes to)
    loops: BTreeMap<usize, (BTreeSet<usize>, Option<usize>)>,
    emitted: usize,
}

fn edges(b: &Block) -> Vec<&Edge> {
    match &b.term {
        Jump::Return => vec![],
        Jump::Goto(e) => vec![e],
        Jump::If { yes, no, .. } => vec![yes, no],
    }
}

impl<'g> St<'g> {
    fn new(g: &'g Graph) -> Self {
        let n = g.blocks.len();
        let succ: Vec<Vec<usize>> = g.blocks.iter().map(|b| edges(b).iter().map(|e| e.to).collect()).collect();
        // back edges (to a block on the DFS stack): loops
        let mut back: BTreeSet<(usize, usize)> = BTreeSet::new();
        fn dfs(i: usize, succ: &[Vec<usize>], st: &mut [u8], back: &mut BTreeSet<(usize, usize)>) {
            st[i] = 1;
            for &s in &succ[i] {
                if st[s] == 1 {
                    back.insert((i, s));
                } else if st[s] == 0 {
                    dfs(s, succ, st, back);
                }
            }
            st[i] = 2;
        }
        dfs(g.entry, &succ, &mut vec![0u8; n], &mut back);
        // the natural loop of each head: the blocks reaching a latch
        // without passing the head
        let mut loops: BTreeMap<usize, (BTreeSet<usize>, Option<usize>)> = BTreeMap::new();
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
        for i in 0..n {
            for &s in &succ[i] {
                preds[s].push(i);
            }
        }
        for &(latch, h) in &back {
            let body = &mut loops.entry(h).or_default().0;
            body.insert(h);
            let mut work = vec![latch];
            while let Some(x) = work.pop() {
                if body.insert(x) {
                    work.extend(preds[x].iter().copied());
                }
            }
        }
        // the exit `break` goes to: the most frequent target outside
        for (_, (body, exit)) in loops.iter_mut() {
            let mut count: BTreeMap<usize, usize> = BTreeMap::new();
            for &b in body.iter() {
                for &s in &succ[b] {
                    if !body.contains(&s) {
                        *count.entry(s).or_default() += 1;
                    }
                }
            }
            *exit = count.iter().max_by_key(|(_, &c)| c).map(|(&s, _)| s);
        }
        // post-dominators, on the whole graph, by iteration to the fixpoint
        let all: BTreeSet<usize> = (0..n).collect();
        let mut pdom: Vec<BTreeSet<usize>> = (0..n).map(|i| if succ[i].is_empty() { BTreeSet::from([i]) } else { all.clone() }).collect();
        loop {
            let mut changed = false;
            for i in (0..n).rev() {
                if succ[i].is_empty() {
                    continue;
                }
                let mut s = succ[i].iter().map(|&j| pdom[j].clone()).reduce(|a, b| a.intersection(&b).copied().collect()).unwrap_or_default();
                s.insert(i);
                if s != pdom[i] {
                    pdom[i] = s;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let ipdom: Vec<Option<usize>> = (0..n)
            .map(|i| {
                let rest: BTreeSet<usize> = pdom[i].iter().copied().filter(|&j| j != i).collect();
                rest.iter().copied().find(|&j| pdom[j] == rest)
            })
            .collect();
        St { g, succ, ipdom, loops, emitted: 0 }
    }

    fn returns(&self, b: usize) -> bool {
        matches!(self.g.blocks[b].term, Jump::Return)
    }

    /// Blocks from `b` until `stop`, inside the loops `ctx` (their heads,
    /// innermost last).
    fn emit(&mut self, out: &mut Vec<Node>, mut b: usize, stop: Option<usize>, ctx: &[usize]) -> Result<(), String> {
        loop {
            if Some(b) == stop {
                out.push(Node::Join(b));
                return Ok(());
            }
            if self.emitted > 20 * self.g.blocks.iter().map(|b| b.stmts.len()).sum::<usize>() + 100 {
                return Err("unstructured control flow".into());
            }
            // entering a loop
            if self.loops.contains_key(&b) && ctx.last() != Some(&b) {
                let exit = self.loops[&b].1;
                let inner: Vec<usize> = ctx.iter().copied().chain([b]).collect();
                let mut body = Vec::new();
                self.emit(&mut body, b, None, &inner)?;
                out.push(Node::Loop { head: b, body });
                match exit {
                    Some(x) => {
                        b = x;
                        continue;
                    }
                    None => return Ok(()),
                }
            }
            let blk = &self.g.blocks[b];
            self.emitted += blk.stmts.len();
            out.push(Node::Stmts(b, blk.stmts.clone()));
            match &blk.term {
                Jump::Return => return Ok(()),
                Jump::If { .. } => {
                    // (a short-circuit condition: the condition blocks of an
                    // `&&` / `||` it combines, their statements first)
                    let ch = self.chain(b);
                    self.emitted += ch.hoist.iter().map(|&h| self.g.blocks[h].stmts.len()).sum::<usize>();
                    let (yes, no) = (ch.yes.to, ch.no.to);
                    // the join, if in the current loop (else each way ends
                    // by itself: the next iteration, `break`, or `return`)
                    let mut join = self.ipdom[b].filter(|j| ctx.last().is_none_or(|h| self.loops[h].0.contains(j)));
                    // an early return: when the ways only meet at a return,
                    // but one way leads to the other or returns, the other
                    // is the join (the return is written in place)
                    let in_loop = |s: &Self, j: usize| ctx.last().is_none_or(|h| j != *h && s.loops[h].0.contains(&j));
                    if join.is_none_or(|j| self.returns(j)) {
                        if in_loop(self, no) && self.early(yes, no) {
                            join = Some(no);
                        } else if in_loop(self, yes) && self.early(no, yes) {
                            join = Some(yes);
                        }
                    }
                    let cond = self.render_cond(&ch.tree, false);
                    let ncond = self.render_cond(&ch.tree, true);
                    let yes_nodes = self.arm(&ch.yes, join, ctx)?;
                    let no_nodes = self.arm(&ch.no, join, ctx)?;
                    // (an empty way -- no lines -- left out: the other under
                    // the condition that takes it)
                    let empty = |ns: &Vec<Node>| {
                        let mut ls = Vec::new();
                        render(self.g, ns, 0, &mut ls);
                        ls.is_empty()
                    };
                    match (empty(&yes_nodes), empty(&no_nodes)) {
                        (true, true) => out.push(Node::If { cond, hoist: ch.hoist, yes: Vec::new(), no: Vec::new() }),
                        (true, false) => out.push(Node::If { cond: ncond, hoist: ch.hoist, yes: no_nodes, no: Vec::new() }),
                        (false, true) => out.push(Node::If { cond, hoist: ch.hoist, yes: yes_nodes, no: Vec::new() }),
                        (false, false) => out.push(Node::If { cond, hoist: ch.hoist, yes: yes_nodes, no: no_nodes }),
                    }
                    match join {
                        Some(j) => b = j,
                        None => return Ok(()),
                    }
                }
                Jump::Goto(e) => {
                    let e = e.clone();
                    match self.edge(out, &e, ctx)? {
                        Some(s) => b = s,
                        None => return Ok(()),
                    }
                }
            }
        }
    }

    /// The branch at b with the condition blocks it combines: an `&&` (its
    /// yes way a condition block whose other way is b's no way) or an `||`
    /// (its no way one whose other way is b's yes way), recursively -- each
    /// combined block b's alone (its only predecessor), no loop head, its
    /// statements total, the shared way's copies the same from both blocks.
    fn chain(&self, b: usize) -> Chain {
        let Jump::If { yes, no, .. } = &self.g.blocks[b].term else { unreachable!("a branch") };
        let mut ch = Chain { tree: CT::Leaf(b), hoist: Vec::new(), yes: yes.clone(), yes_from: b, no: no.clone(), no_from: b };
        loop {
            // (an `&&`: the yes way's block)
            let c = ch.yes.to;
            if ch.yes.copies.is_empty() && self.combinable(c, ch.yes_from) {
                let sub = self.chain(c);
                if sub.no.to == ch.no.to && sub.no.copies == ch.no.copies {
                    ch.tree = CT::And(Box::new(ch.tree), Box::new(sub.tree));
                    ch.hoist.push(c);
                    ch.hoist.extend(sub.hoist);
                    (ch.yes, ch.yes_from) = (sub.yes, sub.yes_from);
                    continue;
                }
                if sub.yes.to == ch.no.to && sub.yes.copies == ch.no.copies {
                    ch.tree = CT::And(Box::new(ch.tree), Box::new(CT::Not(Box::new(sub.tree))));
                    ch.hoist.push(c);
                    ch.hoist.extend(sub.hoist);
                    (ch.yes, ch.yes_from) = (sub.no, sub.no_from);
                    continue;
                }
            }
            // (an `||`: the no way's block)
            let c = ch.no.to;
            if ch.no.copies.is_empty() && self.combinable(c, ch.no_from) {
                let sub = self.chain(c);
                if sub.yes.to == ch.yes.to && sub.yes.copies == ch.yes.copies {
                    ch.tree = CT::Or(Box::new(ch.tree), Box::new(sub.tree));
                    ch.hoist.push(c);
                    ch.hoist.extend(sub.hoist);
                    (ch.no, ch.no_from) = (sub.no, sub.no_from);
                    continue;
                }
                if sub.no.to == ch.yes.to && sub.no.copies == ch.yes.copies {
                    ch.tree = CT::Or(Box::new(ch.tree), Box::new(CT::Not(Box::new(sub.tree))));
                    ch.hoist.push(c);
                    ch.hoist.extend(sub.hoist);
                    (ch.no, ch.no_from) = (sub.yes, sub.yes_from);
                    continue;
                }
            }
            return ch;
        }
    }

    /// c a condition block a branch at `from` may combine: from's alone, no
    /// loop head, its statements total
    fn combinable(&self, c: usize, from: usize) -> bool {
        let preds = (0..self.succ.len()).filter(|&i| self.succ[i].contains(&c)).count();
        let blk = &self.g.blocks[c];
        preds == 1 && self.succ[from].contains(&c) && !self.loops.contains_key(&c) && matches!(blk.term, Jump::If { .. }) && blk.total
    }

    /// a combined condition as text (`!` pushed to the comparisons)
    fn render_cond(&self, t: &CT, neg: bool) -> String {
        match t {
            CT::Leaf(b) => {
                let Jump::If { cond, .. } = &self.g.blocks[*b].term else { unreachable!("a condition block") };
                if neg { cond.neg.clone() } else { cond.text.clone() }
            }
            CT::Not(x) => self.render_cond(x, !neg),
            CT::And(x, y) | CT::Or(x, y) => {
                let and = matches!(t, CT::And(..)) != neg;
                format!("({}) {} ({})", self.render_cond(x, neg), if and { "&&" } else { "||" }, self.render_cond(y, neg))
            }
        }
    }

    /// Every path from `from` reaches `to` or ends in a `return` (without
    /// going round a loop).
    fn early(&self, from: usize, to: usize) -> bool {
        if from == to {
            return false;
        }
        let mut seen = BTreeSet::new();
        let mut work = vec![from];
        while let Some(b) = work.pop() {
            if b == to || !seen.insert(b) {
                continue;
            }
            if self.loops.contains_key(&b) {
                return false;
            }
            let s = &self.succ[b];
            if s.is_empty() && !self.returns(b) {
                return false;
            }
            work.extend(s.iter().copied());
        }
        true
    }

    /// The edge e: its copies, then (in a loop) the next iteration, `break`,
    /// or an exit written in place; otherwise its target is where the code
    /// goes on.
    fn edge(&mut self, out: &mut Vec<Node>, e: &Edge, ctx: &[usize]) -> Result<Option<usize>, String> {
        out.push(Node::Lines(e.copies.clone()));
        let Some(&h) = ctx.last() else { return Ok(Some(e.to)) };
        if e.to == h {
            return Ok(None);
        }
        let (body, exit) = &self.loops[&h];
        if body.contains(&e.to) {
            return Ok(Some(e.to));
        }
        if Some(e.to) == *exit {
            out.push(Node::Lines(vec!["break".into()]));
            return Ok(None);
        }
        // another exit (a `return` from inside the loop): in place
        self.emit(out, e.to, None, &ctx[..ctx.len() - 1])?;
        Ok(None)
    }

    /// One way of a branch.
    fn arm(&mut self, e: &Edge, join: Option<usize>, ctx: &[usize]) -> Result<Vec<Node>, String> {
        let mut out = Vec::new();
        if let Some(to) = self.edge(&mut out, e, ctx)? {
            self.emit(&mut out, to, join, ctx)?;
        }
        Ok(out)
    }
}
