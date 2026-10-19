//! Abstract-semantics flow theory: the first genuinely selection-dependent
//! check in the pipeline.
//!
//! A Datalog rule cannot express this. Rules see the superposition of every
//! candidate at once; this analysis evaluates one SELECTED subset and asks
//! whether the values actually flowing through a basic block agree with the
//! types those selected statements claim, and with the machine facts anchoring
//! them. The question only has meaning once a selection exists.
//!
//! The domain is deliberately tiny: a class set over {Int, Float, Ptr} and a
//! width. There is no join and no fixpoint -- each basic block starts at Top
//! and is folded in execution order. That keeps the evaluator cheap enough to
//! run inside a solver callback and, more importantly, keeps it honest: an
//! intra-block chain of concrete facts is something we can explain to Z3 as a
//! clause over the selection literals that produced it.
//!
//! Int and Ptr deliberately do NOT contradict each other. This pipeline emits
//! pointers held in longs and integers cast to pointers as a matter of course,
//! so making that a contradiction would drown the real signal. Float against
//! non-Float, and unequal known widths, are the axes that carry it.

use std::collections::{BTreeMap, BTreeSet};

use crate::x86::types::{
    ClightExpr, ClightFloatSize, ClightIntSize, ClightStmt, ClightType, Ident, MemoryChunk, Node,
    RTLReg, XType,
};

pub const CLASS_INT: u8 = 1;
pub const CLASS_FLOAT: u8 = 2;
pub const CLASS_PTR: u8 = 4;
pub const CLASS_TOP: u8 = CLASS_INT | CLASS_FLOAT | CLASS_PTR;

/// Width in bytes, or Top when the value's width is not committed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AWidth {
    W1,
    W2,
    W4,
    W8,
    W16,
    Top,
}

/// One abstract value: which classes it may belong to, and how wide it is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AVal {
    pub classes: u8,
    pub width: AWidth,
}

impl AVal {
    pub const fn top() -> AVal {
        AVal {
            classes: CLASS_TOP,
            width: AWidth::Top,
        }
    }

    pub const fn new(classes: u8, width: AWidth) -> AVal {
        AVal { classes, width }
    }

    pub fn is_top(&self) -> bool {
        self.classes == CLASS_TOP && self.width == AWidth::Top
    }

    /// Greatest lower bound, or None when the two cannot describe one value.
    /// Disjoint class sets and two different committed widths are the only two
    /// ways to contradict.
    pub fn meet(self, other: AVal) -> Option<AVal> {
        let classes = self.classes & other.classes;
        if classes == 0 {
            return None;
        }
        let width = match (self.width, other.width) {
            (AWidth::Top, w) | (w, AWidth::Top) => w,
            (a, b) if a == b => a,
            _ => return None,
        };
        Some(AVal { classes, width })
    }

    /// True when the two could describe the same value.
    pub fn compatible(self, other: AVal) -> bool {
        self.meet(other).is_some()
    }
}

fn int_width(size: ClightIntSize) -> AWidth {
    match size {
        ClightIntSize::I8 | ClightIntSize::IBool => AWidth::W1,
        ClightIntSize::I16 => AWidth::W2,
        ClightIntSize::I32 => AWidth::W4,
    }
}

/// The claim a selected candidate makes by spelling a value with this type.
/// Aggregates (struct, union, function) and void claim nothing.
pub fn claim_of_type(ty: &ClightType, ptr64: bool) -> AVal {
    let ptr_width = if ptr64 { AWidth::W8 } else { AWidth::W4 };
    match ty {
        ClightType::Tint(size, _, _) => AVal::new(CLASS_INT, int_width(*size)),
        ClightType::Tlong(_, _) => AVal::new(CLASS_INT | CLASS_PTR, AWidth::W8),
        ClightType::Tint128(_, _) => AVal::new(CLASS_INT, AWidth::W16),
        ClightType::Tfloat(ClightFloatSize::F32, _) => AVal::new(CLASS_FLOAT, AWidth::W4),
        ClightType::Tfloat(ClightFloatSize::F64, _) => AVal::new(CLASS_FLOAT, AWidth::W8),
        ClightType::Tpointer(_, _) | ClightType::Tarray(_, _, _) => {
            AVal::new(CLASS_PTR | CLASS_INT, ptr_width)
        }
        ClightType::Tvoid
        | ClightType::Tfunction(_, _, _)
        | ClightType::Tstruct(_, _)
        | ClightType::Tunion(_, _) => AVal::top(),
    }
}

/// Anchor carried by a memory chunk. Width is ALWAYS an anchor: it is what the
/// instruction encoding says it moves. Class is an anchor only where the chunk
/// cannot be a bit-copy of something else -- an MInt64 or MAny move legitimately
/// carries a double or a pointer, so those commit width only.
pub fn anchor_of_chunk(chunk: MemoryChunk) -> AVal {
    match chunk {
        MemoryChunk::MFloat32 => AVal::new(CLASS_FLOAT, AWidth::W4),
        MemoryChunk::MFloat64 => AVal::new(CLASS_FLOAT, AWidth::W8),
        MemoryChunk::MBool | MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned => {
            AVal::new(CLASS_INT, AWidth::W1)
        }
        MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned => AVal::new(CLASS_INT, AWidth::W2),
        MemoryChunk::MInt32 => AVal::new(CLASS_INT, AWidth::W4),
        MemoryChunk::MInt64 => AVal::new(CLASS_TOP, AWidth::W8),
        MemoryChunk::MAny32 => AVal::new(CLASS_TOP, AWidth::W4),
        MemoryChunk::MAny64 => AVal::new(CLASS_TOP, AWidth::W8),
        MemoryChunk::Unknown => AVal::top(),
    }
}

/// Anchor carried by an ABI slot in a known external signature.
pub fn anchor_of_xtype(xt: &XType, ptr64: bool) -> AVal {
    let ptr_width = if ptr64 { AWidth::W8 } else { AWidth::W4 };
    match xt {
        XType::Xfloat => AVal::new(CLASS_FLOAT, AWidth::W8),
        XType::Xsingle => AVal::new(CLASS_FLOAT, AWidth::W4),
        XType::Xbool | XType::Xint8signed | XType::Xint8unsigned => {
            AVal::new(CLASS_INT, AWidth::W1)
        }
        XType::Xint16signed | XType::Xint16unsigned => AVal::new(CLASS_INT, AWidth::W2),
        XType::Xint | XType::Xintunsigned => AVal::new(CLASS_INT, AWidth::W4),
        XType::Xlong | XType::Xlongunsigned => AVal::new(CLASS_INT | CLASS_PTR, AWidth::W8),
        XType::Xptr
        | XType::Xcharptr
        | XType::Xcharptrptr
        | XType::Xintptr
        | XType::Xfloatptr
        | XType::Xsingleptr
        | XType::Xfuncptr
        | XType::XstructPtr(_) => AVal::new(CLASS_PTR | CLASS_INT, ptr_width),
        // The two generic widths commit a width and nothing else, exactly like
        // their MAny chunk counterparts.
        XType::Xany32 => AVal::new(CLASS_TOP, AWidth::W4),
        XType::Xany64 => AVal::new(CLASS_TOP, AWidth::W8),
        XType::Xvoid => AVal::top(),
    }
}

/// A location the evaluator tracks. Temps are RTL registers; addressable
/// variables (stack locals and globals alike) are Clight `Evar` idents; a slot
/// is a constant displacement off a tracked register, which is how a field or
/// a spilled local appears after lifting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LocKey {
    Reg(RTLReg),
    Var(Ident),
    Slot(RTLReg, i64),
}

impl LocKey {
    /// True for the locations aliasing can reach behind our back.
    fn is_memory(&self) -> bool {
        matches!(self, LocKey::Var(_) | LocKey::Slot(_, _))
    }
}

/// A flowing value together with the selection literals responsible for it.
/// The provenance is never truncated: an explaining clause built from a partial
/// chain would exclude models that are not in fact contradictory.
#[derive(Debug, Clone)]
struct Flowing {
    val: AVal,
    /// True when the width came from a MACHINE anchor rather than from a
    /// statement's own spelling.
    ///
    /// This distinction is the difference between signal and noise. A memory
    /// chunk's width is architectural, so disagreeing with it means the
    /// recovered code moves the wrong number of bytes. Two statements spelling
    /// the same register `int` and then `long` disagree about nothing: a
    /// narrowing read is ordinary C, and treating it as a contradiction buried
    /// the real reports under a thousand of them.
    width_anchored: bool,
    /// Where this value came from. A contradiction is reported under the origin
    /// of the value it contradicts, not the site of the claim: what makes a
    /// disagreement evidence is that one side is a machine fact.
    origin: AnchorKind,
    /// The program-level global commitment responsible for this value, when
    /// `origin` is `GlobalType`.  Keep the identity while values flow through
    /// temporaries so a disagreement can be priced against the right Stage-B
    /// variable rather than merely counted by kind.
    global_origin: Option<Ident>,
    /// Nodes whose SELECTED candidate contributed. Only multi-candidate nodes
    /// carry a literal, so this stays short in practice.
    from: BTreeSet<Node>,
}

impl Flowing {
    fn top() -> Flowing {
        Flowing {
            val: AVal::top(),
            width_anchored: false,
            origin: AnchorKind::StatementOnly,
            global_origin: None,
            from: BTreeSet::new(),
        }
    }

    fn claim(val: AVal) -> Flowing {
        Flowing {
            val,
            width_anchored: false,
            origin: AnchorKind::StatementOnly,
            global_origin: None,
            from: BTreeSet::new(),
        }
    }
}

/// Where the opposing value came from, which decides how a contradiction is
/// reported and counted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AnchorKind {
    /// A load or store memory chunk.
    Chunk,
    /// An argument or return slot of a known external signature.
    ExternSignature,
    /// A committed global variable type.
    GlobalType,
    /// No machine anchor: two selected statements disagree with each other.
    StatementOnly,
}

/// One flow contradiction, with the chain that produced it.
#[derive(Debug, Clone)]
pub struct Contradiction {
    pub node: Node,
    pub loc: LocKey,
    pub claimed: AVal,
    pub flowing: AVal,
    pub kind: AnchorKind,
    /// The exact committed global whose value reached this contradiction.
    /// This remains `None` for architectural and statement-only origins.
    pub global_symbol: Option<Ident>,
    /// Every node whose selected candidate the contradiction depends on,
    /// including `node`. The explaining clause is the negation of their
    /// conjunction.
    pub chain: BTreeSet<Node>,
}

#[derive(Debug, Default, Clone, Copy)]
pub struct FlowStats {
    pub blocks_checked: usize,
    /// Blocks some machine anchor actually reaches. Only these can be
    /// certified: a block with no anchor has nothing to be consistent with.
    pub blocks_anchored: usize,
    pub blocks_certified: usize,
    pub contradictions: usize,
    pub by_chunk: usize,
    pub by_extern_signature: usize,
    pub by_global_type: usize,
    pub by_statement_only: usize,
    /// Contradictions whose chain has no selectable alternative: nothing to
    /// select, so an upstream gap rather than a selection error.
    pub gaps: usize,
    /// Explaining clauses handed to the solver.
    pub clauses_injected: usize,
    /// Final-check rounds the theory saw.
    pub final_rounds: usize,
    /// Functions that hit the per-function final-round cap.
    pub caps_hit: usize,
    /// Selections where a flow clause named the node and the final pick is not
    /// candidate 0, i.e. the weight-1 prior lost to flow evidence.
    pub ties_determined_by_flow: usize,
    /// Propagator retries made after an injected flow clause made the ground
    /// formula UNSAT.
    pub unsat_retries: usize,
    /// Exact contradiction sites exempted by maximal certification retries.
    pub exempted_nodes: usize,
    /// Contradictions skipped because their exact site was exempted.
    pub exemptions_skipped: usize,
}

impl FlowStats {
    pub fn merge(&mut self, o: &FlowStats) {
        self.blocks_checked += o.blocks_checked;
        self.blocks_anchored += o.blocks_anchored;
        self.blocks_certified += o.blocks_certified;
        self.contradictions += o.contradictions;
        self.by_chunk += o.by_chunk;
        self.by_extern_signature += o.by_extern_signature;
        self.by_global_type += o.by_global_type;
        self.by_statement_only += o.by_statement_only;
        self.gaps += o.gaps;
        self.clauses_injected += o.clauses_injected;
        self.final_rounds += o.final_rounds;
        self.caps_hit += o.caps_hit;
        self.ties_determined_by_flow += o.ties_determined_by_flow;
        self.unsat_retries += o.unsat_retries;
        self.exempted_nodes += o.exempted_nodes;
        self.exemptions_skipped += o.exemptions_skipped;
    }

    pub fn count_kind(&mut self, kind: AnchorKind) {
        match kind {
            AnchorKind::Chunk => self.by_chunk += 1,
            AnchorKind::ExternSignature => self.by_extern_signature += 1,
            AnchorKind::GlobalType => self.by_global_type += 1,
            AnchorKind::StatementOnly => self.by_statement_only += 1,
        }
    }
}

/// Machine facts the evaluator checks against, all keyed by the node they
/// belong to, plus the program-level global types.
#[derive(Debug, Clone, Default)]
pub struct FlowAnchors {
    /// Load/store chunk at a node: the value register it commits, and to what.
    pub chunk: BTreeMap<Node, (RTLReg, AVal)>,
    /// Known external signature at a call node: (argument anchors, return anchor).
    pub call: BTreeMap<Node, (Vec<AVal>, AVal)>,
    /// Committed global variable types, by Clight ident.
    pub global: BTreeMap<Ident, AVal>,
}

impl FlowAnchors {
    pub fn is_empty(&self) -> bool {
        self.chunk.is_empty() && self.call.is_empty() && self.global.is_empty()
    }
}

/// A straight-line run of nodes, evaluated from a Top entry state.
pub type Block = Vec<Node>;

/// Partition a function's nodes into maximal straight-line runs. A node starts
/// a block unless it has exactly one predecessor which has exactly one
/// successor; the run then follows the unique successor edge, which IS the
/// execution order and so is what the fold needs.
pub fn basic_blocks(nodes: &[Node], successors: &BTreeMap<Node, Vec<Node>>) -> Vec<Block> {
    // One predecessor pass, so partitioning stays linear in the CFG rather than
    // rescanning the successor map per node.
    let mut preds: BTreeMap<Node, Vec<Node>> = BTreeMap::new();
    for n in nodes {
        preds.entry(*n).or_default();
    }
    for (p, succs) in successors.iter() {
        for s in succs {
            if let Some(v) = preds.get_mut(s) {
                v.push(*p);
            }
        }
    }
    for v in preds.values_mut() {
        v.sort_unstable();
        v.dedup();
    }
    let succ_count = |n: &Node| successors.get(n).map(|v| v.len()).unwrap_or(0);
    let starts_block = |n: &Node| -> bool {
        match preds.get(n) {
            Some(p) if p.len() == 1 => succ_count(&p[0]) != 1,
            _ => true,
        }
    };

    let mut seen: BTreeSet<Node> = BTreeSet::new();
    let mut blocks = Vec::new();
    let mut ordered: Vec<Node> = nodes.to_vec();
    ordered.sort_unstable();
    for n in &ordered {
        if seen.contains(n) || !starts_block(n) {
            continue;
        }
        let mut block = Vec::new();
        let mut cur = *n;
        loop {
            if !seen.insert(cur) {
                break;
            }
            block.push(cur);
            let succs = match successors.get(&cur) {
                Some(s) if s.len() == 1 => s,
                _ => break,
            };
            let next = succs[0];
            let single_entry = preds.get(&next).map(|p| p.len() == 1).unwrap_or(false);
            if !single_entry || seen.contains(&next) {
                break;
            }
            cur = next;
        }
        if !block.is_empty() {
            blocks.push(block);
        }
    }
    // Anything unreached by the walk (a node in a cycle of single-entry
    // single-exit edges) still deserves a block of its own.
    for n in &ordered {
        if !seen.contains(n) {
            seen.insert(*n);
            blocks.push(vec![*n]);
        }
    }
    blocks
}

/// The callee symbol a call statement names, when every candidate at the node
/// agrees on it. Candidates differ in how arguments are spelled, not in who is
/// called, so a disagreement means this is not a plain direct call and no
/// signature anchor applies.
pub fn agreed_callee(candidates: &[ClightStmt]) -> Option<String> {
    let mut agreed: Option<String> = None;
    for cand in candidates {
        let name = callee_symbol(cand)?;
        match &agreed {
            Some(prev) if *prev != name => return None,
            _ => agreed = Some(name),
        }
    }
    agreed
}

fn callee_symbol(stmt: &ClightStmt) -> Option<String> {
    match stmt {
        ClightStmt::Scall(_, callee, _) => match callee {
            ClightExpr::EvarSymbol(name, _) => Some(name.clone()),
            ClightExpr::Ecast(inner, _) => match inner.as_ref() {
                ClightExpr::EvarSymbol(name, _) => Some(name.clone()),
                _ => None,
            },
            _ => None,
        },
        ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner) => callee_symbol(inner),
        ClightStmt::Ssequence(items) => items.iter().find_map(callee_symbol),
        _ => None,
    }
}

/// The evaluator state for one block.
struct Eval<'a> {
    anchors: &'a FlowAnchors,
    ptr64: bool,
    state: BTreeMap<LocKey, Flowing>,
    contradictions: Vec<Contradiction>,
    /// Nodes with more than one candidate, whose selection carries a literal.
    selectable: &'a BTreeSet<Node>,
    /// Every node's candidate list, needed to know what a node's REJECTED
    /// candidates could have done.
    candidates: &'a BTreeMap<Node, Vec<ClightStmt>>,
}

impl<'a> Eval<'a> {
    fn get(&self, loc: LocKey) -> Flowing {
        self.state.get(&loc).cloned().unwrap_or_else(Flowing::top)
    }

    fn set(&mut self, loc: LocKey, val: AVal, from: BTreeSet<Node>) {
        self.state.insert(
            loc,
            Flowing {
                val,
                width_anchored: false,
                origin: AnchorKind::StatementOnly,
                global_origin: None,
                from,
            },
        );
    }

    fn set_flowing(&mut self, loc: LocKey, f: Flowing) {
        self.state.insert(loc, f);
    }

    fn set_anchored(&mut self, loc: LocKey, val: AVal, origin: AnchorKind, from: BTreeSet<Node>) {
        self.state.insert(
            loc,
            Flowing {
                val,
                width_anchored: true,
                origin,
                global_origin: None,
                from,
            },
        );
    }

    /// Aliasing honesty: a call or a store we cannot resolve invalidates every
    /// memory location we were tracking. Registers survive.
    fn kill_memory(&mut self) {
        self.state.retain(|k, _| !k.is_memory());
    }

    /// A value survives past a node not only because the nodes that wrote it
    /// were selected, but because THIS node's selection did not overwrite it.
    /// A rejected candidate that would have written the location is therefore
    /// part of the explanation: a clause omitting this node would forbid models
    /// where the alternative runs and no contradiction arises at all, which is
    /// how an explaining clause turns into a lost answer.
    fn note_preserving(&mut self, node: Node, chosen: &ClightStmt) {
        if !self.selectable.contains(&node) {
            return;
        }
        let Some(cands) = self.candidates.get(&node) else {
            return;
        };
        let mut alt_defs: BTreeSet<LocKey> = BTreeSet::new();
        let mut alt_kills_memory = false;
        for cand in cands {
            if cand == chosen {
                continue;
            }
            let mut defs = Vec::new();
            self.collect_defs(cand, &mut defs, &mut alt_kills_memory);
            alt_defs.extend(defs);
        }
        if alt_defs.is_empty() && !alt_kills_memory {
            return;
        }
        let touched: Vec<LocKey> = self
            .state
            .keys()
            .copied()
            .filter(|loc| alt_defs.contains(loc) || (alt_kills_memory && loc.is_memory()))
            .collect();
        for loc in touched {
            if let Some(f) = self.state.get_mut(&loc) {
                f.from.insert(node);
            }
        }
    }

    /// An undecided node still runs. Forget every location any of its
    /// candidates could write, so nothing older flows past it as if the node
    /// were absent.
    fn forget_possible_defs(&mut self, candidates: &[ClightStmt]) {
        let mut kills_memory = false;
        for cand in candidates {
            let mut defs = Vec::new();
            self.collect_defs(cand, &mut defs, &mut kills_memory);
            for loc in defs {
                self.state.remove(&loc);
            }
        }
        if kills_memory {
            self.kill_memory();
        }
    }

    fn collect_defs(&self, s: &ClightStmt, out: &mut Vec<LocKey>, kills_memory: &mut bool) {
        match s {
            ClightStmt::Sset(t, _) => out.push(LocKey::Reg(*t as RTLReg)),
            ClightStmt::Sassign(lhs, _) => match self.loc_of(lhs) {
                Some(loc) => out.push(loc),
                None => *kills_memory = true,
            },
            ClightStmt::Scall(dst, _, _) | ClightStmt::Sbuiltin(dst, _, _, _) => {
                *kills_memory = true;
                if let Some(d) = dst {
                    out.push(LocKey::Reg(*d as RTLReg));
                }
            }
            ClightStmt::Slabel(_, i) | ClightStmt::Seffect(_, i) => self.collect_defs(i, out, kills_memory),
            ClightStmt::Ssequence(items) => {
                for i in items {
                    self.collect_defs(i, out, kills_memory);
                }
            }
            ClightStmt::Sifthenelse(_, a, b) | ClightStmt::Sloop(a, b) => {
                self.collect_defs(a, out, kills_memory);
                self.collect_defs(b, out, kills_memory);
            }
            ClightStmt::Sswitch(_, cases) => {
                for (_, c) in cases {
                    self.collect_defs(c, out, kills_memory);
                }
            }
            _ => {}
        }
    }

    fn record(
        &mut self,
        node: Node,
        loc: LocKey,
        claimed: AVal,
        flowing: &Flowing,
        kind: AnchorKind,
    ) {
        let mut chain = flowing.from.clone();
        if self.selectable.contains(&node) {
            chain.insert(node);
        }
        self.contradictions.push(Contradiction {
            node,
            loc,
            claimed,
            flowing: flowing.val,
            kind,
            global_symbol: if kind == AnchorKind::GlobalType {
                flowing.global_origin.or(match loc {
                    LocKey::Var(id) if self.anchors.global.contains_key(&id) => Some(id),
                    _ => None,
                })
            } else {
                None
            },
            chain,
        });
    }

    /// Check one leaf reference's claim against what is flowing there, and
    /// return the value the expression yields together with its provenance.
    fn leaf(&mut self, node: Node, loc: LocKey, ty: &ClightType, fallback: AnchorKind) -> Flowing {
        let claimed = claim_of_type(ty, self.ptr64);
        let mut flowing = self.get(loc);
        // A committed global type is an anchor on the variable itself, so meet
        // it in before comparing rather than only naming it in the report.
        if let LocKey::Var(id) = loc {
            if let Some(&g) = self.anchors.global.get(&id) {
                if let Some(v) = g.meet(flowing.val) {
                    flowing = Flowing {
                        val: v,
                        width_anchored: true,
                        origin: AnchorKind::GlobalType,
                        global_origin: Some(id),
                        from: flowing.from,
                    };
                }
            }
        }
        let classes = claimed.classes & flowing.val.classes;
        let width_conflict = flowing.width_anchored
            && claimed.width != AWidth::Top
            && flowing.val.width != AWidth::Top
            && claimed.width != flowing.val.width;
        if classes == 0 || width_conflict {
            // Report under the ORIGIN of the value being contradicted: what
            // makes the disagreement evidence is that one side is a machine
            // fact, not where the claim happens to sit.
            let kind = if flowing.origin == AnchorKind::StatementOnly {
                fallback
            } else {
                flowing.origin
            };
            self.record(node, loc, claimed, &flowing, kind);
            // Continue with the claim so one contradiction does not cascade
            // into a second report for the same value.
            return Flowing::claim(claimed);
        }
        let mut from = flowing.from.clone();
        if self.selectable.contains(&node) {
            from.insert(node);
        }
        // The anchored width survives a narrowing read; an unanchored one is
        // simply replaced by whatever this statement says.
        let width = if flowing.width_anchored {
            flowing.val.width
        } else if claimed.width != AWidth::Top {
            claimed.width
        } else {
            flowing.val.width
        };
        Flowing {
            origin: flowing.origin,
            global_origin: flowing.global_origin,
            val: AVal::new(classes, width),
            width_anchored: flowing.width_anchored,
            from,
        }
    }

    /// The location an expression designates, when the evaluator tracks it.
    fn loc_of(&self, e: &ClightExpr) -> Option<LocKey> {
        match e {
            ClightExpr::Etempvar(id, _) => Some(LocKey::Reg(*id as RTLReg)),
            ClightExpr::Evar(id, _) => Some(LocKey::Var(*id)),
            ClightExpr::Ederef(inner, _) => match inner.as_ref() {
                ClightExpr::Etempvar(id, _) => Some(LocKey::Slot(*id as RTLReg, 0)),
                ClightExpr::Ebinop(crate::x86::types::ClightBinaryOp::Oadd, base, off, _) => {
                    match (base.as_ref(), off.as_ref()) {
                        (ClightExpr::Etempvar(id, _), ClightExpr::EconstInt(k, _)) => {
                            Some(LocKey::Slot(*id as RTLReg, *k as i64))
                        }
                        (ClightExpr::Etempvar(id, _), ClightExpr::EconstLong(k, _)) => {
                            Some(LocKey::Slot(*id as RTLReg, *k))
                        }
                        _ => None,
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn eval(&mut self, node: Node, e: &ClightExpr) -> Flowing {
        match e {
            ClightExpr::Etempvar(id, ty) => self.leaf(
                node,
                LocKey::Reg(*id as RTLReg),
                ty,
                AnchorKind::StatementOnly,
            ),
            ClightExpr::Evar(id, ty) => {
                let kind = if self.anchors.global.contains_key(id) {
                    AnchorKind::GlobalType
                } else {
                    AnchorKind::StatementOnly
                };
                self.leaf(node, LocKey::Var(*id), ty, kind)
            }
            ClightExpr::EconstInt(_, _) => Flowing {
                origin: AnchorKind::StatementOnly,
                global_origin: None,
                width_anchored: false,
                val: AVal::new(CLASS_INT, AWidth::W4),
                from: BTreeSet::new(),
            },
            ClightExpr::EconstLong(_, _) => Flowing {
                origin: AnchorKind::StatementOnly,
                global_origin: None,
                width_anchored: false,
                val: AVal::new(CLASS_INT | CLASS_PTR, AWidth::W8),
                from: BTreeSet::new(),
            },
            ClightExpr::EconstFloat(_, _) => Flowing {
                origin: AnchorKind::StatementOnly,
                global_origin: None,
                width_anchored: false,
                val: AVal::new(CLASS_FLOAT, AWidth::W8),
                from: BTreeSet::new(),
            },
            ClightExpr::EconstSingle(_, _) => Flowing {
                origin: AnchorKind::StatementOnly,
                global_origin: None,
                width_anchored: false,
                val: AVal::new(CLASS_FLOAT, AWidth::W4),
                from: BTreeSet::new(),
            },
            // A cast is the one form that legitimately changes both axes, so it
            // yields its own annotation and never contradicts its operand.
            ClightExpr::Ecast(inner, ty) => {
                let from = self.eval(node, inner).from;
                Flowing {
                    origin: AnchorKind::StatementOnly,
                    global_origin: None,
                    width_anchored: false,
                    val: claim_of_type(ty, self.ptr64),
                    from,
                }
            }
            ClightExpr::Eaddrof(inner, _) => {
                let _ = self.eval(node, inner);
                Flowing {
                    origin: AnchorKind::StatementOnly,
                    global_origin: None,
                    width_anchored: false,
                    val: AVal::new(
                        CLASS_PTR | CLASS_INT,
                        if self.ptr64 { AWidth::W8 } else { AWidth::W4 },
                    ),
                    from: BTreeSet::new(),
                }
            }
            ClightExpr::Ederef(inner, ty) => {
                if let Some(loc) = self.loc_of(e) {
                    let _ = self.eval(node, inner);
                    return self.leaf(node, loc, ty, AnchorKind::StatementOnly);
                }
                let from = self.eval(node, inner).from;
                Flowing {
                    origin: AnchorKind::StatementOnly,
                    global_origin: None,
                    width_anchored: false,
                    val: claim_of_type(ty, self.ptr64),
                    from,
                }
            }
            ClightExpr::Eunop(_, inner, ty) => {
                let from = self.eval(node, inner).from;
                Flowing {
                    origin: AnchorKind::StatementOnly,
                    global_origin: None,
                    width_anchored: false,
                    val: claim_of_type(ty, self.ptr64),
                    from,
                }
            }
            ClightExpr::Ebinop(_, l, r, ty) => {
                let mut from = self.eval(node, l).from;
                from.extend(self.eval(node, r).from);
                Flowing {
                    origin: AnchorKind::StatementOnly,
                    global_origin: None,
                    width_anchored: false,
                    val: claim_of_type(ty, self.ptr64),
                    from,
                }
            }
            ClightExpr::Efield(base, _, ty) => {
                let from = self.eval(node, base).from;
                Flowing {
                    origin: AnchorKind::StatementOnly,
                    global_origin: None,
                    width_anchored: false,
                    val: claim_of_type(ty, self.ptr64),
                    from,
                }
            }
            ClightExpr::Econdition(c, a, b, ty) => {
                let mut from = self.eval(node, c).from;
                from.extend(self.eval(node, a).from);
                from.extend(self.eval(node, b).from);
                Flowing {
                    origin: AnchorKind::StatementOnly,
                    global_origin: None,
                    width_anchored: false,
                    val: claim_of_type(ty, self.ptr64),
                    from,
                }
            }
            ClightExpr::EvarSymbol(_, ty)
            | ClightExpr::Esizeof(_, ty)
            | ClightExpr::Ealignof(_, ty) => Flowing {
                origin: AnchorKind::StatementOnly,
                global_origin: None,
                width_anchored: false,
                val: claim_of_type(ty, self.ptr64),
                from: BTreeSet::new(),
            },
        }
    }

    /// Apply a chunk anchor at this node, after the statement's own transfer,
    /// so a later reader of the same register meets the machine's commitment.
    ///
    /// The width is architectural whatever the chunk. The CLASS is only
    /// architectural on a chunk that names one: a wide integer or generic move
    /// is class-agnostic, so it does not agree or disagree with the statement's
    /// class -- it DISCARDS it. Meeting instead of discarding would let the
    /// loading statement's guess ("this long is an integer") outlive the move
    /// and contradict a later, equally valid reading of the same bits as a
    /// double, which is the bit-copy trap this domain exists to avoid.
    fn apply_chunk_anchor(&mut self, node: Node) {
        let Some(&(reg, anchor)) = self.anchors.chunk.get(&node) else {
            return;
        };
        if anchor.is_top() {
            return;
        }
        let loc = LocKey::Reg(reg);
        let flowing = self.get(loc);
        let class_agnostic = anchor.classes == CLASS_TOP;
        let width_ok = anchor.width == AWidth::Top
            || flowing.val.width == AWidth::Top
            || anchor.width == flowing.val.width;
        let class_ok = class_agnostic || (anchor.classes & flowing.val.classes) != 0;
        if !width_ok || !class_ok {
            self.record(node, loc, anchor, &flowing, AnchorKind::Chunk);
            self.set_anchored(loc, anchor, AnchorKind::Chunk, BTreeSet::new());
            return;
        }
        if class_agnostic {
            self.set_anchored(
                loc,
                AVal::new(CLASS_TOP, anchor.width),
                AnchorKind::Chunk,
                BTreeSet::new(),
            );
        } else {
            let classes = anchor.classes & flowing.val.classes;
            self.set_anchored(
                loc,
                AVal::new(classes, anchor.width),
                AnchorKind::Chunk,
                flowing.from,
            );
        }
    }

    fn stmt(&mut self, node: Node, s: &ClightStmt) {
        match s {
            ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner) => {
                self.stmt(node, inner);
                return;
            }
            ClightStmt::Ssequence(items) => {
                for i in items {
                    self.stmt(node, i);
                }
                return;
            }
            ClightStmt::Sset(target, rhs) => {
                let v = self.eval(node, rhs);
                let mut from = v.from.clone();
                if self.selectable.contains(&node) {
                    from.insert(node);
                }
                // A move carries the anchoring with the value: copying an
                // 8-byte machine load into a temp does not make its width a
                // guess.
                self.set_flowing(
                    LocKey::Reg(*target as RTLReg),
                    Flowing {
                        origin: v.origin,
                        global_origin: v.global_origin,
                        val: v.val,
                        width_anchored: v.width_anchored,
                        from,
                    },
                );
            }
            ClightStmt::Sassign(lhs, rhs) => {
                let v = self.eval(node, rhs);
                match self.loc_of(lhs) {
                    Some(loc) => {
                        let mut from = v.from.clone();
                        if self.selectable.contains(&node) {
                            from.insert(node);
                        }
                        self.set_flowing(
                            loc,
                            Flowing {
                                origin: v.origin,
                                global_origin: v.global_origin,
                                val: v.val,
                                width_anchored: v.width_anchored,
                                from,
                            },
                        );
                    }
                    None => {
                        // An unresolved store can hit anything addressable.
                        let _ = self.eval(node, lhs);
                        self.kill_memory();
                    }
                }
            }
            ClightStmt::Scall(dst, callee, args) => {
                let anchor = self.anchors.call.get(&node).cloned();
                for (i, a) in args.iter().enumerate() {
                    let v = self.eval(node, a);
                    if let Some((arg_anchors, _)) = anchor.as_ref() {
                        if let Some(expected) = arg_anchors.get(i) {
                            // Only the CLASS of an ABI slot is checked against
                            // an argument spelling. The width is not: passing a
                            // narrower integer where the prototype says `long`
                            // is an ordinary promotion, not a defect.
                            let class_clash =
                                !expected.is_top() && (expected.classes & v.val.classes) == 0;
                            if class_clash {
                                self.record(
                                    node,
                                    self.loc_of(a).unwrap_or(LocKey::Reg(0)),
                                    v.val,
                                    &Flowing {
                                        origin: AnchorKind::StatementOnly,
                                        global_origin: None,
                                        width_anchored: true,
                                        val: *expected,
                                        from: v.from.clone(),
                                    },
                                    AnchorKind::ExternSignature,
                                );
                            }
                        }
                    }
                }
                let _ = self.eval(node, callee);
                self.kill_memory();
                if let Some(d) = dst {
                    let ret = anchor.map(|(_, r)| r).unwrap_or_else(AVal::top);
                    self.set_anchored(
                        LocKey::Reg(*d as RTLReg),
                        ret,
                        AnchorKind::ExternSignature,
                        BTreeSet::new(),
                    );
                }
                return;
            }
            ClightStmt::Sifthenelse(cond, a, b) => {
                let _ = self.eval(node, cond);
                self.stmt(node, a);
                self.stmt(node, b);
                return;
            }
            ClightStmt::Sloop(a, b) => {
                self.stmt(node, a);
                self.stmt(node, b);
                return;
            }
            ClightStmt::Sreturn(Some(e)) => {
                let _ = self.eval(node, e);
            }
            ClightStmt::Sswitch(e, cases) => {
                let _ = self.eval(node, e);
                for (_, c) in cases {
                    self.stmt(node, c);
                }
                return;
            }
            ClightStmt::Sbuiltin(dst, _, _, args) => {
                for a in args {
                    let _ = self.eval(node, a);
                }
                self.kill_memory();
                if let Some(d) = dst {
                    self.set(LocKey::Reg(*d as RTLReg), AVal::top(), BTreeSet::new());
                }
                return;
            }
            _ => return,
        }
        self.apply_chunk_anchor(node);
    }
}

/// Fold one block's selected statements and report every flow contradiction.
///
/// `selected` gives the decided statement per node. `unresolved` gives the
/// candidate list of every node in the block whose statement is NOT decided:
/// those must not simply be skipped, because a skipped node can still DEFINE a
/// location, and letting an older anchored value flow past it invents
/// contradictions that no selection produces. Each unresolved node instead
/// forgets everything any of its candidates could write.
pub fn eval_block(
    block: &[Node],
    selected: &BTreeMap<Node, ClightStmt>,
    unresolved: &BTreeMap<Node, Vec<ClightStmt>>,
    candidates: &BTreeMap<Node, Vec<ClightStmt>>,
    anchors: &FlowAnchors,
    selectable: &BTreeSet<Node>,
    ptr64: bool,
) -> Vec<Contradiction> {
    let mut eval = Eval {
        anchors,
        ptr64,
        state: BTreeMap::new(),
        contradictions: Vec::new(),
        selectable,
        candidates,
    };
    for node in block {
        if let Some(stmt) = selected.get(node) {
            eval.stmt(*node, stmt);
            eval.note_preserving(*node, stmt);
        } else if let Some(cands) = unresolved.get(node) {
            eval.forget_possible_defs(cands);
        }
    }
    eval.contradictions
}

/// Fold every block of one function and summarise.
///
/// A block counts as ANCHORED when some machine fact reaches it; only anchored
/// blocks can be certified, because a block no anchor touches has nothing to be
/// consistent with and certifying it would inflate the fraction with vacuous
/// passes.
pub fn eval_function(
    blocks: &[Block],
    selected: &BTreeMap<Node, ClightStmt>,
    unresolved: &BTreeMap<Node, Vec<ClightStmt>>,
    candidates: &BTreeMap<Node, Vec<ClightStmt>>,
    anchors: &FlowAnchors,
    selectable: &BTreeSet<Node>,
    ptr64: bool,
) -> (FlowStats, Vec<Contradiction>) {
    let mut stats = FlowStats::default();
    let mut all = Vec::new();
    for block in blocks {
        if !block.iter().any(|n| selected.contains_key(n)) {
            continue;
        }
        stats.blocks_checked += 1;
        // Only a chunk or call anchor makes a block checkable against the
        // machine. Program-wide global types are NOT enough: they would mark
        // every block anchored and make the certified fraction vacuous.
        let anchored = block
            .iter()
            .any(|n| anchors.chunk.contains_key(n) || anchors.call.contains_key(n));
        let contras = eval_block(
            block, selected, unresolved, candidates, anchors, selectable, ptr64,
        );
        if anchored {
            stats.blocks_anchored += 1;
            if contras.is_empty() {
                stats.blocks_certified += 1;
            }
        }
        for c in &contras {
            stats.contradictions += 1;
            stats.count_kind(c.kind);
        }
        all.extend(contras);
    }
    (stats, all)
}

/// Human-readable location, with the defining address an RTL value web id
/// encodes so a reader can look the site up.
pub fn loc_label(loc: LocKey) -> String {
    match loc {
        LocKey::Reg(r) => {
            let node =
                (r & !(1u64 << 63)) >> crate::decompile::passes::rtl_pass::MREG_DISCRIMINANT_BITS;
            format!("reg {:#x}@{:#x}", r, node)
        }
        LocKey::Var(id) => format!("var {}", id),
        LocKey::Slot(base, ofs) => format!("slot {:#x}+{}", base, ofs),
    }
}

pub fn aval_label(v: AVal) -> String {
    let mut classes = String::new();
    if v.classes & CLASS_INT != 0 {
        classes.push('i');
    }
    if v.classes & CLASS_FLOAT != 0 {
        classes.push('f');
    }
    if v.classes & CLASS_PTR != 0 {
        classes.push('p');
    }
    let width = match v.width {
        AWidth::W1 => "1",
        AWidth::W2 => "2",
        AWidth::W4 => "4",
        AWidth::W8 => "8",
        AWidth::W16 => "16",
        AWidth::Top => "?",
    };
    format!("{{{}}}w{}", classes, width)
}

/// Progress guard for an explaining clause: injecting is only worthwhile when
/// some node on the chain has an alternative candidate whose claim on the
/// contradicting location could hold instead. Without one, re-searching cannot
/// reach a different answer and the contradiction is an upstream gap.
pub fn chain_has_alternative(
    contra: &Contradiction,
    candidates: &BTreeMap<Node, Vec<ClightStmt>>,
    selected_index: &BTreeMap<Node, usize>,
    ptr64: bool,
) -> bool {
    for node in &contra.chain {
        let Some(cands) = candidates.get(node) else {
            continue;
        };
        if cands.len() < 2 {
            continue;
        }
        let chosen = selected_index.get(node).copied().unwrap_or(0);
        for (i, cand) in cands.iter().enumerate() {
            if i == chosen {
                continue;
            }
            match claim_on(cand, contra.loc, ptr64) {
                // An alternative that says nothing about the location is a way
                // out too: the contradicting claim simply disappears.
                None => return true,
                Some(c) if c.compatible(contra.flowing) => return true,
                Some(_) => {}
            }
        }
    }
    false
}

/// The strongest claim a candidate statement makes about one location, or None
/// when it names the location nowhere.
pub fn claim_on(stmt: &ClightStmt, loc: LocKey, ptr64: bool) -> Option<AVal> {
    let mut found: Option<AVal> = None;
    let visit_expr = |e: &ClightExpr, found: &mut Option<AVal>| {
        let mut stack = vec![e];
        while let Some(cur) = stack.pop() {
            let hit = match cur {
                ClightExpr::Etempvar(id, ty) => {
                    (LocKey::Reg(*id as RTLReg) == loc).then(|| claim_of_type(ty, ptr64))
                }
                ClightExpr::Evar(id, ty) => {
                    (LocKey::Var(*id) == loc).then(|| claim_of_type(ty, ptr64))
                }
                _ => None,
            };
            if let Some(h) = hit {
                *found = Some(match *found {
                    Some(prev) => prev.meet(h).unwrap_or(h),
                    None => h,
                });
            }
            match cur {
                ClightExpr::Ederef(i, _)
                | ClightExpr::Eaddrof(i, _)
                | ClightExpr::Eunop(_, i, _)
                | ClightExpr::Ecast(i, _)
                | ClightExpr::Efield(i, _, _) => stack.push(i),
                ClightExpr::Ebinop(_, l, r, _) => {
                    stack.push(l);
                    stack.push(r);
                }
                ClightExpr::Econdition(c, a, b, _) => {
                    stack.push(c);
                    stack.push(a);
                    stack.push(b);
                }
                _ => {}
            }
        }
    };
    let mut stack = vec![stmt];
    while let Some(cur) = stack.pop() {
        match cur {
            ClightStmt::Sset(_, rhs) => visit_expr(rhs, &mut found),
            ClightStmt::Sassign(l, r) => {
                visit_expr(l, &mut found);
                visit_expr(r, &mut found);
            }
            ClightStmt::Scall(_, f, args) => {
                visit_expr(f, &mut found);
                for a in args {
                    visit_expr(a, &mut found);
                }
            }
            ClightStmt::Sbuiltin(_, _, _, args) => {
                for a in args {
                    visit_expr(a, &mut found);
                }
            }
            ClightStmt::Sreturn(Some(e)) => visit_expr(e, &mut found),
            ClightStmt::Sifthenelse(c, a, b) => {
                visit_expr(c, &mut found);
                stack.push(a);
                stack.push(b);
            }
            ClightStmt::Sswitch(e, cases) => {
                visit_expr(e, &mut found);
                for (_, c) in cases {
                    stack.push(c);
                }
            }
            ClightStmt::Ssequence(items) => stack.extend(items.iter()),
            ClightStmt::Slabel(_, i) | ClightStmt::Seffect(_, i) | ClightStmt::Sloop(i, _) => stack.push(i),
            _ => {}
        }
    }
    found
}

#[cfg(test)]
mod tests {
    use crate::decompile::passes::clight_select::solvers::flow::*;
    use crate::x86::types::{ClightAttr, ClightSignedness};

    fn int32() -> ClightType {
        ClightType::Tint(
            ClightIntSize::I32,
            ClightSignedness::Signed,
            ClightAttr::default(),
        )
    }

    fn f64ty() -> ClightType {
        ClightType::Tfloat(ClightFloatSize::F64, ClightAttr::default())
    }

    fn long() -> ClightType {
        ClightType::Tlong(ClightSignedness::Signed, ClightAttr::default())
    }

    #[test]
    fn int_and_pointer_never_contradict() {
        let i = claim_of_type(&long(), true);
        let p = claim_of_type(
            &ClightType::Tpointer(std::sync::Arc::new(int32()), ClightAttr::default()),
            true,
        );
        assert!(i.compatible(p));
    }

    #[test]
    fn float_contradicts_int_at_the_same_width() {
        let f = claim_of_type(&f64ty(), true);
        let i = claim_of_type(&long(), true);
        assert!(!f.compatible(i));
    }

    #[test]
    fn different_committed_widths_contradict() {
        let a = AVal::new(CLASS_INT, AWidth::W4);
        let b = AVal::new(CLASS_INT, AWidth::W8);
        assert!(!a.compatible(b));
        assert!(a.compatible(AVal::new(CLASS_INT, AWidth::Top)));
    }

    // The bit-copy trap: an integer move of a double is ordinary compiler
    // output, so the wide generic chunks commit width only.
    #[test]
    fn wide_integer_chunks_commit_width_only() {
        for chunk in [MemoryChunk::MInt64, MemoryChunk::MAny64] {
            let a = anchor_of_chunk(chunk);
            assert_eq!(a.classes, CLASS_TOP);
            assert_eq!(a.width, AWidth::W8);
            assert!(a.compatible(claim_of_type(&f64ty(), true)));
        }
        assert!(
            anchor_of_chunk(MemoryChunk::MAny32).compatible(claim_of_type(
                &ClightType::Tfloat(ClightFloatSize::F32, ClightAttr::default()),
                true
            ))
        );
    }

    #[test]
    fn narrow_integer_chunks_commit_the_integer_class() {
        let a = anchor_of_chunk(MemoryChunk::MInt32);
        assert_eq!(a.classes, CLASS_INT);
        assert_eq!(a.width, AWidth::W4);
        assert!(!a.compatible(claim_of_type(&f64ty(), true)));
    }

    fn blocks_of(edges: &[(Node, Node)], nodes: &[Node]) -> Vec<Block> {
        let mut succ: BTreeMap<Node, Vec<Node>> = BTreeMap::new();
        for (a, b) in edges {
            succ.entry(*a).or_default().push(*b);
        }
        basic_blocks(nodes, &succ)
    }

    #[test]
    fn a_straight_line_is_one_block() {
        let b = blocks_of(&[(1, 2), (2, 3)], &[1, 2, 3]);
        assert_eq!(b, vec![vec![1, 2, 3]]);
    }

    #[test]
    fn a_join_starts_a_new_block() {
        let b = blocks_of(&[(1, 3), (2, 3), (3, 4)], &[1, 2, 3, 4]);
        assert!(b.contains(&vec![1]));
        assert!(b.contains(&vec![2]));
        assert!(b.contains(&vec![3, 4]));
    }

    #[test]
    fn a_branch_ends_a_block() {
        let b = blocks_of(&[(1, 2), (1, 3)], &[1, 2, 3]);
        assert!(b.contains(&vec![1]));
        assert!(b.contains(&vec![2]));
        assert!(b.contains(&vec![3]));
    }

    // The headline case: a chunk-anchored integer load flows through a move
    // into a statement that spells the value as a double.
    #[test]
    fn an_int_chunk_flowing_into_a_float_claim_contradicts() {
        let load: Node = 0x10;
        let mov: Node = 0x11;
        let use_: Node = 0x12;
        let mut anchors = FlowAnchors::default();
        anchors
            .chunk
            .insert(load, (5, anchor_of_chunk(MemoryChunk::MInt32)));
        let mut selected = BTreeMap::new();
        selected.insert(load, ClightStmt::Sset(5, ClightExpr::EconstInt(0, int32())));
        selected.insert(mov, ClightStmt::Sset(6, ClightExpr::Etempvar(5, int32())));
        selected.insert(use_, ClightStmt::Sset(7, ClightExpr::Etempvar(5, f64ty())));
        let selectable: BTreeSet<Node> = [use_].into_iter().collect();
        let c = eval_block(
            &[load, mov, use_],
            &selected,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &anchors,
            &selectable,
            true,
        );
        assert_eq!(c.len(), 1, "expected exactly one contradiction: {:?}", c);
        assert_eq!(c[0].node, use_);
        assert_eq!(c[0].loc, LocKey::Reg(5));
        // Reported under the ORIGIN of the value it contradicts: the chunk.
        assert_eq!(c[0].kind, AnchorKind::Chunk);
        assert!(c[0].chain.contains(&use_));
    }

    // Same chain, but the chunk is a wide integer move: a bit-copied double is
    // legitimate, so nothing is reported.
    #[test]
    fn a_wide_integer_bit_copy_of_a_double_is_not_a_contradiction() {
        let load: Node = 0x20;
        let use_: Node = 0x21;
        let mut anchors = FlowAnchors::default();
        anchors
            .chunk
            .insert(load, (5, anchor_of_chunk(MemoryChunk::MInt64)));
        let mut selected = BTreeMap::new();
        selected.insert(load, ClightStmt::Sset(5, ClightExpr::EconstLong(0, long())));
        selected.insert(use_, ClightStmt::Sset(7, ClightExpr::Etempvar(5, f64ty())));
        let selectable: BTreeSet<Node> = [use_].into_iter().collect();
        let c = eval_block(
            &[load, use_],
            &selected,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &anchors,
            &selectable,
            true,
        );
        assert!(c.is_empty(), "unexpected contradictions: {:?}", c);
    }

    #[test]
    fn a_cast_absorbs_the_change_and_does_not_contradict() {
        let load: Node = 0x30;
        let use_: Node = 0x31;
        let mut anchors = FlowAnchors::default();
        anchors
            .chunk
            .insert(load, (5, anchor_of_chunk(MemoryChunk::MInt32)));
        let mut selected = BTreeMap::new();
        selected.insert(load, ClightStmt::Sset(5, ClightExpr::EconstInt(0, int32())));
        selected.insert(
            use_,
            ClightStmt::Sset(
                7,
                ClightExpr::Ecast(Box::new(ClightExpr::Etempvar(5, int32())), f64ty()),
            ),
        );
        let c = eval_block(
            &[load, use_],
            &selected,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &anchors,
            &BTreeSet::new(),
            true,
        );
        assert!(c.is_empty(), "unexpected contradictions: {:?}", c);
    }

    #[test]
    fn a_call_kills_memory_but_not_registers() {
        let store: Node = 0x40;
        let call: Node = 0x41;
        let read: Node = 0x42;
        let mut selected = BTreeMap::new();
        selected.insert(
            store,
            ClightStmt::Sassign(
                ClightExpr::Evar(90, int32()),
                ClightExpr::EconstInt(1, int32()),
            ),
        );
        selected.insert(
            call,
            ClightStmt::Scall(
                None,
                ClightExpr::EvarSymbol("f".into(), ClightType::Tvoid),
                vec![],
            ),
        );
        selected.insert(read, ClightStmt::Sset(7, ClightExpr::Evar(90, f64ty())));
        let c = eval_block(
            &[store, call, read],
            &selected,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &FlowAnchors::default(),
            &BTreeSet::new(),
            true,
        );
        assert!(
            c.is_empty(),
            "the call should have killed the Var state: {:?}",
            c
        );
    }

    #[test]
    fn an_extern_signature_argument_anchor_contradicts_a_float_argument() {
        let call: Node = 0x50;
        let mut anchors = FlowAnchors::default();
        anchors.call.insert(
            call,
            (vec![anchor_of_xtype(&XType::Xint, true)], AVal::top()),
        );
        let mut selected = BTreeMap::new();
        selected.insert(
            call,
            ClightStmt::Scall(
                None,
                ClightExpr::EvarSymbol("f".into(), ClightType::Tvoid),
                vec![ClightExpr::Etempvar(5, f64ty())],
            ),
        );
        let selectable: BTreeSet<Node> = [call].into_iter().collect();
        let c = eval_block(
            &[call],
            &selected,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &anchors,
            &selectable,
            true,
        );
        assert_eq!(c.len(), 1, "{:?}", c);
        assert_eq!(c[0].kind, AnchorKind::ExternSignature);
    }

    #[test]
    fn global_origin_identity_survives_a_move() {
        let symbol = 0x9000usize;
        let load: Node = 0x55;
        let use_: Node = 0x56;
        let mut anchors = FlowAnchors::default();
        anchors.global.insert(symbol, claim_of_type(&int32(), true));
        let selected = [
            (load, ClightStmt::Sset(5, ClightExpr::Evar(symbol, int32()))),
            (use_, ClightStmt::Sset(6, ClightExpr::Etempvar(5, f64ty()))),
        ]
        .into_iter()
        .collect();
        let contradictions = eval_block(
            &[load, use_],
            &selected,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &anchors,
            &BTreeSet::new(),
            true,
        );
        assert_eq!(contradictions.len(), 1, "{contradictions:?}");
        assert_eq!(contradictions[0].kind, AnchorKind::GlobalType);
        assert_eq!(contradictions[0].global_symbol, Some(symbol));
        assert_eq!(contradictions[0].loc, LocKey::Reg(5));
    }

    #[test]
    fn the_progress_guard_needs_a_compatible_alternative() {
        let node: Node = 0x60;
        let contra = Contradiction {
            node,
            loc: LocKey::Reg(5),
            claimed: claim_of_type(&f64ty(), true),
            flowing: AVal::new(CLASS_INT, AWidth::W4),
            kind: AnchorKind::Chunk,
            global_symbol: None,
            chain: [node].into_iter().collect(),
        };
        let mut selected_index = BTreeMap::new();
        selected_index.insert(node, 0usize);

        // Only float candidates: nothing to switch to.
        let mut cands = BTreeMap::new();
        cands.insert(
            node,
            vec![
                ClightStmt::Sset(7, ClightExpr::Etempvar(5, f64ty())),
                ClightStmt::Sset(8, ClightExpr::Etempvar(5, f64ty())),
            ],
        );
        assert!(!chain_has_alternative(
            &contra,
            &cands,
            &selected_index,
            true
        ));

        // An integer sibling is a way out.
        cands.insert(
            node,
            vec![
                ClightStmt::Sset(7, ClightExpr::Etempvar(5, f64ty())),
                ClightStmt::Sset(7, ClightExpr::Etempvar(5, int32())),
            ],
        );
        assert!(chain_has_alternative(
            &contra,
            &cands,
            &selected_index,
            true
        ));
    }

    // A forced (single-candidate) chain carries no literals at all, so there is
    // no clause to build; that is a gap, and the caller must not inject.
    #[test]
    fn a_forced_chain_yields_an_empty_clause() {
        let load: Node = 0x70;
        let use_: Node = 0x71;
        let mut anchors = FlowAnchors::default();
        anchors
            .chunk
            .insert(load, (5, anchor_of_chunk(MemoryChunk::MInt32)));
        let mut selected = BTreeMap::new();
        selected.insert(load, ClightStmt::Sset(5, ClightExpr::EconstInt(0, int32())));
        selected.insert(use_, ClightStmt::Sset(7, ClightExpr::Etempvar(5, f64ty())));
        let c = eval_block(
            &[load, use_],
            &selected,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &anchors,
            &BTreeSet::new(),
            true,
        );
        assert_eq!(c.len(), 1);
        assert!(c[0].chain.is_empty());
    }
}
