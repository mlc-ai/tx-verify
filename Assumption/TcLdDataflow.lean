-- SPDX-License-Identifier: Apache-2.0
module

public import Assumption.ClusterScopeMbar

@[expose] public section

/-!
# Assumption constructor `tcLdDataflowAt`

A kernel declares the load-completion-by-dataflow assumption with `Assumption.tcLdDataflowAt`,
naming exactly the `tcgen05.ld` sites whose loads its proof treats as completed, as by a
`tcgen05.wait::ld`, once their registers are consumed. The static condition `ldConsumedAt` is a
decidable function of the code. This file is not itself an assumption.
-/

namespace PTX.Assumption

/-! ## ASM-TCLD-DATAFLOW — a `tcgen05.ld` whose registers are all consumed is complete
Statement: At the `tcgen05.ld` sites a kernel names where a static check finds every loaded register
  read before the thread's next memory, barrier or `tcgen05` event, the model trusts the load to be
  complete, as if a `tcgen05.wait::ld` followed it. A kernel that issues `tcgen05.wait::ld` after
  these loads does not need this assumption.

Defs: Assumption.opndReg, Assumption.opndRegs, Assumption.addrOperands, Assumption.localReads,
  Assumption.localWrites, Assumption.isMove,
  Assumption.scanConsumed, Assumption.ldConsumedAt, Assumption.tcLdDataflowAt

Source:
- §9.7.18.6.4.5: "For tcgen05.ld , an intra-thread ordering through true register dependency will
    be respected regardless of the presence or absence of other forms of synchronization. This
    form of register dependency does not imply any other form of ordering."
- §9.7.18.6.4.5: "To enforce such memory orderings and avoiding anti-dependency hazards around
    tcgen05.ld , tcgen05.wait::ld must be used."
- §9.7.18.8.5: "Instruction tcgen05.wait::ld causes the executing thread to block until all
    prior tcgen05.ld operations issued by the executing thread have completed."

Direction: trust

Effect: `tcLdDataflowAt K name sites why` selects, at exactly the sites (`pc`) in `sites` where
  the static check `ldConsumedAt K` holds, the hook `tcLdWait` (THREAD-RUN). The load is followed
  at the same `pc` by an implicit `tcgen05.wait::ld`, which then orders it by Core's own rules.
  The check follows the code from the load on, while no branch and no guarded instruction occur,
  until every destination register (the loaded registers, and `redval` of `tcgen05.ld.red`) has
  been read by a local instruction other than a move (`mov`, `pack`, `unpack`, a `cvt` with a
  rule, `selp`, `slct`: a move passes the dependency on to its destinations), with no
  destination's value overwritten before then. It fails if the thread first reaches an instruction
  that is neither local nor a `tcgen05.ld`, so the implicit wait claims nothing beyond the next
  memory, barrier or `tcgen05` event of the thread. Placing the wait right after the load also
  claims completion before the intervening loads, which no rule uses (load completion matters only
  against writes and releases). A site where the check fails keeps Core's semantics. The
  constructor sets no `wf` and no `ub`. The statement is generated from the sites and lists every
  site it covers.

Review: The text orders a `tcgen05.ld` before the instructions that depend on its registers, and
  nothing else. Completion of its Tensor Memory read, which a later write of the cells or a
  release of the allocation must follow (DEP-TC-READ-SOURCE `ReadSource .ld`, `SourceLive`), is
  given only by `tcgen05.wait::ld`. Code generated without that wait (CuTeDSL kernels) relies on the
  read being complete once the loaded values have been consumed.
-/

/-- The register of an operand. -/
def opndReg : Opnd → List Nat
  | .reg r => [r]
  | _ => []

/-- The registers of a list of operands. -/
def opndRegs (os : List Opnd) : List Nat := os.flatMap opndReg

/-- The source and destination operands of an address instruction. -/
def addrOperands : AddrInstr → List Opnd × List Nat
  | .cvta _ _ _ d a | .getctarank _ _ d a => ([a], [d])
  | .mapa _ _ d a rank => ([a, rank], [d])
  | .isspacep _ p a => ([a], [p])
  | .prefetch .. => ([], [])
  | .applypriority _ a => (match a.base with | .reg r _ => [.reg r] | _ => [], [])

/-- The registers a local instruction reads. -/
def localReads : Op → List Nat
  | .int i => opndRegs i.srcs
  | .move m => opndRegs m.srcs
  | .cvt c => opndRegs c.srcs
  | .addr c => opndRegs (addrOperands c).1
  | .float f => opndRegs f.srcs
  | .prefetchTensorMap _ _ a => opndReg a
  | _ => []

/-- The registers a local instruction writes; `none` for an instruction this check does not
classify, which makes the check fail. -/
def localWrites : Op → Option (List Nat)
  | .int i => some (i.dsts.filterMap id)
  | .move m => some (m.dsts.filterMap id)
  | .cvt c => some [c.d]
  | .addr c => some (addrOperands c).2
  | .mem a => if a.kind == .load && a.space == some .param then some a.regs else none
  | .float f => some (f.dsts.filterMap id)
  | .prefetchTensorMap .. => some []
  | _ => none

/-- A move passes the values it reads on to its destinations: `mov` (scalar, pack, unpack),
`selp`, `slct`, and a `cvt` with a Core rule (THREAD-CVT). -/
def isMove : Op → Bool
  | .move _ => true
  | .int i => match i.op with
    | .selp | .slct .. => true
    | _ => false
  | .cvt c => c.rule.isSome
  | _ => false

/-- Follow the code: `pend` are the destinations not yet consumed, `live` the registers holding
a value moved from destinations (with those destinations). True once `pend` is empty; false at
a branch, a guarded instruction, an unclassified instruction, an event other than a
`tcgen05.ld`, the end of the code, or when a pending destination's value is no longer held. -/
def scanConsumed : List Instr → List Nat → List (Nat × List Nat) → Bool
  | _, [], _ => true
  | [], _ :: _, _ => false
  | ins :: rest, pend@(_ :: _), live =>
    if ins.guard.isSome then false else
    match ins.op with
    | .tcLd ds _ _ red =>
      let ds := ds ++ red.toList.map (·.dst)
      let live' := live.filter fun p => !ds.contains p.1
      pend.all (fun o => live'.any (·.2.contains o)) && scanConsumed rest pend live'
    | .bra .. => false
    | op =>
      if !op.isLocal then false else
      match localWrites op with
      | none => false
      | some wr =>
        let origins := (live.filter fun p => (localReads op).contains p.1).flatMap (·.2)
        let pend' := if isMove op then pend else pend.filter fun o => !origins.contains o
        let moved := if isMove op then wr.map fun w => (w, origins) else []
        let live' := (live.filter fun p => !wr.contains p.1) ++ moved
        pend'.all (fun o => live'.any (·.2.contains o)) && scanConsumed rest pend' live'

/-- The `tcgen05.ld` at `pc` has all its destination registers consumed by computing
instructions before the thread's next instruction other than a local one or a `tcgen05.ld`,
on a straight path. -/
def ldConsumedAt (K : Kernel) (pc : Nat) : Bool :=
  match K.code[pc]? with
  | some ⟨_, .tcLd ds _ _ red⟩ =>
    let ds := ds ++ red.toList.map (·.dst)
    scanConsumed (K.code.drop (pc + 1)) ds (ds.map fun d => (d, [d]))
  | _ => false

/-- An implicit `tcgen05.wait::ld` after the loads at exactly `sites` of kernel `K` that pass
`ldConsumedAt`; `why` says why the kernel needs it. -/
def tcLdDataflowAt (K : Kernel) (name : String) (sites : List Nat) (why : String) :
    Assumption where
  name := name
  statement := s!"A tcgen05.ld whose destination registers are all read by computing \
    instructions (not moves), with no branch, guarded instruction or other event between, \
    before the thread's next instruction other than a local instruction or a tcgen05.ld, has \
    completed its Tensor Memory read as if tcgen05.wait::ld followed it, at exactly these sites: \
    {siteText sites}. {why}"
  tcLdWait pc := sites.contains pc && ldConsumedAt K pc

end PTX.Assumption
