-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.Synchronization
public meta import Kernels.TmlFa4Fwd.Assumptions.Synchronization
public meta import Kernels.TmlFa4Fwd.Assumptions.DelayedTmem
public meta import Kernels.TmlFa4Fwd.Data.Decoded
public meta import Core.Assumption.TcLdDataflow

open PTX PTX.Assumption PTX.Kernels.TmlFa4Fwd
open PTX.Kernels.TmlFa4Fwd.Assumptions

/- Each of the 48 decoded polls controls an immediate guarded success branch and a retry.
The four plain branches do not select the uniform-poll assumption. -/
#eval show IO Unit from do
  let code : List Instr := Decoded.kernel.code
  let waits := code.zipIdx.filterMap fun (i, pc) => match i.op with
    | .mbarWait dst _ _ _ _ _ => some (i.guard, dst, pc)
    | _ => none
  unless waits.length == 48 do throw (IO.userError "mbarrier poll count mismatch")
  let mut uniform := []
  let mut plain := []
  for (guard, dst, pc) in waits do
    let (some ⟨some (pred, false), .bra target uni⟩, some ⟨none, .bra retry retryUni⟩) :=
      (code[pc + 1]?, code[pc + 2]?) |
      throw (IO.userError s!"mbarrier poll branch shape mismatch at {pc}")
    unless guard.isNone && pred == dst && retry == pc && target == pc + 3 && uni == retryUni do
      throw (IO.userError s!"mbarrier poll branch predicate or target mismatch at {pc}")
    if uni then uniform := (pc + 1) :: uniform else plain := (pc + 1) :: plain
  unless uniform.reverse == pollAgreeSites && plain.reverse == plainPollSites do
    throw (IO.userError "poll-agreement site mismatch")

/- All explicit wait::ld instructions are reached from an output load after four local moves.
For the other loads, independently check the existing straight-line consumption rule. -/
#eval show IO Unit from do
  let code : List Instr := Decoded.kernel.code
  let loads := code.zipIdx.filterMap fun (i, pc) => match i.op with
    | .tcLd .. => some pc
    | _ => none
  let waitSites := code.zipIdx.filterMap fun (i, pc) => match i.op with
    | .tcWaitLd => some pc
    | _ => none
  let explicit := loads.filter fun pc => (code[pc + 5]?).any fun i => match i with
    | ⟨none, .tcWaitLd⟩ => true
    | _ => false
  for pc in explicit do
    unless (code.drop (pc + 1) |>.take 4).all (fun i => match i with
      | ⟨none, .move _⟩ => true
      | _ => false) do throw (IO.userError s!"unexpected path to wait::ld at {pc}")
  unless loads.length == 60 && waitSites.length == 32 && explicit.map (· + 5) == waitSites do
    throw (IO.userError "TMEM load or explicit wait site mismatch")
  let consumed := loads.filter (ldConsumedAt Decoded.kernel)
  let uncovered := loads.filter fun pc => !explicit.contains pc && !consumed.contains pc
  unless consumed == tcLdDataflowSites && uncovered == tcLdUncoveredSites do
    throw (IO.userError s!"TMEM completion site mismatch: {consumed} / {uncovered}")

/- The first Q-empty arrival is followed by the second-stage arrival. Their next explicit Q
tail poll observes only the second-stage shared offset. Every tcgen05 commitment is CTA group 1. -/
#eval show IO Unit from do
  let code : List Instr := Decoded.kernel.code
  let commits := code.zipIdx.filter fun (i, _) => match i.op with
    | .tcCommit .. => true
    | _ => false
  let sites := commits.map (·.2)
  unless sites == [2208, 2270, 2274, 2418, 2462, 2519, 2523, 2537, 2541, 2638, 2642, 2646] &&
      commits.all (fun (i, _) => match i with
        | ⟨none, .tcCommit .one _ _ none⟩ => true
        | _ => false) do
    throw (IO.userError "TMEM commit site or CTA group mismatch")
  match code[2537]?, code[2541]?, code[1892]?, code[1893]? with
  | some (Instr.mk none (.tcCommit .one b0 16 none)),
    some (Instr.mk none (.tcCommit .one b1 24 none)),
    some (Instr.mk none (.int add)), some (Instr.mk none (.mbarWait _ b 0 _ true .cta)) =>
    unless b0 == b1 && add.op == .add && add.dsts == [some b] &&
        add.srcs == [.reg b0, .imm 24] && commitOrderSites == [2537] do
      throw (IO.userError "Q-empty commit or loader-tail address mismatch")
  | _, _, _, _ => throw (IO.userError "Q-empty commit or loader-tail shape mismatch")

/- The diagnostic below follows score registers across the two bias polls. It records
the shared-bias traffic's reads and writes without counting any of them as score use. -/
private def biasSideEffect : Op → Option (List Nat × List Nat)
  | .tcLd ds addr _ red => some ([addr], ds ++ red.toList.map (·.dst))
  | .mbarWait d b _ par _ _ => some (b :: opndReg par, [d])
  | .mbarArrive b _ tx count _ _ _ state =>
    some (b :: opndRegs [tx, count], state.toList)
  | .mem m =>
    if m.kind == .load && m.space == some (.shared .cta) then
      match m.addr.base with
      | .reg r _ => some ([r], m.regs)
      | _ => none
    else none
  | .bra .. | .fence .. => some ([], [])
  | .barSyncN bar count _ => some (opndRegs [bar, count], [])
  | _ => none

private def lastBiasConsumer (code : List (Instr × Nat)) (pending : List Nat)
    (aliases : List (Nat × List Nat)) : Option Nat := do
  let (ins, pc) :: rest := code | none
  if ins.guard.isSome then
    match ins.op with
    | .bra .. => pure ()
    | _ => none
  let side := biasSideEffect ins.op
  let (reads, writes) ← match side with
    | some rw => some rw
    | none => (localWrites ins.op).map fun wr => (localReads ins.op, wr)
  let reads := reads ++ ins.guard.toList.map (·.1)
  let used := (aliases.filter fun p => reads.contains p.1).flatMap (·.2)
  if side.isSome && !used.isEmpty then none else
    let move := side.isNone && isMove ins.op
    let pending' := if side.isSome || move then pending else pending.filter (!used.contains ·)
    let aliases' := (aliases.filter fun p => !writes.contains p.1) ++
      (if move then writes.map fun w => (w, used) else [])
    if pending'.isEmpty then some pc
    else if pending'.all (fun p => aliases'.any (·.2.contains p)) then
      lastBiasConsumer rest pending' aliases'
    else none

/- The bias poll/retry and the optional Bias-empty arrive are the only branches before
the next softmax synchronization or write. The next S/P reuse is after these boundaries.
Both paths consume every loaded score before the boundary, but the current model has
no wait::ld at either boundary. The delayed assumption selects the later first P store. -/
#eval show IO Unit from do
  let code : List Instr := Decoded.kernel.code
  for (sites, expect, stop, optional) in
    [([3428, 3446, 3463, 3481], [3657, 3721, 3785, 3849], 4397, 3584),
     ([5112, 5129, 5146, 5163], [5342, 5406, 5470, 5534], 5682, 5272)] do
    unless code[optional]?.any (fun i => match i with
      | ⟨some (_, false), .bra d false⟩ => d == optional + 7
      | _ => false) do throw (IO.userError s!"Bias-empty branch mismatch at {optional}")
    for (load, last) in sites.zip expect do
      let some (Instr.mk none (.tcLd regs _ _ none)) := code[load]? |
        throw (IO.userError s!"bias score load mismatch at {load}")
      unless regs.length == 32 do
        throw (IO.userError s!"bias score load register count mismatch at {load}")
      let steps := ((code.drop (load + 1)).take (stop - load - 1)).zipIdx (load + 1)
      let branches := steps.filterMap fun (i, pc) => match i.op with
        | .bra .. => some pc
        | _ => none
      let poll := if stop == 4397 then 3498 else 5181
      unless branches == [poll + 1, poll + 2, optional] do
        throw (IO.userError s!"unexpected control flow of bias score load at {load}")
      let skipArrive := steps.filter fun (_, pc) => pc ≤ optional || optional + 7 ≤ pc
      let aliases := regs.map fun r => (r, [r])
      unless lastBiasConsumer steps regs aliases == some last &&
          lastBiasConsumer skipArrive regs aliases == some last do
        throw (IO.userError s!"last score consumption mismatch at {load}")

/- Between the last consumption and its first P write, fallthrough and both
outcomes of each guarded branch advance within the interval. The second path's
forward split for exponentiation reconverges before the store. -/
#eval show IO Unit from do
  let code := Decoded.kernel.code
  let rounds : List (Nat × Nat × List (Nat × Nat × Bool × Bool)) :=
    [(3849, 4826, []), (5534, 6508, [(5815, 5977, true, false), (5976, 6299, false, true)])]
  unless rounds.map (·.2.1) == delayedTmemSites do
    throw (IO.userError "late load wait site mismatch")
  for (last, anchor, expected) in rounds do
    unless code[anchor]?.any (fun i => match i with
      | ⟨none, .tcSt _ regs .s32x32b⟩ => regs.length == 16
      | _ => false) do
      throw (IO.userError s!"missing first P write at {anchor}")
    let steps := ((code.drop (last + 1)).take (anchor - last - 1)).zipIdx (last + 1)
    unless steps.length == anchor - last - 1 && steps.all (fun (i, _) => match i.op with
      | .tcLd .. | .tcSt .. | .tcAlloc .. | .tcDealloc .. | .tcRelinquish ..
      | .tcMma .. | .tcCp .. | .tcShift .. | .tcWaitLd | .tcWaitSt
      | .exit | .ret | .trap => false
      | _ => i.op.rule.isSome) do
      throw (IO.userError s!"unexpected TMEM boundary before {anchor}")
    let branches := steps.filterMap fun (i, pc) => match i.op with
      | .bra dst uni => some (pc, dst, i.guard.isSome, uni)
      | _ => none
    unless branches == expected && branches.all (fun (pc, dst, _, _) =>
        pc < dst && dst ≤ anchor) do
      throw (IO.userError s!"a branch can bypass the first P write at {anchor}")
