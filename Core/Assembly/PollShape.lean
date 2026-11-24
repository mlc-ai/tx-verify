-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Memory.Order
public import Core.Source.Instr

@[expose] public section

/-!
# Canonical spins and the scope restriction on poll results

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

/-! ## DEP-CANONICAL-SPIN — the canonical spin on an mbarrier poll
Statement: A canonical spin is a loop that consists of one mbarrier poll followed by one or two
  branches: a branch on the poll's predicate leaves the loop or returns to the poll, and the other
  branch, if there is one, returns to the poll unconditionally. The loop repeats the poll with
  unchanged operands until it returns True and then leaves, and every instruction that reads the
  predicate is the branch of such a loop. The dependency order uses the exit of a canonical spin
  (`SpinExit`, DEP-ORDER), and ERR-POLL-SHAPE rejects every other use of a poll result.

Defs: Opnd.regs, Addr.regs, Op.readRegs, Instr.readsReg, Kernel.targeted, Kernel.pollReg,
  Kernel.pollDst, Kernel.spinExit?, Kernel.SpinShape, Kernel.spinPred, Kernel.SpinPred,
  Kernel.CanonicalSpin

Source:
- §9.7.15.16.19: "mbarrier.try_wait is a potentially blocking instruction which tests for the
    completion of the phase."
- §9.7.15.16.19 (an example of shape B): "waitLoop:
    mbarrier.try_wait.phase_type::primary.relaxed.cluster.shared.b64 complete, [shMem], %r1;
    @!complete bra waitLoop;"
- §9.7.15.16.19 (Examples 1a, 2 and 5, with a `nanosleep.u32` between the poll and the branch):
    "@!complete nanosleep.u32 20; @!complete bra waitLoop;"
- modelling choice (representation): the two shapes and the absence of branches into the loop
    body after the poll; the manual shows shape B only (quoted above). The model also requires the
    branch right after the poll, so the manual's examples with a `nanosleep.u32` between the poll
    and the branch (Examples 1a, 2 and 5, quoted above) are no canonical spins, and ERR-POLL-SHAPE
    rejects them

Direction: representation

Applies: every `mbarrier.try_wait` and `mbarrier.test_wait` position of a kernel

Premises: none

Effect: Definitions of the loop shapes, used by DEP-ORDER (`SpinExit`) and ERR-POLL-SHAPE. A
  canonical spin (`Kernel.CanonicalSpin`) at position `pc` is an unguarded poll writing predicate
  `p` that does not read `p`, followed either (shape A) by `@p bra exit` and an unguarded `bra pc`,
  where `exit` lies outside the positions `pc` to `pc + 2` so that a successful poll leaves the
  loop, or (shape B) by `@!p bra pc` with the exit at `pc + 2`; `bra` and `bra.uni` are both
  accepted; no branch targets the loop body after the poll (`pc + 1` and `pc + 2` in shape A,
  `pc + 1` in shape B), so the loop consists of these instructions only and its address, parity
  and hint operands do not change; and every instruction of the kernel that reads `p` is the branch
  right after a poll of such a shape that writes `p` (`Kernel.SpinPred`). Register reads are
  over-approximated (`Op.readRegs` lists every register operand an instruction may read, and an
  instruction without a family representation may read any register), which only makes fewer loops
  canonical spins.
-/

/-- The register an operand reads, if any. -/
def Opnd.regs : Opnd → List Nat
  | .reg r => [r]
  | _ => []

/-- The register an address reads, if any. -/
def Addr.regs (a : Addr) : List Nat :=
  match a.base with
  | .reg r _ => [r]
  | _ => []

/-- The registers an instruction may read, over-approximated: every register operand of the
operation that is not only a destination. `none` for an instruction without a family
representation, which may read any register. -/
def Op.readRegs : Op → Option (List Nat)
  | .prefetchTensorMap _ _ src => some src.regs
  | .prefetchTensor map coords _ cp =>
    some (map.regs ++ coords.flatMap Opnd.regs ++ (cp.map Opnd.regs).getD [])
  | .setMaxReg .. => some []
  | .int i => some (i.srcs.flatMap Opnd.regs)
  | .move m => some (m.srcs.flatMap Opnd.regs)
  | .cvt c => some (c.srcs.flatMap Opnd.regs)
  | .mem a => some (a.addr.regs ++ a.srcs.flatMap Opnd.regs)
  | .addr c => some (match c with
    | .cvta _ _ _ _ a | .isspacep _ _ a | .getctarank _ _ _ a => a.regs
    | .mapa _ _ _ a rank => a.regs ++ rank.regs
    | .prefetch _ _ _ a | .applypriority _ a => a.regs)
  | .warp w => some (w.srcs.flatMap Opnd.regs ++ (w.mask.map Opnd.regs).getD [])
  | .matrix m => some ((m.addr.map Addr.regs).getD [] ++ m.srcs.flatMap Opnd.regs)
  | .misc m => some (match m with
    | .nanosleep t => t.regs
    | _ => [])
  | .float f => some (f.srcs.flatMap Opnd.regs)
  | .barSync b _ => some b.regs
  | .barSyncN b c _ | .barArrive b c _ => some (b.regs ++ c.regs)
  | .cluster _ | .bra .. | .ret | .exit | .trap | .bulkCommit | .bulkWait .. | .fenceMbarInit
  | .cpAsyncCommit | .cpAsyncWait .. | .tcRelinquish _ | .tcFenceBefore | .tcFenceAfter
  | .tcWaitLd | .tcWaitSt => some []
  | .brx index _ _ => some index.regs
  | .cpTensor _ _ dst _ map coords mbar _ multicast _ cp =>
    some ([dst, mbar] ++ map.regs ++ coords.flatMap Opnd.regs ++
      (multicast.map fun p => p.2.regs).getD [] ++ (cp.map Opnd.regs).getD [])
  | .cpTensorStore map coords src _ cp _ _ =>
    some ([src] ++ map.regs ++ coords.flatMap Opnd.regs ++ (cp.map Opnd.regs).getD [])
  | .clcTryCancel _ dst _ mbar _ => some [dst, mbar]
  | .clcQuery _ _ response => some response.regs
  | .mbarInit base _ count => some (base :: count.regs)
  | .mbarInval base _ => some [base]
  | .fence f => some (match f with
    | .proxy _ _ (some a) => a.regs
    | _ => [])
  | .mbarArrive base _ tx count .. => some (base :: tx.regs ++ count.regs)
  | .cpBulk c => some ([c.dst, c.src] ++ c.size.regs ++ (c.mbar.map fun p => [p.1]).getD [] ++
      (c.multicast.map fun p => p.2.regs).getD [] ++
      (c.ignoreOob.map fun p => p.1.regs ++ p.2.regs).getD [] ++
      (c.cachePolicy.map Opnd.regs).getD [] ++ (c.mask.map Opnd.regs).getD [])
  | .asyncStore s =>
    some (s.addr.regs ++ s.srcs.flatMap Opnd.regs ++ (s.mbar.map Addr.regs).getD [])
  | .cpAsync dst _ src _ _ source cp => some ([dst, src] ++ (match source with
      | .full => []
      | .size n | .ignore n => n.regs) ++ (cp.map Opnd.regs).getD [])
  | .cpAsyncArrive _ base .. => some [base]
  | .prefetchBulk src _ size cp => some (src :: size.regs ++ (cp.map Opnd.regs).getD [])
  | .mbarWait _ base _ parity .. => some (base :: parity.regs)
  | .tcAlloc _ base _ n => some (base :: n.regs)
  | .tcDealloc _ taddr n => some (taddr.regs ++ n.regs)
  | .tcMma m => some (m.d :: (match m.a with
      | .smem desc => desc.regs
      | .tmem r _ => [r]) ++ m.bdesc.regs ++ m.idesc.regs ++ m.mask.flatMap Opnd.regs ++
      m.enableD.regs ++ (m.zeroColumnMask.map Opnd.regs).getD [] ++
      (m.sparse.map fun p => [p.1]).getD [] ++
      (m.scale.map fun s => [s.sfa.1, s.sfb.1]).getD [] ++ (m.lut.map fun p => [p.1]).getD [])
  | .tcCommit _ base _ mask => some (base :: (mask.map Opnd.regs).getD [])
  | .tcLd _ taddr .. => some [taddr]
  | .tcSt taddr srcs _ => some (taddr :: srcs.flatMap Opnd.regs)
  | .tcCp _ _ taddr sdesc _ => some (taddr :: sdesc.regs)
  | .tcShift _ taddr => some [taddr]
  | .unmodeled _ => none

/-- The instruction may read register `p`: through its guard or its operation. -/
def Instr.readsReg (ins : Instr) (p : Nat) : Bool :=
  (ins.guard.map (·.1 == p)).getD false || (ins.op.readRegs.map (·.contains p)).getD true

namespace Kernel

variable (K : Kernel)

/-- Some branch of the kernel targets position `t`. -/
def targeted (t : Nat) : Bool :=
  K.code.any fun ins => match ins.op with
    | .bra tgt _ => tgt == t
    | .brx _ ts _ => ts.contains t
    | _ => false

/-- The predicate the poll at `pc` writes, guarded or not. -/
def pollReg (pc : Nat) : Option Nat :=
  match K.code[pc]? with
  | some ⟨_, .mbarWait d ..⟩ => some d
  | _ => none

/-- The predicate the unguarded poll at `pc` writes, when the poll does not read it. -/
def pollDst (pc : Nat) : Option Nat :=
  match K.code[pc]? with
  | some ins@⟨none, .mbarWait d ..⟩ => if ins.readsReg d then none else some d
  | _ => none

/-- The exit of the loop of a canonical shape at `pc`: shape A (`@p bra exit; bra pc`) or shape B
(`@!p bra pc`, exit at `pc + 2`), with no branch into the loop after the poll and an exit outside
the loop. -/
def spinExit? (pc : Nat) : Option Nat :=
  match K.pollDst pc, K.code[pc + 1]?, K.code[pc + 2]? with
  | some p, some ⟨some (p', false), .bra ex _⟩, some ⟨none, .bra back _⟩ =>
    if p' == p && back == pc && !K.targeted (pc + 1) && !K.targeted (pc + 2) &&
        (ex < pc || pc + 2 < ex) then some ex
    else none
  | some p, some ⟨some (p', true), .bra back _⟩, _ =>
    if p' == p && back == pc && !K.targeted (pc + 1) then some (pc + 2) else none
  | _, _, _ => none

/-- The poll at `pc` has a canonical spin shape exiting to `exit`. -/
def SpinShape (pc exit : Nat) : Prop := K.spinExit? pc = some exit

/-- Every instruction of the kernel that may read `p` is the branch right after a poll of a
canonical spin shape that writes `p`. -/
def spinPred (p : Nat) : Bool :=
  K.code.zipIdx.all fun (ins, i) => !ins.readsReg p ||
    (decide (1 ≤ i) && (K.spinExit? (i - 1)).isSome && K.pollDst (i - 1) == some p)

/-- `spinPred` as a proposition. -/
def SpinPred (p : Nat) : Prop := K.spinPred p = true

/-- The poll at `pc` is a canonical spin of the kernel, exiting to `exit`. -/
def CanonicalSpin (pc exit : Nat) : Prop :=
  K.SpinShape pc exit ∧ ∃ p, K.pollDst pc = some p ∧ K.SpinPred p

/-! ## ERR-POLL-SHAPE — a poll result used outside a canonical spin
Statement: An execution is unsafe when it performs a poll at a position that is neither a canonical
  spin (DEP-CANONICAL-SPIN) nor a poll whose result is never read.

Defs: Kernel.PollUnused, PollShapeUnsafe

Source:
- §9.7.15.16.19: "mbarrier.test_wait is a non-blocking instruction which tests for the completion
    of the phase."
- §9.7.15.16.19: "Suspended thread resumes execution when the specified phase completes OR before
    the phase completes following a system-dependent time limit."
- DEP-CANONICAL-SPIN

Direction: stricter

Applies: every `mbarrier.try_wait` and `mbarrier.test_wait` event

Premises: none

Effect: Safety rejection (part of Unsafe). It rejects executions and never admits one: an execution
  that performs such a poll is unsafe, so a kernel can prove `Correct.safe` only if no consistent
  execution performs it. A poll whose result is never read (`Kernel.PollUnused`) writes a predicate
  that only the branches of canonical spin shapes read, each after its own poll has overwritten it.
  Rejected uses include a result saved to a register or combined with another predicate, a result
  that guards another instruction, a loop that polls several objects or contains another
  instruction, a parity or address changed inside the loop, a nested retry loop, and a single poll
  whose result a branch reads. The over-approximated register reads of DEP-CANONICAL-SPIN only
  reject more executions.

Review: The canonical-spin rule is a restriction chosen for now. Every poll in the proved and
  surveyed kernels is a canonical spin (the POLL-PATTERNS survey in the project archive), and any
  other use of a poll result is rejected. The general alternative is register dependency, the
  manual's term (§9.7.18.6.4.5 "Register dependencies, same thread"; §8.10.4 "chains of instruction
  dependencies"). Along one thread's run, each register carries the set of value-returning events
  its value derives from. A value-returning event e writing d sets prov(d) = {e} ∪ dep(e). A local
  instruction writing d takes the union of the provenance of every register it reads and of its
  guard, also when the guard is false and d is unchanged. Each conditional or indexed branch adds
  the provenance of its predicate or index to a path provenance that only grows. dep(e) is the
  provenance of e's registers, its guard and the path provenance at e. An event that depends on an
  observing event comes after what that event observed. Loops need no fixpoint, because the
  definition follows the dynamic run. Its cost is a trust reading (EXT) that ptxas preserves
  PTX-level register dependencies, including control through branches, because the growing path
  provenance also counts a branch whose arms execute the same instruction. Its benefits: no
  rejection of non-canonical poll code; it could shrink FA4's tcLdDataflow assumption through
  §9.7.18.6.4.5; and it would serve a later §8.10.4 No-Thin-Air axiom. With it, the canonical spin
  becomes a lemma. Revision 8 of the dependency design and the codex design review rounds 6 and 7
  (the older-instance and guarded-poll counterexamples) explain why the provenance must be dynamic
  and must include the returning event's own dependencies.
-/
/-- The result of the poll at `pc` is never read: only branches of canonical spin shapes read its
predicate, each after its own poll has overwritten it, and `pc` is not a canonical spin. -/
def PollUnused (pc : Nat) : Prop :=
  (∃ p, K.pollReg pc = some p ∧ K.SpinPred p) ∧ ¬ ∃ exit, K.CanonicalSpin pc exit

end Kernel

/-- The execution contains a poll at a position that is neither a canonical spin nor a poll whose
result is never read. -/
def PollShapeUnsafe (K : Kernel) (X : Execution) : Prop :=
  ∃ e pc m q ok acq sc, X.get e = some ⟨pc, .wait m q ok acq sc⟩ ∧
    (¬ ∃ exit, K.CanonicalSpin pc exit) ∧ ¬ K.PollUnused pc

end PTX
