-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Iface.GlobalReads
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Snoc.PlainAsyncExtend
public import Lemmas.Order.Order
import Lemmas.Step.CommitOrderExtend

@[expose] public section

/-! # A read of input bytes keeps the assumptions' constraints

A plain read that is appended to an execution reads each byte from a covering write of the
execution, or from the launch content. At one of the read-only input sites the constraint
`Assumptions.inputReadOnly` asks the launch content; it holds when no write of the execution
covers a byte of the read, which is so when the read is of input bytes and no operation writes
an input byte (the assumption's own `ub`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

/-- No write of the execution covers a byte of an input access. -/
theorem input_fresh {Q L m X a} (hp : Pre Q L m) (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (inp : Iface.InputAcc Q a) {k : Nat} (hk : k < a.size) {w a' bs'}
    (hw : X.MemWrites w a' bs') : ¬ a'.Covers (a.loc.at k) := by
  intro cov
  obtain ⟨sp, c0, rd⟩ := inp
  exact nub ⟨Q, w, a', a.loc.at k, hp, hw.intent, cov, by simp [Loc.at, sp], by simp [Loc.at, c0],
    by simpa [Loc.at] using rd k hk⟩

/-- **A read whose bytes have sources keeps the assumptions' constraints**, at an address that is
an input when the pc is one of the sites. -/
theorem wf_snoc_read {Q L m X g pc a bs r} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (inp : Assumptions.inputReadSites.contains pc = true → Iface.InputAcc Q a)
    (hr : NewRead L m X g ⟨pc, .rd a bs⟩ r a bs) :
    ∀ q ∈ Assumptions.all, q.wf L m (X.snoc g ⟨pc, .rd a bs⟩ r) := by
  intro q hq
  have hold := hX.asm q hq
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try first
    | exact hold
    | exact Assumption.commitPerformedAt_extend (fun _ _ => rfl) hold hX.tcCommit le_snoc
        (Execution.notifiedInOrder_of_eq (sel := fun _ => true) rfl)
  intro f pc' acc bs' he hs
  rw [snoc_get] at he
  split_ifs at he
  · simp only [Option.some.injEq, Event.mk.injEq, Kind.rd.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    intro k hk c hc
    have hsrc := hr.src k hk
    cases hrk : r k with
    | none =>
      rw [hrk] at hsrc
      simpa [Execution.initialByte] using hsrc _ hc
    | some w =>
      rw [hrk] at hsrc
      obtain ⟨a'', bs'', hw, hcov, -⟩ := hsrc
      exact absurd hcov (input_fresh hp nub (inp hs) hk hw)
  · exact hold f pc' acc bs' he hs

end PTX.Kernels.InklingRelDecode.Proof.Lib
