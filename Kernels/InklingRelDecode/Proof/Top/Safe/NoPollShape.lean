-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Kernel.Goals
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotWait
public import Lemmas.Flow.WaitLoopPcs
public import Lemmas.Flow.OpPcsFast

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top.Safe
open PTX PTX.Proof PTX.Flow

set_option maxRecDepth 100000

def waitPcs : List Nat := [1257, 2239, 2374, 2462, 2510, 2565]

def isWaitOp : Op → Bool
  | .mbarWait .. => true
  | _ => false

theorem kernel_wait_pcs : OpPcsFast kernel.code isWaitOp waitPcs = true := by decide +kernel

def spinOk (pc : Nat) : Bool :=
  (kernel.spinExit? pc).isSome &&
    (match kernel.pollDst pc with
      | some p => kernel.spinPred p
      | none => false)

/-- **Each of the kernel's polls is a canonical spin**: all six are shape B,
`mbarrier.try_wait` followed by `@!complete bra.uni` back to the poll. -/
theorem kernel_spins : waitPcs.all spinOk = true := by decide +kernel

theorem canonical_of_spinOk {pc : Nat} (h : spinOk pc = true) :
    ∃ exit, kernel.CanonicalSpin pc exit := by
  unfold spinOk at h
  cases hs : kernel.spinExit? pc with
  | none => simp [hs] at h
  | some ex =>
    cases hp : kernel.pollDst pc with
    | none => simp [hs, hp] at h
    | some p =>
      simp only [hs, hp, Option.isSome_some, Bool.true_and] at h
      exact ⟨ex, hs, p, hp, h⟩

/-- **Every poll fires from a canonical spin**: a poll event fires from a listed poll of the
code (`SyncSites.waitPcs`), each of which heads a canonical spin (DEP-CANONICAL-SPIN). -/
theorem poll_spins (hX : Consistent L kernel Assumptions.all mem0 X) {e : EvId} {pc : Nat} {m : Loc}
    {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (he : X.get e = some ⟨pc, .wait m p ok acq sc⟩) : ∃ exit, kernel.CanonicalSpin pc exit := by
  rcases Flow.get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hf
  · by_cases hw : ∃ q b off par a s, ins.op = .mbarWait q b off par a s
    · obtain ⟨q, b, off, par, a, s, hop⟩ := hw
      have hop' : isWaitOp ins.op = true := by rw [hop]; rfl
      have hmem := OpPcsFast.mem kernel_wait_pcs hc hop'
      have hall := List.all_eq_true.mp kernel_spins _ hmem
      exact canonical_of_spinOk hall
    · push Not at hw
      exact absurd rfl (Flow.fires_notWait (Flow.eventTmpl_notWait hw) hf m p ok acq sc)

/-- **No poll breaks the canonical shape.** -/
theorem noPollShape (hX : Consistent L kernel Assumptions.all mem0 X) :
    ¬ PollShapeUnsafe kernel X := by
  rintro ⟨e, pc, m, q, ok, acq, sc, he, hns, -⟩
  exact hns (poll_spins hX he)

end PTX.Kernels.InklingRelDecode.Proof.Top.Safe
