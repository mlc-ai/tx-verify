-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFragmentHistory
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseCapacity

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Proof

private theorem pvFragmentAtOrBefore {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {block : Fin 4} {n : Nat} {step : Fin 8}
    (hStep : step.val ≤ n) (hn : n < 8)
    {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hMma : PvInstruction X (g, index) block ⟨n, hn⟩ d op accum mask) :
    ∃ j ≤ index,
      ((X.tr g).take j).countP (readyAtSite (pvReadySite block)) =
        ((X.tr g).take index).countP (readyAtSite (pvReadySite block)) ∧
      ∃ dest operands acc flags, PvInstruction X (g, j) block step dest operands acc flags := by
  induction n using Nat.strong_induction_on generalizing index d op accum mask with
  | h n ih =>
    by_cases hEq : step.val = n
    · have hSame : (⟨n, hn⟩ : Fin 8) = step := Fin.ext hEq.symm
      exact ⟨index, le_rfl, rfl, d, op, accum, mask, hSame ▸ hMma⟩
    · have hPos : 0 < n := by omega
      obtain ⟨prev, hBefore, hReady, d', op', accum', mask', hPrevious⟩ :=
        hMma.previousFragmentSameReadyCount hp hX hPos
      have hLt : n - 1 < n := by omega
      obtain ⟨j, hj, hCount, hFrag⟩ :=
        ih (n - 1) hLt (index := prev) (by omega) (by omega) hPrevious
      exact ⟨j, hj.trans hBefore.le, hCount.trans hReady, hFrag⟩

/-- The two value release forms delimit the steady and tail PV banks. -/
def Mma.valueReleaseForm (steady : Bool) : Mma.ReleaseForm :=
  if steady then .loopValue else .tailValue

/-- Every issued V release certifies each PV fragment in its two banks. -/
theorem Mma.ReleaseIssue.valueBank {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index wait : Nat} {spec : TcCommit.Spec} (steady : Bool)
    (hIssue : Mma.ReleaseIssue X g index (Mma.valueReleaseForm steady) spec)
    (hRank : Mma.readyOccurrence X g wait (Mma.valueReleaseForm steady) =
      Mma.releaseOccurrence X g index (Mma.valueReleaseForm steady)) (stage : Fin 2) :
    ∀ step : Fin 8, ∃ j d operands accum mask,
      PvInstruction X (g, j) (firstPvBlock steady stage) step d operands accum mask ∧
      TraceBefore X (g, wait) (g, j) ∧
      TraceBefore X (g, j) (g, index) := by
  let form := Mma.valueReleaseForm steady
  let site := Mma.releaseIndex form
  have hSite : site = (if steady then 1 else 3) := by cases steady <;> rfl
  have hGet : X.get (g, index) =
      some ⟨(commitSite (releaseCommitSite site)).pc, .tc (.commit spec)⟩ := hIssue
  have hGet' := hGet
  rw [hSite] at hGet'
  obtain ⟨last, hBefore, hCountLast, d, op, accum, mask, hLast⟩ :=
    pvLastFragmentBeforeValueRelease hp hX steady stage hGet'
  rw [← hSite] at hCountLast
  obtain ⟨hI, inst, leader, hVote, _⟩ := readyReleaseLeader hp hX site hGet
  have hCountVote := releaseElectionBalance hp hX site hVote
  change ((X.tr g).take wait).countP (readyAtSite site) =
    ElectOrd.siteOrdinal (· == (slotElect site).pc) X g (index - 1) at hRank
  let mark := readyAtSite site
  have hCountRelease :
      ((X.tr g).take index).countP mark =
        1 + ((X.tr g).take wait).countP mark := by
    have hVote' : (X.tr g)[index - 1]? =
        some ⟨(slotElect site).pc, .elect (2 ^ 32 - 1) inst leader⟩ := hVote
    have hQuiet : mark ⟨(slotElect site).pc, .elect (2 ^ 32 - 1) inst leader⟩ = false := rfl
    conv_lhs => rw [show index = index - 1 + 1 by omega, List.take_add_one, hVote']
    simp only [List.countP_append, Option.toList_some, List.countP_singleton, hQuiet,
      Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact hCountVote.trans (congrArg (1 + ·) hRank.symm)
  intro step
  obtain ⟨j, hj, hCount, d', op', accum', mask', hFrag⟩ := pvFragmentAtOrBefore hp hX
    (step := step) (by have := step.isLt; omega) (by decide : 7 < 8) hLast
  have hMark : pvReadySite (firstPvBlock steady stage) = site := by
    cases steady <;> fin_cases stage <;> rfl
  rw [hMark] at hCount
  have hReady : wait < j := by
    by_contra! hWait
    have hMono := (List.take_sublist_take_left (l := X.tr g) hWait).countP_le (p := mark)
    change ((X.tr g).take j).countP mark = ((X.tr g).take last).countP mark at hCount
    change ((X.tr g).take last).countP mark =
      ((X.tr g).take index).countP mark at hCountLast
    omega
  exact ⟨j, d', op', accum', mask', hFrag, ⟨rfl, hReady, len_of_get hFrag.decoded⟩,
    ⟨rfl, hj.trans_lt hBefore, len_of_get hGet⟩⟩

/-- A delivered V release has the same PV bank witnesses as its issue. -/
theorem Mma.EmptyReleaseAt.valueBank {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {target : Loc} {g k : Nat} (release : Mma.EmptyReleaseAt l X target g k)
    (steady : Bool) (hForm : release.form = Mma.valueReleaseForm steady) (stage : Fin 2) :
    ∀ step : Fin 8, ∃ j d operands accum mask,
      PvInstruction X (g, j) (firstPvBlock steady stage) step d operands accum mask ∧
      TraceBefore X (g, release.matched.wait) (g, j) ∧
      TraceBefore X (g, j) (g, release.index) := by
  let rank (form : Mma.ReleaseForm) := Mma.readyOccurrence X g release.matched.wait form =
    Mma.releaseOccurrence X g release.index form
  exact Mma.ReleaseIssue.valueBank hp hX steady (hForm ▸ release.issue)
    (Eq.mp (congrArg rank hForm) release.matched.ordinal) stage

end PTX.Kernels.TmlFa4Fwd.Thread
