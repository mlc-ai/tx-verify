-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MbarOperands
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputQueryObject
import all Kernels.TmlFa4Fwd.Proof.Thread.OutputQueryObject

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Output
open PTX PTX.Flow PTX.Proof AsyncCopy Prologue

private def loaderPolls : List Nat :=
  [517, 679, 704, 730, 756, 782, 1146, 1175, 1361, 1893]

private def loaderRingPolls : List Nat := [960, 1206, 1430, 1611, 1866, 1877, 1888]
private def mmaPolls : List Nat := List.ofFn (fun site : Fin 14 => (Mma.waitSite site).pc)
private def outputPolls : List Nat := [2958, 2972]
private def scorePolls : List Nat := [3420, 3425, 3498, 4874, 5109, 5181, 6558, 6676, 7463, 7738]
private def correctionPolls : List Nat := [8473, 8476, 8769, 8772, 9201]

private def pollOp : Op → Bool
  | .mbarWait .. => true
  | _ => false

private theorem pollSites :
    OpPcsFast kernel.code pollOp
      (loaderPolls ++ loaderRingPolls ++ mmaPolls ++ outputPolls ++ scorePolls ++ correctionPolls)
      = true := by
  decide +kernel

/-- An observed event belongs to the MMA warp's input processing or its continuation. -/
def MmaAfterInput (l : Launch) (X : Execution) (i : EvId) : Prop :=
  warpIndex l i.1 = 12 ∧ ∃ e, X.get i = some e ∧ 2141 ≤ e.pc

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Only the MMA warp observes the completion objects of the Q loads. -/
theorem queryWaitMmaAfterInput {wait : EvId} {cta parity : Nat} {stage : Fin 2} {scope : MbarScope}
    (hWait : ∃ pc, X.get wait = some ⟨pc, .wait (queryObject l cta stage) parity true true scope⟩) :
    MmaAfterInput l X wait := by
  obtain ⟨pc, he⟩ := hWait
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨_, ins, _, _, hCode, hFire⟩
  · cases hBad
  obtain ⟨_, _, _, _, _, hop, _⟩ := fires_wait_flags hFire rfl
  have hSite := OpPcsFast.mem pollSites hCode (show pollOp ins.op = true by rw [hop]; rfl)
  have hStage := stage.isLt
  have notQuery {off : Nat} (hOff : 8 < off)
      (hLoc : queryObject l cta stage = ⟨.shared, wait.1 / l.block, l.sharedBase + off⟩) :
      False := by
    have ha := congrArg Loc.addr hLoc
    change l.sharedBase + 8 * stage.val = l.sharedBase + off at ha
    omega
  simp only [List.mem_append, or_assoc] at hSite
  rcases hSite with hLoad | hRing | hMma | hOut | hScore | hCorr
  · obtain ⟨off, hoff, hLoc⟩ := Loader.loaderFixedWaitAddress hp hX he hLoad
    apply (notQuery _ hLoc).elim
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    omega
  · obtain ⟨off, hoff, hLoc⟩ := Loader.loaderRingWaitAddress hp hX he hRing
    apply (notQuery _ hLoc).elim
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    omega
  · obtain ⟨site, rfl⟩ := List.mem_ofFn.mp hMma
    have hRange : 2141 ≤ (Mma.waitSite site).pc ∧ (Mma.waitSite site).pc < 2768 := by
      fin_cases site <;> decide
    have hLate : 173 < (Mma.waitSite site).pc := by omega
    have hNotHint : (Mma.waitSite site).pc ∉ registerHintSites := by
      simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hRole : roleBodyPc (warpIndex l wait.1) (Mma.waitSite site).pc :=
      roleBodyPcOfEvent hp hX he hLate hNotHint
    refine ⟨?_, _, he, hRange.1⟩
    rcases hRole with ht | ht
    · omega
    · split_ifs at ht <;> omega
  · obtain ⟨off, hoff, hLoc⟩ := OutputWarp.waitAddress hp hX he
      (by simpa [outputPolls] using hOut)
    apply (notQuery _ hLoc).elim
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    omega
  · obtain ⟨off, hoff, hLoc⟩ := Softmax.softmaxWaitAddress hp hX he hScore
    apply (notQuery _ hLoc).elim
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    omega
  · obtain ⟨off, hoff, hLoc⟩ := Correction.correctionWaitAddress hp hX he hCorr
    apply (notQuery _ hLoc).elim
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    omega

/-- Only the MMA warp observes the completion objects of the Q loads. -/
theorem queryWaitIsMma {wait : EvId} {cta parity : Nat} {stage : Fin 2} {scope : MbarScope}
    (hWait : ∃ pc, X.get wait = some ⟨pc, .wait (queryObject l cta stage) parity true true scope⟩) :
    warpIndex l wait.1 = 12 :=
  (queryWaitMmaAfterInput hp hX hWait).1

/-- A Q load byte can be made visible by an acquire in the MMA warp alone. -/
theorem queryLoadFinishedMmaAfterInput {load wait : EvId} {addr cta x y k : Nat}
    {spec : TensorCopy.Spec} {stage : Fin 2} (hIssue : X.TensorIssue load addr spec)
    (hObject : spec.mbar = queryObject l cta stage)
    (hFinished : AsyncFinished l X load (.write (.load x y k)) wait) :
    MmaAfterInput l X wait := by
  rcases hFinished with ⟨kind, hVisible, _, _⟩ | ⟨scope, hObserved, _⟩
  · cases kind with
    | bulk mode => cases mode <;> cases hVisible
    | cpAsync => cases hVisible
  · obtain ⟨notification, loc, hNotify, hWait⟩ := hObserved
    change notification = .async load (.notify .load) ∧ NotifyOn X load .load loc at hNotify
    obtain ⟨_, observed, addr', _, hi, hm, _⟩ := hNotify
    obtain ⟨pc, he⟩ := hIssue
    obtain ⟨pc', he'⟩ := hi
    rw [he] at he'
    have hs := (Kind.tensorIssue.inj (Event.mk.inj (Option.some.inj he')).2).2
    rw [← hs, hObject] at hm
    obtain rfl := hm.symm
    obtain ⟨site, parity, hew⟩ := hWait.1
    exact queryWaitMmaAfterInput hp hX ⟨site, hew⟩

/-- A Q load byte can be made visible by an acquire in the MMA warp alone. -/
theorem queryLoadFinishedObserver {load wait : EvId} {addr cta x y k : Nat} {spec : TensorCopy.Spec}
    {stage : Fin 2} (hIssue : X.TensorIssue load addr spec)
    (hObject : spec.mbar = queryObject l cta stage)
    (hFinished : AsyncFinished l X load (.write (.load x y k)) wait) :
    warpIndex l wait.1 = 12 :=
  (queryLoadFinishedMmaAfterInput hp hX hIssue hObject hFinished).1

end PTX.Kernels.TmlFa4Fwd.Thread.Output
