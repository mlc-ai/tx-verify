-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.Classes
import Kernels.InklingRelDecode.Proof.Mma.Export.Count
import Kernels.InklingRelDecode.Proof.Lib.AssumptionStep
import Lemmas.Quiet.Progress.AsyncCp

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

/-- All commits issued by the same thread target the same set of CTA ranks. -/
private theorem targets {Q L m X g j k p q sp sq rank l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (first : X.get (g,j)=some ⟨p,.tc (.commit sp)⟩)
    (second : X.get (g,k)=some ⟨q,.tc (.commit sq)⟩) (hit : TcCommit.target sq rank=some l) :
    ∃ l', TcCommit.target sp rank=some l' := by
  have warp := Mma.Export.commit_warp hp hX hf first
  obtain ⟨_,rfl,_⟩ := Mma.Export.commit hp hX hf warp first
  obtain ⟨_,rfl,_⟩ := Mma.Export.commit hp hX hf warp second
  unfold TcCommit.target at hit ⊢
  split at hit <;> simp_all

/-- A pending commit either has its tracked MMA starts, or descends to an open MMA. -/
public theorem Prog.commit {Q L m X} (hp : Pre Q L m) (hm : Maximal L kernel Assumptions.all m X)
    (hf : Follow Q L X) (openCommit : Descent.Obl L X .commit) :
    Sched.Steps (schedule Q L) m X .commit := by
  by_cases starts : ∀ x i, AsyncCopy.TracksMma X x i → X.async.mmaStarted x=true
  · exact Sched.commit_stepsQ Lib.assumptions_step.wfQuiet hm starts
      (fun _ _ _ _ _ _ _ _ _ he _ he' _ hit => targets hp hm.1 hf he he' hit) openCommit
  · push Not at starts
    obtain ⟨x,_,tracked,missing⟩ := starts
    obtain ⟨_,_,issue,_⟩ := tracked
    refine .inr ⟨X,.mma,hm,fun drained => ?_,by simp [Sched.rank]⟩
    exact missing (hm.1.tma.2.1.2 x (drained x issue))

end PTX.Kernels.InklingRelDecode.Proof.Top
