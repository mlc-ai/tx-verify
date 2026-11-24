-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.StatsCreditHistory
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreReadyUpdate
import all Kernels.TmlFa4Fwd.Proof.StatsCreditHistory
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Prologue

/-- A successful softmax poll at one of the three score acquire sites. -/
def scoreAcquired (e : Event) : Bool :=
  match e.kind with
  | .wait _ _ true _ _ => [3425,5109,6676].contains e.pc
  | _ => false

/-- Successful waits on the stage's score object are exactly the successful score acquires. -/
theorem scorePollCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} (stage : Fin 2) (hStage : stage.val = warpIndex l g / 4) :
    okPolls (Thread.Scores.scoreReadyObject l (g/l.block) stage) ((X.tr g).take j) =
      ((X.tr g).take j).countP scoreAcquired := by
  have hw : warpIndex l g < 8 := by have := stage.isLt; omega
  rw [Flow.okPolls]
  apply List.countP_congr
  intro f hf
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hf
  have hK := (List.getElem?_eq_some_iff.mp hk).1
  simp only [List.length_take] at hK
  rw [List.getElem?_take_of_lt (by omega)] at hk
  obtain ⟨pc,kind⟩ := f
  cases kind <;> try rfl
  rename_i loc q ok acq scope
  cases ok
  · rfl
  · have he : X.get (g,k) = some ⟨pc,.wait loc q true acq scope⟩ := hk
    have hSite := Correction.softmaxPollOfRole hp hX he hw
    obtain ⟨_,hAddr⟩ := softmaxWaitExactAddress hp hX he hSite
    subst hAddr
    simp only [sourceWaitSuccess,scoreAcquired,Thread.Scores.scoreReadyObject,decide_eq_true_eq,
      List.contains_iff_mem]
    rw [← hStage]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hSite ⊢
    rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [softmaxWaitBaseOffset] <;> omega

end PTX.Kernels.TmlFa4Fwd.Softmax
