-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.BiasedScoreProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedAffineOrdinals

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction Thread.Scores

/-- Only failed waits and the successful acquire occur in this observed
window, so unrelated event ordinals are unchanged. -/
theorem repeatedScorePollKeepsCount {X : Execution} {g start index stop : Nat}
    {pc phase : Nat} {object : Loc} {mark : Event → Bool}
    (hStart : start ≤ index) (hStop : stop = index+1)
    (hTrace : (X.tr g).drop start = List.replicate (index-start)
      ⟨pc,.wait object phase false true .cta⟩ ++
      ⟨pc,.wait object phase true true .cta⟩ :: (X.tr g).drop stop)
    (hMark : ∀ ok, mark ⟨pc,.wait object phase ok true .cta⟩ = false) :
    ((X.tr g).take stop).countP mark = ((X.tr g).take start).countP mark := by
  let failed := Event.mk pc (.wait object phase false true .cta)
  let success := Event.mk pc (.wait object phase true true .cta)
  let window := List.replicate (index-start) failed ++ [success]
  have hSize : start+window.length = stop := by simp [window]; omega
  have hWindow : (X.tr g).drop start = window ++ (X.tr g).drop stop := by
    simpa [window,failed,success] using hTrace
  have hSilent : window.countP mark = 0 := by
    apply List.countP_eq_zero.mpr
    intro e he
    rcases List.mem_append.mp he with h | h
    · obtain ⟨_,rfl⟩ := List.mem_replicate.mp h
      exact fun he => Bool.false_ne_true ((hMark false).symm.trans he)
    · obtain rfl := List.mem_singleton.mp h
      exact fun he => Bool.false_ne_true ((hMark true).symm.trans he)
  rw [← hSize,List.take_add,hWindow,List.take_append_length,List.countP_append,hSilent,
    Nat.add_zero]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads) (warp : Fin 8)
include hp hMax hg warp

end PTX.Kernels.TmlFa4Fwd.Softmax
