-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue

public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow

/-- The other softmax warps take the guarded branch from the closing barrier to the return. -/
theorem everyone_return_tail {P : Params} {L : Launch} {g : Nat} {d : D} {t u : TState}
    {mem0 : Mem0} {e : Event} (hpre : Pre P L mem0)
    (hd : d.site = .everyone) (hw : warpOf L g ≠ 0)
    (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hf : Fires d.site.pc
      (eventTmpl asms L g t (.barSyncN (.reg 2425) (.reg 2426) false)) e (some u)) :
    ∃ v, run kernel asms L g 2 u = some v ∧ At v 3611 [] := by
  rw [event_everyone hpre ha hd] at hf
  obtain ⟨_, hu⟩ := hf
  have hc : d.site.pc = 1835 := by rw [hd]; rfl
  have hsub : d.sub = 0 := by simpa [hd, Site.elems] using hi.subLt
  have h := at_next_of ha hc hsub
  rw [← Option.some.inj hu] at h
  let F := factsFrom ((Flow.live 1835).filter tracked.contains) (valueOf P L g d)
  have ht : At u 1836 F := h
  have hwlt := hi.warpLt
  have hcmp : compare .ne .b 32 (truncBits 32 (BitVec.ofNat 64 (warpOf L g)))
      (truncBits 32 (BitVec.ofInt 64 0)) = true := by
    have hs : warpOf L g = 1 ∨ warpOf L g = 2 ∨ warpOf L g = 3 := by omega
    rcases hs with hs | hs | hs <;> rw [hs] <;> decide
  obtain ⟨v, hv, hav⟩ : ∃ v, run kernel asms L g 1 u = some v ∧
      At v 1837 ((129, .pred true) :: F) := by
    simp only [F] at ht ⊢
    seg_fp ht using
      (try wg0_values)
      exact congrArg Value.pred hcmp
  have hnone : ∀ a ∈ asms, a.localRule L g v (.bra 3611 false) = none := by
    intro a ha
    exact Thread.asms_localRule_bra (t := v) (by rw [hav.1]; decide)
      (by rw [hav.1]; decide) a ha
  obtain ⟨w, hr, haw⟩ :=
    run_bra Flow.code_1837 true hav hav.2.2.2.2.1 hnone (by seg_free_pc)
  exact ⟨w, run_comp hv hr, haw.mono trivial⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
