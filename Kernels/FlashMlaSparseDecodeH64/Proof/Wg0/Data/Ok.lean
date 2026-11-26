-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.OkSite

@[expose] public section

/-! # The data flag holds at every inner site of the loop

`OkInv d`: at an inner site (on the chain and past the `setmaxnreg`) the data flag `ok` is set,
so the data facts of the site (`dF`) are present. `okInv_next`: every followed data step keeps it
(from `OkSite.lean` for the chain's and the epilogue's sites; the softmax-ready arrival keeps the
flag); `okInv_init`: the initial state is at the `setmaxnreg`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

def OkInv (d : D) : Prop := innerSite d.c.site = true → d.ok = true

theorem okInv_next {d d' : D} {e : Event} (hd : OkInv d)
    (h : (code P L g w).next d e = some (some d')) : OkInv d' := by
  obtain ⟨c', hc, rfl⟩ := next_ctl h
  by_cases hs : d.c.site = .arrS
  · intro hi
    rw [dataNext_c] at hi
    have hok : d.ok = true := hd (by simp [innerSite, onChain, hs, isStart])
    simp only [dataNext, hs, hok]
  · intro hi
    rw [dataNext_c] at hi
    rw [dataNext_eq hs]
    by_cases hch : onChain d.c.site = true
    · have hsu : succOk d.c c' = true := (okc_chain hch hs hc).resolve_right (by simpa using hi)
      have h1 : (isStart d.c.site || d.ok) = true := by
        by_cases hst : isStart d.c.site = true
        · simp [hst]
        · have : innerSite d.c.site = true := by simp_all [innerSite]
          simp [hd this]
      simp [h1, hsu]
    · rw [okc_off (by simpa using hch) hc] at hi; cases hi

theorem okInv_init : OkInv (code P L g w).init := by
  intro h
  exact absurd h (by decide : ¬innerSite .smr = true)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
