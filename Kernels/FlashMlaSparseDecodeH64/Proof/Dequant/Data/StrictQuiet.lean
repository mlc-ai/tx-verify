-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.StrictKinds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.StepFor
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.StepForSmr
public import Lemmas.Flow.DataOverStrict

@[expose] public section

/-! # The strict step at the sites whose successors have no data facts

`quiet_stepFor`: the set-up, the polls, the fence, the arrivals, the barrier and the last store of
a row take the strict step of the control machine at the erased state (`stepAt_<site>S`,
`Over.stepFor_quiet`). `stepFor_el0`: a site that is no scale load has its only element. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

/-- A state of a site that is no scale load has element `0`. -/
theorem el_zero {d : D} (hs : ∀ r, d.c.site ≠ .scale r) (hi : (code P L g w).inv d) :
    d.c.el = 0 := by
  have h : d.c.el < Control.elems d.c.site := hi
  have h1 : Control.elems d.c.site = 1 := by
    unfold Control.elems
    split
    · rename_i r hr; exact absurd hr (hs r)
    · rfl
  omega

/-- The strict step of a site with one element from its step at element `0`. -/
theorem stepFor_el0 {d : D} {e : Event} (hs : ∀ r, d.c.site ≠ .scale r)
    (h : d.c.el = 0 → (code P L g w).StepFor d e) : (code P L g w).StepFor d e :=
  fun {_ _} ins hat hi hc hf => h (el_zero hs hi) ins hat hi hc hf

/-- **The strict step at a quiet site.** -/
theorem quiet_stepFor (hp : Pre P L m) (d : D) (hq : QuietSrc d.c.site) (e : Event) :
    (code P L g w).StepFor d e := by
  have hqs : ∀ e d', (code P L g w).next d e = some (some d') → dF L g d' = [] := by
    intro e d' hn
    obtain ⟨c', hc', hd⟩ := next_ctl hn
    exact dF_quiet (dataNext_c hd ▸ quiet_succ hc' hq)
  have key : ((Control.code P L g w).inv d.c → (Control.code P L g w).StepAt d.c) →
      (code P L g w).StepFor d e := fun hS => (over P L g w).stepFor_quiet hS hqs e
  have el0 : ∀ {s : Site}, d.c.site = s → (∀ r, s ≠ .scale r) →
      (Control.code P L g w).inv d.c → d.c.el = 0 :=
    fun hs hn hi => el_zero (P := P) (L := L) (g := g) (w := w) (fun r h => hn r (hs ▸ h)) hi
  cases hs : d.c.site with
  | smr => apply key; intro hi; exact Control.stepAt_smrS hp d.c hs (el0 hs (by simp) hi)
  | lenA => apply key; intro hi; exact Control.stepAt_lenAS d.c hs (el0 hs (by simp) hi)
  | lenB => apply key; intro hi; exact Control.stepAt_lenBS d.c hs (el0 hs (by simp) hi)
  | wq => apply key; intro hi; exact Control.stepAt_wqS d.c hs (el0 hs (by simp) hi)
  | wraw => apply key; intro hi; exact Control.stepAt_wrawS d.c hs (el0 hs (by simp) hi)
  | wsv => apply key; intro hi; exact Control.stepAt_wsvS d.c hs (el0 hs (by simp) hi)
  | fpx => apply key; intro hi; exact Control.stepAt_fpxS d.c hs (el0 hs (by simp) hi)
  | arrD => apply key; intro hi; exact Control.stepAt_arrDS d.c hs (el0 hs (by simp) hi)
  | arrF => apply key; intro hi; exact Control.stepAt_arrFS d.c hs (el0 hs (by simp) hi)
  | bar => apply key; intro hi; exact Control.stepAt_barS d.c hs (el0 hs (by simp) hi)
  | exit => apply key; intro _; exact Control.stepAt_exitS d.c hs
  | scale r => exfalso; exact absurd hq (by simp [hs, QuietSrc])
  | raw r s => exfalso; exact absurd hq (by simp [hs, QuietSrc])
  | store r s =>
    obtain rfl : s = 7 := Fin.ext (by simpa [QuietSrc, hs] using hq)
    apply key; intro hi; exact Control.stepAt_store7S r d.c hs (el0 hs (by simp) hi)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data
