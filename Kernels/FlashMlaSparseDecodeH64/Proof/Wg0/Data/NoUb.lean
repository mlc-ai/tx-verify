-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.NoUbTma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Machine

@[expose] public section

/-! # The event fired from a state of warpgroup 0's data machine is no fault

`w0_nonub`: from a state of the data machine whose control words are well formed (`W0State`:
the ring slot words are slots, the pointers a site loads through are set) and whose payload
registers hold values of the width the stores need (`PayAll`), the event of the site's template
is no fault. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

/-- The control words of a state that its site reads as slots and pointers. -/
structure W0State (P : Params) (d : Control.D) : Prop where
  ringV : (d.site = .wv ∨ d.site = .arrV ∨ d.site = .vm) → ∃ v < 4, d.vs = W v
  ringS : (d.site = .wq ∨ d.site = .arrS ∨ d.site = .wsv) → ∃ b < 2, d.sl = W b
  ptr : PtrOk P d

/-- The payload registers of the instruction a store, a vote or a Tensor Memory store fires. -/
def PayAll (t : TState) (ins : Instr) : Prop := PayMem t ins ∧ PayTc t ins ∧ PayVote t ins

/-- The control state's concrete state of a data state's. -/
theorem w0_ctl_atD {d : D} {t : TState} (hat : (code P L g w).AtD d t) :
    (Control.code P L g w).AtD d.c t := by
  obtain ⟨hpc, hsub, hacc, hf, hF⟩ := hat
  exact ⟨hpc, hsub, hacc, hf, ((holds_append _ _ _).mp hF).1⟩

/-- **The event fired from a state of the data machine is no fault.** -/
theorem w0_nonub (hp : Pre P L m) (hg : g < L.threads ∧ g / L.block < L.grid)
    (ht : tidOf L g < 128) (hw : w = warpW L g) (d : D) (hs : W0State P d.c) {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (hat : (code P L g w).AtD d t)
    (hi : (code P L g w).inv d) (hc : kernel.code[(code P L g w).pc d]? = some ins)
    (hf : Fires ((code P L g w).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hpay : PayAll t ins) : ∀ f, e.kind ≠ .ub f := by
  have hC := w0_ctl_atD hat
  obtain ⟨hMem, hTc, hVote⟩ := hpay
  cases hsite : d.c.site with
  | smr => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | bwait => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | bar0 => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | bar2 => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | ebar0 => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | ebar1 => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | bar1 => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | ebar => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | tcfa => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | rsf => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | efa => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | tcfb => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | rsfb => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | fpx => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | sldw => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | commit => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | exit => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | obar c => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | ofpx c => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | rldw c => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | oldw c => exact noUbAt_pure hp d.c (by simp [hsite, Site.pure]) hC hi hc hf
  | sink => exact noUbAt_nc hp d.c hs.ptr (by simp [hsite]) hC hi hc hf
  | lenA => exact noUbAt_nc hp d.c hs.ptr (by simp [hsite]) hC hi hc hf
  | lenB => exact noUbAt_nc hp d.c hs.ptr (by simp [hsite]) hC hi hc hf
  | arrL => exact noUbAt_arrL hp d.c hsite hC hi hc hf
  | wv => exact noUbAt_ringV hp d.c (by simp [hsite]) (hs.ringV (by simp [hsite])) hC hi hc hf
  | arrV => exact noUbAt_ringV hp d.c (by simp [hsite]) (hs.ringV (by simp [hsite])) hC hi hc hf
  | wq => exact noUbAt_ringS hp d.c (by simp [hsite]) (hs.ringS (by simp [hsite])) hC hi hc hf
  | arrS => exact noUbAt_ringS hp d.c (by simp [hsite]) (hs.ringS (by simp [hsite])) hC hi hc hf
  | wsv => exact noUbAt_ringS hp d.c (by simp [hsite]) (hs.ringS (by simp [hsite])) hC hi hc hf
  | sld a k => exact noUbAt_tcld hp d.c (.inl ⟨a, k, hsite⟩) hC hi hc hf
  | rld c => exact noUbAt_tcld hp d.c (.inr (.inl ⟨c, hsite⟩)) hC hi hc hf
  | old c => exact noUbAt_tcld hp d.c (.inr (.inr ⟨c, hsite⟩)) hC hi hc hf
  | rstw c => exact noUbAt_rstw hp d.c ⟨c, hsite⟩ hC hi hc hf
  | vm => exact noUbAt_vm hp d.c hsite hw ht (hs.ringV (by simp [hsite])) hC hi hc hf
  | pld k => exact noUbAt_pld hp d.c ⟨k, hsite⟩ hw ht hC hi hc hf
  | mld => exact noUbAt_row hp d.c (.inl hsite) hw ht hC hi hc hf
  | eld => exact noUbAt_row hp d.c (.inr hsite) hw ht hC hi hc hf
  | pst k => exact noUbAt_pst hp d.c ⟨k, hsite⟩ hw ht hC hi hc hf hMem
  | mst => exact noUbAt_mst hp d.c (.inl hsite) hw ht hC hi hc hf hMem
  | est => exact noUbAt_mst hp d.c (.inr hsite) hw ht hC hi hc hf hMem
  | ost k => exact noUbAt_ost hp d.c ⟨k, hsite⟩ hw ht hC hi hc hf hMem
  | lse => exact noUbAt_lse hp d.c hsite hC hi hc hf hMem
  | ost2 c k => exact noUbAt_ost2 hp hg d.c ⟨c, k, hsite⟩ ht hC hi hc hf hMem
  | rst c => exact noUbAt_rst hp d.c ⟨c, hsite⟩ hC hi hc hf hTc
  | vote => exact noUbAt_vote hp d.c hsite hC hi hc hf hVote
  | oel c => exact noUbAt_oel d.c ⟨c, hsite⟩ hC hi hc hf
  | otma c => exact noUbAt_otma hp d.c ⟨c, hsite⟩ hw ht hC hi hc hf
  | dealloc => exact noUbAt_dealloc hp d.c hsite hC hi hc hf

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
