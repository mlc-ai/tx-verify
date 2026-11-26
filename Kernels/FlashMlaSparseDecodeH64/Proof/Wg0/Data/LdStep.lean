-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.LdOk
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ev
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.SuccPc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.OkSite
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SuccRst

@[expose] public section

/-! # The loaded words along a lane's steps

`ldOk_step`: a data step keeps `LdOk`, given the event's kind at its site (`EvK`, no undefined
behaviour) and the typing of its word (`W0EvPayload`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

theorem W0EvPayload.scoreLo {sc : ℝ} {l : List Event} {e : Event} (h : W0EvPayload sc l e) :
    ∀ vals, w0TcVals e = some vals → (e.pc = 280 ∨ e.pc = 283) →
    vals.length = 32 ∧ ∀ c < 32,
      Kernels.FlashMlaSparseDecodeH64.Assumptions.scoreHalf (vals.getD c (.pred false)) := by
  obtain ⟨-, h2, -⟩ := h
  exact h2

namespace Wg0.Data

noncomputable section

theorem rec_lo_est {c : Control.D} {ev : Event} {b : Blk} {x : Nat} {vals sh}
    (hs : estLo c.site = true) (hk : ev.kind = .tc (.ld x vals sh)) :
    (record c ev b).lo = vals := by
  simp only [estLo, Bool.or_eq_true, beq_iff_eq] at hs
  rcases hs with hs | hs <;> simp [record, hs, hk, sldLo]

theorem rec_hi_est {c : Control.D} {ev : Event} {b : Blk} {x : Nat} {vals sh}
    (hs : estHi c.site = true) (hk : ev.kind = .tc (.ld x vals sh)) :
    (record c ev b).hi = vals := by
  simp only [estHi, Bool.or_eq_true, beq_iff_eq] at hs
  rcases hs with hs | hs <;> simp [record, hs, hk, sldLo]

theorem rec_o_est {c : Control.D} {ev : Event} {b : Blk} {x : Nat} {vals sh}
    (hs : estO c.site = true) (hk : ev.kind = .tc (.ld x vals sh)) :
    (record c ev b).o = vals := by
  revert hs
  cases h : c.site <;> simp [estO, record, h, hk]

theorem rec_mw_est {c : Control.D} {ev : Event} {b : Blk} {x : Acc} {bs}
    (hs : c.site = .vm) (hk : ev.kind = .rd x bs) : (record c ev b).mw = loadVal bs := by
  simp [record, hs, hk]

theorem rec_pm_est {c : Control.D} {ev : Event} {b : Blk} {x : Acc} {bs}
    (hs : c.site = .mld) (hk : ev.kind = .rd x bs) : (record c ev b).pm = loadVal bs := by
  simp [record, hs, hk]

theorem rec_pe_est {c : Control.D} {ev : Event} {b : Blk} {x : Acc} {bs}
    (hs : c.site = .eld) (hk : ev.kind = .rd x bs) : (record c ev b).pe = loadVal bs := by
  simp [record, hs, hk]

theorem rec_pw_est {c : Control.D} {ev : Event} {b : Blk} {x : Acc} {bs} {j : Nat}
    (hs : estPw j c.site c.el = true) (hk : ev.kind = .rd x bs) :
    (record c ev b).pw j = (c.a0, loadVal bs) := by
  revert hs
  cases h : c.site <;> simp [estPw, record, h, hk]
  rename_i k
  intro hj hel
  simp [hel, hj]

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem kind_tc {c : Control.D} {ev : Event} (hK : EvK P L g w c ev) (hub : ∀ f, ev.kind ≠ .ub f)
    (hs : (∃ a k, c.site = .sld a k) ∨ (∃ k, c.site = .rld k) ∨ ∃ k, c.site = .old k) :
    ∃ x vals, ev.kind = .tc (.ld x vals .s32x32b) := by
  unfold EvK at hK
  rcases hs with ⟨a, k, hs⟩ | ⟨k, hs⟩ | ⟨k, hs⟩ <;> rw [hs] at hK <;>
    simp only [TcLdEv] at hK <;> rcases hK with ⟨vals, hk⟩ | ⟨f, hf⟩
  all_goals first | exact ⟨_, vals, hk⟩ | exact absurd hf (hub f)

theorem kind_rd {c : Control.D} {ev : Event} (hK : EvK P L g w c ev) (hub : ∀ f, ev.kind ≠ .ub f)
    (hs : c.site = .vm ∨ (∃ k, c.site = .pld k) ∨ c.site = .mld ∨ c.site = .eld) :
    ∃ x bs, ev.kind = .rd x bs := by
  unfold EvK at hK
  rcases hs with hs | ⟨k, hs⟩ | hs | hs <;> rw [hs] at hK
  · rcases hK with ⟨a, bs, hk, -⟩ | ⟨f, hf⟩
    · exact ⟨a, bs, hk⟩
    · exact absurd hf (hub f)
  · obtain ⟨-, hK⟩ := hK
    rcases hK with ⟨a, bs, hk, -⟩ | ⟨f, hf⟩
    · exact ⟨a, bs, hk⟩
    · exact absurd hf (hub f)
  all_goals
    rcases hK with ⟨a, bs, hk, -⟩ | ⟨f, hf⟩
    · exact ⟨a, bs, hk⟩
    · exact absurd hf (hub f)

theorem peer_ne {v : Value} (h : W0Fin (splitValue 64 v).2) : v ≠ .pred false := by
  intro hv
  subst hv
  obtain ⟨x, hx⟩ := h
  simp only [splitValue, valFloat] at hx
  rw [bitsAsFloat_eq (by intro f h; cases h)] at hx
  simp [Value.bitPattern] at hx

theorem clean_ne {v : Value} (h : PTX.Flow.Clean v) : v ≠ .pred false := by
  intro h0
  rw [h0] at h
  exact absurd h.1 (by simp [Value.bytes])

theorem tc_ne {c : Control.D} {ev : Event} {sc : ℝ} {l : List Event} {x : Nat}
    {vals : List Value} {sh : TcShape} (hpay : W0EvPayload sc l ev) (hpc : ev.pc = c.site.pc)
    (hs : (∃ a k, c.site = .sld a k) ∨ (∃ k, c.site = .rld k) ∨ ∃ k, c.site = .old k)
    (hk : ev.kind = .tc (.ld x vals sh)) : vals ≠ [] := by
  have hv : w0TcVals ev = some vals := by simp [w0TcVals, hk]
  have hl : vals.length ≠ 0 → vals ≠ [] := fun h h0 => h (by simp [h0])
  rcases hs with ⟨a, k, hs⟩ | ⟨k, hs⟩ | ⟨k, hs⟩
  · rw [hs] at hpc
    have : ev.pc = 278 ∨ ev.pc = 280 ∨ ev.pc = 283 ∨ ev.pc = 285 := by
      cases a <;> fin_cases k <;> simp [Site.pc] at hpc <;> omega
    rcases this with h | h | h | h
    · exact hl (by have := (hpay.scoreHi vals hv (Or.inl h)).1; omega)
    · exact hl (by have := (hpay.scoreLo vals hv (Or.inl h)).1; omega)
    · exact hl (by have := (hpay.scoreLo vals hv (Or.inr h)).1; omega)
    · exact hl (by have := (hpay.scoreHi vals hv (Or.inr h)).1; omega)
  all_goals
    rw [hs] at hpc
    have hm : ev.pc ∈ w0OPcs := by
      fin_cases k <;> simp [Site.pc, w0OPcs] at hpc ⊢ <;> omega
    exact hl (by have := (hpay.acc vals hv hm).1; omega)

theorem rd_ne {c : Control.D} {ev : Event} {sc : ℝ} {l : List Event} {x : Acc}
    {bs : List (Option Byte)} (hpay : W0EvPayload sc l ev) (hpc : ev.pc = c.site.pc)
    (hk : ev.kind = .rd x bs)
    (hs : c.site = .vm ∨ (∃ k, c.site = .pld k) ∨ c.site = .mld ∨ c.site = .eld) :
    loadVal bs ≠ .pred false := by
  rcases hs with hs | ⟨k, hs⟩ | hs | hs
  · rw [hs] at hpc
    obtain ⟨n, -, hr⟩ := hpay.mask x bs hk (by simpa [Site.pc] using hpc)
    simp [loadVal, hr, Except.toOption]
  · rw [hs] at hpc
    obtain ⟨v, hr, -, h2⟩ := hpay.peer x bs hk ⟨k.val, k.isLt, by simpa [Site.pc] using hpc⟩
    simpa [loadVal, hr, Except.toOption] using peer_ne h2
  · rw [hs] at hpc
    obtain ⟨v, hr, hc, -⟩ := hpay.peerMax x bs hk (by simpa [Site.pc] using hpc)
    simpa [loadVal, hr, Except.toOption] using clean_ne hc
  · rw [hs] at hpc
    obtain ⟨v, p, hr, -, hrd, -⟩ := hpay.rowSum x bs hk (by simpa [Site.pc] using hpc)
    simpa [loadVal, hr, Except.toOption] using clean_ne hrd.1

private theorem succOk_norm' (c c' : Control.D) :
    succOk c c' = succOk {site := c.site, el := if c.el = 0 then 0 else if c.el + 1 < 4 then 1
      else 4} {site := c'.site} := by
  unfold succOk
  cases c.site <;> simp only [] <;> (split_ifs <;> simp_all)

private theorem ld_chk {c c' : Control.D} (h : succOk c c' = true) :
    ldChk c.site c'.site (if c.el = 0 then 0 else if c.el + 1 < 4 then 1 else 4) = true := by
  rw [succOk_norm'] at h
  split_ifs at h ⊢
  · exact ld_tbl0 _ (Wg0.mem_allSites _) _ (Wg0.mem_allSites _) h
  · exact ld_tbl1 _ (Wg0.mem_allSites _) _ (Wg0.mem_allSites _) h
  · exact ld_tbl4 _ (Wg0.mem_allSites _) _ (Wg0.mem_allSites _) h

set_option maxRecDepth 100000 in
private theorem has_inner : ∀ s ∈ allSites, (hasLo s || hasHi s || hasMw s || hasPm s || hasO s ||
    hasPe s || (List.range 8).any (fun j => hasPw j s)) = true → innerSite s = true := by
  decide +kernel

private theorem estPw_norm {j : Nat} {s : Site} {el : Nat}
    (h : estPw j s (if el = 0 then 0 else if el + 1 < 4 then 1 else 4) = true) :
    estPw j s el = true := by
  unfold estPw at h ⊢
  split_ifs at h <;> simp_all

private theorem ldChk_fields {s s' : Site} {el : Nat} (h : ldChk s s' el = true) :
    (hasLo s' = true → hasLo s = true ∨ estLo s = true) ∧
    (hasHi s' = true → hasHi s = true ∨ estHi s = true) ∧
    (hasMw s' = true → hasMw s = true ∨ s = .vm) ∧
    (∀ j ∈ List.range 8, hasPw j s' = true → hasPw j s = true ∨ estPw j s el = true) ∧
    (hasPm s' = true → hasPm s = true ∨ s = .mld) ∧
    (hasO s' = true → hasO s = true ∨ estO s = true) ∧
    (hasPe s' = true → hasPe s = true ∨ s = .eld) := by
  have conv : ∀ a b c : Bool, ((!a || b || c) = true) → a = true → b = true ∨ c = true := by
    decide
  simp only [ldChk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨conv _ _ _ h1, conv _ _ _ h2, fun hh => ?_, fun j hj hh => conv _ _ _ (h4 j hj) hh,
    fun hh => ?_, conv _ _ _ h6, fun hh => ?_⟩
  · rcases conv _ _ _ h3 hh with h | h
    · exact Or.inl h
    · exact Or.inr (beq_iff_eq.mp h)
  · rcases conv _ _ _ h5 hh with h | h
    · exact Or.inl h
    · exact Or.inr (beq_iff_eq.mp h)
  · rcases conv _ _ _ h7 hh with h | h
    · exact Or.inl h
    · exact Or.inr (beq_iff_eq.mp h)

private theorem hasPw_start : ∀ j ∈ List.range 8,
    hasPw j .bar0 = false ∧ hasPw j .ebar0 = false := by decide

section fields
variable {sc : ℝ} {l : List Event} {c : Control.D} {ev : Event} {b : Blk}
  (hpay : W0EvPayload sc l ev) (hpc : ev.pc = c.site.pc)

include hpay hpc

theorem fld_lo (kT : ((∃ a k, c.site = .sld a k) ∨ (∃ k, c.site = .rld k) ∨ ∃ k, c.site = .old k) →
      ∃ x vals, ev.kind = .tc (.ld x vals .s32x32b))
    (hold : hasLo c.site = true → b.lo ≠ []) (hn : hasLo c.site = true ∨ estLo c.site = true) :
    (record c ev b).lo ≠ [] := by
  by_cases he : estLo c.site = true
  · have hs : ∃ a k, c.site = .sld a k := by
      simp only [estLo, Bool.or_eq_true, beq_iff_eq] at he
      rcases he with h | h
      · exact ⟨false, 1, h⟩
      · exact ⟨true, 0, h⟩
    obtain ⟨x, vals, hk⟩ := kT (Or.inl hs)
    rw [rec_lo_est he hk]
    exact tc_ne hpay hpc (Or.inl hs) hk
  · rcases rec_lo c ev b with h | ⟨x, vals, sh, hk, h2, hs2⟩
    · rw [h]; exact hold (hn.resolve_right he)
    · rw [h2]
      refine tc_ne hpay hpc (Or.inl ?_) hk
      rcases hs2 with h | h
      · exact ⟨false, 1, h⟩
      · exact ⟨true, 0, h⟩

theorem fld_hi (kT : ((∃ a k, c.site = .sld a k) ∨ (∃ k, c.site = .rld k) ∨ ∃ k, c.site = .old k) →
      ∃ x vals, ev.kind = .tc (.ld x vals .s32x32b))
    (hold : hasHi c.site = true → b.hi ≠ []) (hn : hasHi c.site = true ∨ estHi c.site = true) :
    (record c ev b).hi ≠ [] := by
  by_cases he : estHi c.site = true
  · have hs : ∃ a k, c.site = .sld a k := by
      simp only [estHi, Bool.or_eq_true, beq_iff_eq] at he
      rcases he with h | h
      · exact ⟨false, 0, h⟩
      · exact ⟨true, 1, h⟩
    obtain ⟨x, vals, hk⟩ := kT (Or.inl hs)
    rw [rec_hi_est he hk]
    exact tc_ne hpay hpc (Or.inl hs) hk
  · rcases rec_hi c ev b with h | ⟨x, vals, sh, hk, h2, hs2⟩
    · rw [h]; exact hold (hn.resolve_right he)
    · rw [h2]
      refine tc_ne hpay hpc (Or.inl ?_) hk
      rcases hs2 with h | h
      · exact ⟨false, 0, h⟩
      · exact ⟨true, 1, h⟩

theorem fld_o (kT : ((∃ a k, c.site = .sld a k) ∨ (∃ k, c.site = .rld k) ∨ ∃ k, c.site = .old k) →
      ∃ x vals, ev.kind = .tc (.ld x vals .s32x32b))
    (hold : hasO c.site = true → b.o ≠ []) (hn : hasO c.site = true ∨ estO c.site = true) :
    (record c ev b).o ≠ [] := by
  by_cases he : estO c.site = true
  · have hs : (∃ k, c.site = .rld k) ∨ ∃ k, c.site = .old k := by
      revert he
      cases h : c.site <;> simp [estO]
    obtain ⟨x, vals, hk⟩ := kT (Or.inr hs)
    rw [rec_o_est he hk]
    exact tc_ne hpay hpc (Or.inr hs) hk
  · rcases rec_o c ev b with h | ⟨x, vals, sh, hk, h2, hs2⟩
    · rw [h]; exact hold (hn.resolve_right he)
    · rw [h2]
      exact tc_ne hpay hpc (Or.inr hs2) hk

theorem fld_mw (kR : (c.site = .vm ∨ (∃ k, c.site = .pld k) ∨ c.site = .mld ∨ c.site = .eld) →
      ∃ x bs, ev.kind = .rd x bs)
    (hold : hasMw c.site = true → b.mw ≠ .pred false)
    (hn : hasMw c.site = true ∨ c.site = .vm) : (record c ev b).mw ≠ .pred false := by
  by_cases he : c.site = .vm
  · obtain ⟨x, bs, hk⟩ := kR (Or.inl he)
    rw [rec_mw_est he hk]
    exact rd_ne hpay hpc hk (Or.inl he)
  · rcases rec_mw c ev b with h | ⟨x, bs, hk, h2, hs2⟩
    · rw [h]; exact hold (hn.resolve_right he)
    · exact absurd hs2 he

theorem fld_pm (kR : (c.site = .vm ∨ (∃ k, c.site = .pld k) ∨ c.site = .mld ∨ c.site = .eld) →
      ∃ x bs, ev.kind = .rd x bs)
    (hold : hasPm c.site = true → b.pm ≠ .pred false)
    (hn : hasPm c.site = true ∨ c.site = .mld) : (record c ev b).pm ≠ .pred false := by
  by_cases he : c.site = .mld
  · obtain ⟨x, bs, hk⟩ := kR (Or.inr (Or.inr (Or.inl he)))
    rw [rec_pm_est he hk]
    exact rd_ne hpay hpc hk (Or.inr (Or.inr (Or.inl he)))
  · rcases rec_pm c ev b with h | ⟨x, bs, hk, h2, hs2⟩
    · rw [h]; exact hold (hn.resolve_right he)
    · exact absurd hs2 he

theorem fld_pe (kR : (c.site = .vm ∨ (∃ k, c.site = .pld k) ∨ c.site = .mld ∨ c.site = .eld) →
      ∃ x bs, ev.kind = .rd x bs)
    (hold : hasPe c.site = true → b.pe ≠ .pred false)
    (hn : hasPe c.site = true ∨ c.site = .eld) : (record c ev b).pe ≠ .pred false := by
  by_cases he : c.site = .eld
  · obtain ⟨x, bs, hk⟩ := kR (Or.inr (Or.inr (Or.inr he)))
    rw [rec_pe_est he hk]
    exact rd_ne hpay hpc hk (Or.inr (Or.inr (Or.inr he)))
  · rcases rec_pe c ev b with h | ⟨x, bs, hk, h2, hs2⟩
    · rw [h]; exact hold (hn.resolve_right he)
    · exact absurd hs2 he

theorem fld_pw {j : Nat}
    (kR : (c.site = .vm ∨ (∃ k, c.site = .pld k) ∨ c.site = .mld ∨ c.site = .eld) →
      ∃ x bs, ev.kind = .rd x bs)
    (hold : hasPw j c.site = true → b.pw j ≠ (.pred false, .pred false))
    (hn : hasPw j c.site = true ∨ estPw j c.site c.el = true) :
    (record c ev b).pw j ≠ (.pred false, .pred false) := by
  by_cases he : estPw j c.site c.el = true
  · have hs : ∃ k, c.site = .pld k := by
      revert he
      cases h : c.site <;> simp [estPw]
    obtain ⟨x, bs, hk⟩ := kR (Or.inr (Or.inl hs))
    rw [rec_pw_est he hk]
    intro h0
    exact rd_ne hpay hpc hk (Or.inr (Or.inl hs)) (Prod.mk.inj h0).2
  · rcases rec_pw c ev b j with h | ⟨k, x, bs, hk, hs2, hel, hkj, h2⟩
    · rw [h]; exact hold (hn.resolve_right he)
    · rw [h2]
      intro h0
      exact rd_ne hpay hpc hk (Or.inr (Or.inl ⟨k, hs2⟩)) (Prod.mk.inj h0).2

end fields

/-- **A step keeps the loaded words**: the event is at the state's site, of its kind, and its word
is typed. -/
theorem ldOk_step {sc : ℝ} {l : List Event} {d : D} {c' : Control.D} {ev : Event}
    (h : LdOk d) (hsucc : Control.succ P L g w d.c ev = some (some c'))
    (hOk' : OkInv (dataNext L d c' ev)) (hpc : ev.pc = d.c.site.pc)
    (kT : ((∃ a k, d.c.site = .sld a k) ∨ (∃ k, d.c.site = .rld k) ∨ ∃ k, d.c.site = .old k) →
      ∃ x vals, ev.kind = .tc (.ld x vals .s32x32b))
    (kR : (d.c.site = .vm ∨ (∃ k, d.c.site = .pld k) ∨ d.c.site = .mld ∨ d.c.site = .eld) →
      ∃ x bs, ev.kind = .rd x bs) (hpay : W0EvPayload sc l ev) :
    LdOk (dataNext L d c' ev) := by
  obtain ⟨hlo, hhi, hmw, hpw, hpm, hO, hpe⟩ := h
  by_cases hs : d.c.site = .arrS
  · obtain hb | hb := Control.succ_arrS hsucc hs
    all_goals
      have e1 : (dataNext L d c' ev).c.site = c'.site := by rw [dataNext_c]
      simp only [LdOk, e1, hb]
      refine ⟨fun hh => ?_, fun hh => ?_, fun hh => ?_, fun j hj hh => ?_, fun hh => ?_,
        fun hh => ?_, fun hh => ?_⟩
      all_goals first
        | (simp [hasLo, hasHi, hasMw, hasPm, hasO, hasPe, accPcs, Site.pc] at hh)
        | exact absurd hh (by simpa using (hasPw_start j (List.mem_range.mpr hj)).1)
        | exact absurd hh (by simpa using (hasPw_start j (List.mem_range.mpr hj)).2)
  have e1 : (dataNext L d c' ev).c.site = c'.site := by rw [dataNext_c]
  have e2 : (dataNext L d c' ev).b = record d.c ev d.b := by rw [dataNext_eq hs]
  have hsOk : (hasLo c'.site || hasHi c'.site || hasMw c'.site || hasPm c'.site || hasO c'.site ||
      hasPe c'.site || (List.range 8).any (fun j => hasPw j c'.site)) = true →
      succOk d.c c' = true := fun hA => by
    have hok := hOk' (by rw [e1]; exact has_inner _ (Wg0.mem_allSites _) hA)
    rw [dataNext_eq hs] at hok
    exact (Bool.and_eq_true_iff.mp hok).2
  simp only [LdOk, e1, e2]
  have hchk : ∀ (hA : (hasLo c'.site || hasHi c'.site || hasMw c'.site || hasPm c'.site ||
      hasO c'.site || hasPe c'.site || (List.range 8).any (fun j => hasPw j c'.site)) = true),
      ldChk d.c.site c'.site (if d.c.el = 0 then 0 else if d.c.el + 1 < 4 then 1 else 4) = true :=
    fun hA => ld_chk (hsOk hA)
  refine ⟨fun hh => ?_, fun hh => ?_, fun hh => ?_, fun j hj hh => ?_, fun hh => ?_,
    fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨c1, -⟩ := ldChk_fields (hchk (by simp [hh]))
    exact fld_lo hpay hpc kT hlo (c1 hh)
  · obtain ⟨-, c1, -⟩ := ldChk_fields (hchk (by simp [hh]))
    exact fld_hi hpay hpc kT hhi (c1 hh)
  · obtain ⟨-, -, c1, -⟩ := ldChk_fields (hchk (by simp [hh]))
    exact fld_mw hpay hpc kR hmw (c1 hh)
  · obtain ⟨-, -, -, c1, -⟩ := ldChk_fields (hchk (by
      simp only [Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨j, List.mem_range.mpr hj, hh⟩))
    exact fld_pw hpay hpc kR (hpw j hj) (Or.imp_right estPw_norm (c1 j (List.mem_range.mpr hj) hh))
  · obtain ⟨-, -, -, -, c1, -⟩ := ldChk_fields (hchk (by simp [hh]))
    exact fld_pm hpay hpc kR hpm (c1 hh)
  · obtain ⟨-, -, -, -, -, c1, -⟩ := ldChk_fields (hchk (by simp [hh]))
    exact fld_o hpay hpc kT hO (c1 hh)
  · obtain ⟨-, -, -, -, -, -, c1⟩ := ldChk_fields (hchk (by simp [hh]))
    exact fld_pe hpay hpc kR hpe (c1 hh)

end
end Wg0.Data
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
