-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LkSm
public import Kernels.InklingRelDecode.Proof.Thread.SmBridge
public import Lemmas.Flow.FmaTotal
public import Kernels.InklingRelDecode.Proof.Thread.SmTotH

@[expose] public section

/-!
# The words of the softmax state are `.f32` data

The edge into the P store (`Sm.toBar20`: pcs 949 and 950) faults when the new running maximum is
not a word of four bytes or the update `fma.rn.f32 l, l, alpha, rs` has no outcome. `NumInv` is the
invariant that rules both out: the running maximum is a four-byte word, the running sum, `alpha`
and the row sum are `.f32` data (`F32Dat`: numbers, zeros, infinities or NaNs), and the stage's
maximum is a four-byte word. `fma.rn.f32` has an outcome on any three data, the Core rule where the
ideal rule declines (`floatE_fma_dat`), and the outcome is a datum, as is every outcome of the row
sum's `add.f32` (`floatE_add_dat`), whatever word the exchange returned. So `NumInv` holds at the
first state and is kept by every step of the region (`numInv_next`) with no fact of another lane,
and the edge never faults (`updOk_of`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Lk

noncomputable section
set_option maxRecDepth 100000

/-- **The words of a softmax state.** -/
structure NumInv (d : D) : Prop where
  m : d.m.bytes = 4
  l : F32Dat d.l
  al : F32Dat d.stg.al
  rs : F32Dat d.stg.rs
  mn : d.stg.mn.bytes = 4
  /-- The conversions of the P store's packed pairs have outcomes. -/
  pq : d.pqOk

theorem NumInv.of_eq {d d' : D} (h : NumInv d) (hm : d'.m = d.m) (hl : d'.l = d.l)
    (ha : d'.stg.al = d.stg.al) (hr : d'.stg.rs = d.stg.rs) (hn : d'.stg.mn = d.stg.mn)
    (hp : d'.stg.pv = d.stg.pv := by rfl) :
    NumInv d' :=
  ⟨hm ▸ h.m, hl ▸ h.l, ha ▸ h.al, hr ▸ h.rs, hn ▸ h.mn, by
    simpa only [D.pqOk, D.pwE, hp] using h.pq⟩

theorem valFloat_b32_one : ∃ x, valFloat .f32 (b32 1065353216) = .ok x :=
  ⟨_, valFloat_b32 (by decide) (show f32Value 1065353216 = some 1 by decide +kernel)⟩

theorem numInv_init (e : Ent) : NumInv (SmEntry.d0 e) where
  m := rfl
  l := f32Dat_bits _
  al := f32Dat_bits _
  rs := f32Dat_bits _
  mn := rfl
  pq := pqOk_float (f := fun _ => 0) (fun _ => rfl)

theorem mNew_bytes {d : D} (h : NumInv d) : d.mNew.bytes = 4 := by
  unfold D.mNew
  split
  · exact h.m
  · exact h.mn

/-- **The edge into the P store does not fault** at a state with the words. -/
theorem updOk_of {d : D} (h : NumInv d) : d.updOk = true := by
  obtain ⟨v, hv, -⟩ := floatE_fma_dat h.l h.al h.rs
  have hl : d.lOut = .ok v := hv
  simp [D.updOk, mNew_bytes h, hl, Except.toBool, h.pq]

theorem numInv_upd {d : D} (h : NumInv d) : NumInv d.upd := by
  obtain ⟨v, hv, hd⟩ := floatE_fma_dat h.l h.al h.rs
  have hl : d.lOut = .ok v := hv
  refine ⟨mNew_bytes h, ?_, h.al, h.rs, h.mn, h.pq⟩
  show F32Dat (okVal (b32 0) d.lOut)
  rw [okVal_of_ok hl]
  exact hd

theorem numInv_toBar20 {d d' : D} (h : NumInv d) (hn : toBar20 d = some (some d')) : NumInv d' := by
  unfold toBar20 at hn
  split at hn
  · simp only [Option.some.injEq] at hn
    subst hn
    exact (numInv_upd h).of_eq rfl rfl rfl rfl rfl
  · cases hn

theorem numInv_afterSetup {L : Launch} {g : Nat} {d d' : D} (h : NumInv d)
    (hn : Sm.afterSetup L g d = some (some d')) : NumInv d' := by
  unfold Sm.afterSetup at hn
  split at hn
  · cases hn
  · split at hn <;>
      (simp only [Option.some.injEq] at hn; subst hn; exact h.of_eq rfl rfl rfl rfl rfl)

theorem f32Dat_alV (d : D) (rE : EReal) : F32Dat (d.alV rE) := by
  unfold D.alV
  split
  · exact f32Dat_bits _
  · exact f32Dat_float _

/-- The row sum after the exchange is an `.f32` datum, whatever word was received. -/
theorem rsOut_dat {d : D} {recv v : Value} (h : d.rsOut recv = .ok v) : F32Dat v :=
  floatE_add_dat h

theorem numInv_afterSum {d : D} {recv v : Value} (h : NumInv d) (hv : d.rsOut recv = .ok v) :
    NumInv (d.afterSum v) :=
  ⟨h.m, h.l, h.al, rsOut_dat hv, h.mn, h.pq⟩

/-- **The successors of the softmax region keep the words** after the exchange of the row
maximum on any words. -/
theorem numInv_afterMaxT {L : Launch} {g : Nat} {d : D} {recv : Value} (h : NumInv d)
    (hok : d.s2Ok L g recv) : NumInv (d.afterMaxT L g recv) :=
  ⟨h.m, h.l, f32Dat_alT d recv, h.rs, mnT_bytes d recv, pqOk_afterMaxT hok⟩

/-- **Every step of the softmax region keeps the words.** -/
theorem numInv_next {L : Launch} {g : Nat} {d d' : D} {e : Event} (h : NumInv d)
    (hn : Sm.next L g d e = some (some d')) : NumInv d' := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; exact h.of_eq rfl rfl rfl rfl rfl)
    | (refine numInv_afterSetup ?_ hn; exact h.of_eq rfl rfl rfl rfl rfl)
    | exact numInv_toBar20 h hn
    | (simp only [Option.some.injEq] at hn; subst hn
       exact ⟨h.m, h.l, f32Dat_alV _ _, h.rs, erealValue_f32_bytes _,
         pqOk_float (fun _ => rfl)⟩)
    | (simp only [Option.some.injEq] at hn; subst hn
       exact numInv_afterMaxT h (by assumption))
    | (simp only [Option.some.injEq] at hn; subst hn
       exact numInv_afterSum h (by assumption))
    | exact numInv_toBar20 (numInv_afterSum h (by assumption)) hn

/-! ### The flag of the real numbers -/

theorem re_toBar20 {d d' : D} (hn : toBar20 d = some (some d')) : d'.stg.re = d.stg.re := by
  unfold toBar20 at hn
  split at hn
  · simp only [Option.some.injEq] at hn
    subst hn
    rfl
  · cases hn

theorem re_afterSetup {L : Launch} {g : Nat} {d d' : D}
    (hn : Sm.afterSetup L g d = some (some d')) : d'.stg.re = d.stg.re := by
  unfold Sm.afterSetup at hn
  split at hn
  · cases hn
  · split at hn <;> (simp only [Option.some.injEq] at hn; subst hn; rfl)

/-- **A step keeps the flag of the real numbers** unless it is the exchange of the row maximum
on words that are not score words (`D.afterMaxT` clears it). -/
theorem re_next {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : Sm.next L g d e = some (some d'))
    (hR : d.site = .shfl5 → ∀ m av bv cv r o, e.kind = .shfl m av bv cv r o → d.RealIn r) :
    d'.stg.re = d.stg.re := by
  by_cases h5 : d.site = .shfl5
  · simp only [Sm.next, h5] at hn
    split at hn
    · rename_i m av bv cv r o hk
      simp only [hR h5 _ _ _ _ _ _ hk, ↓reduceIte, Option.some.injEq] at hn
      subst hn
      rfl
    · cases hn
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; rfl)
    | exact (re_afterSetup hn).trans rfl
    | exact (re_toBar20 hn).trans rfl
    | (exfalso; simp_all)

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
