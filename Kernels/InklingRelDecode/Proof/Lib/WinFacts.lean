-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.WinBack

@[expose] public section

/-! # A register fact in a window that no event enters

`win_induct` for a window that events enter nowhere (no event outside the window continues inside
it): the fact is given at the states entering by a local step at `lo`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow

variable {L : Launch} {g : Nat}

/-- **The window is entered by no event.** -/
def evOut (S : List (Nat × Nat)) : Bool :=
  scanCode (fun pc ins => ins.op.isLocal || inS S pc || !inS S (pc + 1)) kernel.code 0

theorem no_event_in {S} (h : evOut S = true) {s t0 : TState} {e : Event}
    (hes : EStep kernel Assumptions.all L g s e (some t0)) (hs : inS S s.pc = false)
    (ht : inS S t0.pc = true) : False := by
  obtain ⟨ins, hc, hnl, -⟩ := EventFrame.estep_event_source hes
  have hp := post_pc hes
  have hsc := scanCode_get h hc
  rw [Nat.zero_add] at hsc
  simp only [hnl, hs, Bool.false_or, Bool.or_false, Bool.not_eq_true'] at hsc
  rcases (by omega : t0.pc = s.pc ∨ t0.pc = s.pc + 1) with e1 | e1 <;> rw [e1] at ht <;>
    simp_all

/-- **A fact of the registers `R` of a window that no event enters**, from its entry. -/
theorem win_ind {S R lo} {P : TState → Prop} {X : Execution} {preds : List Nat}
    (hf : fwdOk S R = true) (hev : evKeep S R = true) (hb : enterOk S lo = true)
    (hpr : predOk lo preds = true) (h0 : inS S 0 = false) (ho : evOut S = true)
    (hP : ∀ t t', (∀ r ∈ R, t'.regs r = t.regs r) → P t → P t')
    (hlo : ∀ c w, Iface.LaneState L X g c → Tau kernel Assumptions.all L g c w →
      c.pc ∈ preds → w.pc = lo → P w) :
    ∀ t, Iface.LaneState L X g t → inS S t.pc = true → P t :=
  win_induct hf hev hb hpr h0 hP hlo fun _ _ _ _ hes hs ht => (no_event_in ho hes hs ht).elim

/-- A local step extends a state of the lane. -/
theorem lane_tail {X : Execution} {c w : TState} (hc : Iface.LaneState L X g c)
    (ht : Tau kernel Assumptions.all L g c w) : Iface.LaneState L X g w := by
  obtain ⟨k, t0, hr, hrt⟩ := hc
  exact ⟨k, t0, hr, hrt.tail ht⟩

/-- No event continues at `P`. -/
def evLand (P : Nat) : Bool :=
  scanCode (fun pc ins => ins.op.isLocal || (pc != P && pc + 1 != P)) kernel.code 0

/-- **A state of the lane at `P`, entered by no event, follows a local step** from a state at one
of `preds`. -/
theorem tau_before {P preds} (hpr : predOk P preds = true) (hev : evLand P = true) (hP : P ≠ 0)
    {X : Execution} {w : TState} (hl : Iface.LaneState L X g w) (hw : w.pc = P) :
    ∃ c, Iface.LaneState L X g c ∧ c.pc ∈ preds ∧ Tau kernel Assumptions.all L g c w := by
  obtain ⟨k, t0, hr, hrt⟩ := hl
  obtain ⟨k0, hk0, hr0⟩ := run_norm hr
  rcases Relation.ReflTransGen.cases_tail hrt with rfl | ⟨c, hc, ht⟩
  · exfalso
    cases k0 with
    | zero =>
      rw [List.take_zero] at hr0
      cases hr0
      simp at hw
      omega
    | succ k =>
      obtain ⟨e, he'⟩ : ∃ e, (X.tr g)[k]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨u, s, hu, hus, hes⟩ := pre_idx he' hr0
      obtain ⟨ins, hci, hnl, -⟩ := EventFrame.estep_event_source hes
      have hp := post_pc hes
      have hsc := scanCode_get hev hci
      rw [Nat.zero_add] at hsc
      simp only [hnl, Bool.false_or, Bool.and_eq_true, bne_iff_ne, ne_eq] at hsc
      omega
  · exact ⟨c, ⟨k, t0, hr, hc⟩, pred_of_tau hpr ht hw, ht⟩

/-- **A guarded local step**: the guard predicate false skips the instruction, true runs it. -/
theorem tau_guard {c w : TState} (ht : Tau kernel Assumptions.all L g c w) {p : Nat} {neg : Bool}
    {op : Op} (hc : kernel.code[c.pc]? = some ⟨some (p, neg), op⟩) {b : Bool}
    (hp : c.regs p = some (.pred b)) :
    ((b != neg) = false ∧ w.pc = c.pc + 1 ∧ ∀ r, w.regs r = c.regs r) ∨
    ((b != neg) = true ∧ op.isLocal = true ∧ execLocalA Assumptions.all L g c op = .ok w) := by
  unfold Tau out at ht
  cases hf : c.fault with
  | some f => simp [hf] at ht
  | none =>
    simp only [hf, hc, guardHolds, readReg, hp, bind, Except.bind, pure, Except.pure] at ht
    cases hg : (b != neg) with
    | false =>
      simp only [hg, Out.tau.injEq] at ht
      subst ht
      exact .inl ⟨rfl, rfl, fun _ => rfl⟩
    | true =>
      simp only [hg] at ht
      by_cases hl : op.isLocal = true
      · simp only [hl, ↓reduceIte] at ht
        cases he : execLocalA Assumptions.all L g c op with
        | error e => simp [he] at ht
        | ok u =>
          simp only [he, Out.tau.injEq] at ht
          subst ht
          exact .inr ⟨rfl, hl, rfl⟩
      · simp [hl] at ht

end PTX.Kernels.InklingRelDecode.Proof.Lib
