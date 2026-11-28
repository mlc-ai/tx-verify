-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.WinLane

@[expose] public section

/-! # A fact about the registers `R` of a window, carried along the lane

The window `S` is left by no local step (`fwdOk S R`: it keeps `R`) and entered by local steps
only at `lo`. A predicate `P` of the registers `R` that holds at the states entering it (at `lo`
by local steps, after an event from outside) holds at every state of the lane in the window: the
events inside the window write none of `R` (`evKeep`). The induction is on the length of the
trace prefix the state follows. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow

variable {L : Launch} {g : Nat}

/-- The local steps from `u` to `v`: the path of a lane between two events. -/
abbrev TauPath (L : Launch) (g : Nat) (u v : TState) : Prop :=
  Relation.ReflTransGen (Tau kernel Assumptions.all L g) u v

/-- **The events scan**: an event at a position of `S` writes none of `R`. -/
def evKeep (S : List (Nat × Nat)) (R : List Nat) : Bool :=
  scanCode (fun pc ins => !inS S pc || ins.op.isLocal ||
    R.all (fun r => !(EventFrame.eventWrites ins.op).contains r)) kernel.code 0

/-- The state before the last event of a run, with the prefix it follows. -/
theorem pre_idx {X : Execution} {k : Nat} {e : Event} {t : TState}
    (hk : (X.tr g)[k]? = some e)
    (hr : Run kernel Assumptions.all L g {} ((X.tr g).take (k + 1)) (some t)) :
    ∃ u s, Run kernel Assumptions.all L g {} ((X.tr g).take k) (some u) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) u s ∧
      EStep kernel Assumptions.all L g s e (some t) := by
  rw [List.take_add_one, hk, Option.toList_some] at hr
  obtain ⟨u, s, hu, hus, hes⟩ := Run.unsnoc _ e hr
  exact ⟨u, s, hu, hus, hes⟩

/-- **The predecessor scan**: every instruction that a local step of can land at `lo` (by its
branch, its fall-through or a skipped guard) is at a position of `preds`. -/
def predOk (lo : Nat) (preds : List Nat) : Bool :=
  scanCode (fun pc ins => !((ins.guard.isSome && pc + 1 == lo) ||
    (ins.op.isLocal && (succs pc ins.op).contains lo)) || preds.contains pc) kernel.code 0

theorem pred_of_tau {lo preds} (h : predOk lo preds = true) {c w : TState}
    (ht : Tau kernel Assumptions.all L g c w) (hw : w.pc = lo) : c.pc ∈ preds := by
  obtain ⟨ins, hc, -, hk⟩ := win_cases ht
  have := scanCode_get h hc
  rw [Nat.zero_add] at this
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with hn | hm
  · exfalso
    rcases hk with ⟨hs, hp, -⟩ | ⟨hl, hp, -⟩
    · have key : (ins.guard.isSome && c.pc + 1 == lo || ins.op.isLocal &&
          (succs c.pc ins.op).contains lo) = true := by simp [hs]; omega
      rw [key] at hn
      cases hn
    · have key : (ins.guard.isSome && c.pc + 1 == lo || ins.op.isLocal &&
          (succs c.pc ins.op).contains lo) = true := by
        simp [hl]
        exact .inr (hw ▸ hp)
      rw [key] at hn
      cases hn
  · exact List.contains_iff_mem.mp hm

theorem pred_tail {S} {u w : TState}
    (h : Relation.ReflTransGen (Tau kernel Assumptions.all L g) u w) (hu : inS S u.pc = false)
    (hw : inS S w.pc = true) : ∃ c, Relation.ReflTransGen (Tau kernel Assumptions.all L g) u c ∧
      Tau kernel Assumptions.all L g c w := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨c, hc, ht⟩
  · rw [hu] at hw
    cases hw
  · exact ⟨c, hc, ht⟩

theorem win_induct {S R lo} {P : TState → Prop} {X : Execution}
    {preds : List Nat} (hf : fwdOk S R = true) (hev : evKeep S R = true)
    (hb : enterOk S lo = true) (hpr : predOk lo preds = true)
    (h0 : inS S 0 = false) (hP : ∀ t t', (∀ r ∈ R, t'.regs r = t.regs r) → P t → P t')
    (hlo : ∀ c w, Iface.LaneState L X g c → Tau kernel Assumptions.all L g c w → c.pc ∈ preds →
      w.pc = lo → P w)
    (hin : ∀ s e t0, Iface.LaneState L X g s → EStep kernel Assumptions.all L g s e (some t0) →
      inS S s.pc = false → inS S t0.pc = true → P t0) :
    ∀ t, Iface.LaneState L X g t → inS S t.pc = true → P t := by
  have key : ∀ k t0 t, Run kernel Assumptions.all L g {} ((X.tr g).take k) (some t0) →
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t → inS S t.pc = true → P t := by
    intro k
    induction k with
    | zero =>
      intro t0 t hr hrt ht
      rw [List.take_zero] at hr
      cases hr
      by_cases h : inS S 0 = true
      · simp [h0] at h
      · obtain ⟨w, h1, h2, hw, hwS⟩ := first_entry hb hrt (by simpa using h) ht
        refine hP w t (fun r hr => (win_keep hf h2 hwS |>.2 r hr)) ?_
        obtain ⟨c, hc1, hc2⟩ := pred_tail h1 (by simpa using h) hwS
        exact hlo c w ⟨0, _, by simp [Run.nil], hc1⟩ hc2 (pred_of_tau hpr hc2 hw) hw
    | succ k ih =>
      intro t0 t hr hrt ht
      by_cases hk : k < (X.tr g).length
      swap
      · refine ih t0 t ?_ hrt ht
        rw [List.take_of_length_le (by omega)] at hr ⊢
        exact hr
      by_cases h : inS S t0.pc = true
      · obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
        obtain ⟨u, s, hu, hus, hes⟩ := pre_idx he hr
        have hs : Iface.LaneState L X g s := ⟨k, u, hu, hus⟩
        obtain ⟨-, hkeep⟩ := win_keep hf hrt h
        refine hP t0 t (fun r hr' => hkeep r hr') ?_
        by_cases hsS : inS S s.pc = true
        · have hPs := ih u s hu hus hsS
          obtain ⟨ins, hc, hnl, -⟩ := EventFrame.estep_event_source hes
          refine hP s t0 (fun r hr' => estep_keeps hes ins hc r ?_) hPs
          have := scanCode_get hev hc
          rw [Nat.zero_add] at this
          simp only [hsS, Bool.not_true, hnl, Bool.false_or, Bool.or_false,
            List.all_eq_true, Bool.not_eq_true'] at this
          simpa using this r hr'
        · exact hin s e t0 hs hes (by simpa using hsS) h
      · obtain ⟨w, h1, h2, hw, hwS⟩ := first_entry hb hrt (by simpa using h) ht
        refine hP w t (fun r hr => (win_keep hf h2 hwS |>.2 r hr)) ?_
        obtain ⟨c, hc1, hc2⟩ := pred_tail h1 (by simpa using h) hwS
        exact hlo c w ⟨k + 1, t0, hr, hc1⟩ hc2 (pred_of_tau hpr hc2 hw) hw
  intro t ⟨k, t0, hr, hrt⟩ ht
  exact key k t0 t hr hrt ht

end PTX.Kernels.InklingRelDecode.Proof.Lib
