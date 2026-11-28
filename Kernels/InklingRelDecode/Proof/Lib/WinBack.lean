-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.WinInduct

@[expose] public section

/-! # A state in a window without events comes from the window's entry

In a window `S` that holds no event, a state of the lane at a position of `S` follows by local steps
a state at the entry `lo`, a state of the lane too. Local steps from the epilogue's positions from
2567 on only go forward, so two states of the same position that follow each other are one. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow

variable {L : Launch} {g : Nat}

/-- **The window holds no event.** -/
def noEv (S : List (Nat × Nat)) : Bool :=
  scanCode (fun pc ins => !inS S pc || ins.op.isLocal) kernel.code 0

/-- **The event entry scan**: an event just before `S` continues at `lo`. -/
def evEnterOk (S : List (Nat × Nat)) (lo : Nat) : Bool :=
  scanCode (fun pc ins => ins.op.isLocal || inS S pc || !inS S (pc + 1) || pc + 1 == lo)
    kernel.code 0

/-- A run of a prefix, as one of at most the whole trace. -/
theorem run_norm {X : Execution} {k : Nat} {t0 : TState}
    (hr : Run kernel Assumptions.all L g {} ((X.tr g).take k) (some t0)) :
    ∃ k0 ≤ (X.tr g).length, Run kernel Assumptions.all L g {} ((X.tr g).take k0) (some t0) := by
  by_cases h : k ≤ (X.tr g).length
  · exact ⟨k, h, hr⟩
  · refine ⟨_, le_rfl, ?_⟩
    rw [List.take_length]
    rwa [List.take_of_length_le (by omega)] at hr

theorem back_entry {S lo} (hn : noEv S = true) (hb : enterOk S lo = true)
    (he : evEnterOk S lo = true) (h0 : inS S 0 = false) {X : Execution} {c : TState}
    (hl : Iface.LaneState L X g c) (hc : inS S c.pc = true) :
    ∃ w, Iface.LaneState L X g w ∧ w.pc = lo ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) w c := by
  obtain ⟨k, t0, hr, hrt⟩ := hl
  obtain ⟨k0, hk0, hr0⟩ := run_norm hr
  by_cases h : inS S t0.pc = true
  · refine ⟨t0, ⟨k0, t0, hr0, .refl⟩, ?_, hrt⟩
    cases k0 with
    | zero =>
      rw [List.take_zero] at hr0
      cases hr0
      simp [h0] at h
    | succ k =>
      obtain ⟨e, he'⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨u, s, hu, hus, hes⟩ := pre_idx he' hr0
      obtain ⟨ins, hci, hnl, -⟩ := EventFrame.estep_event_source hes
      have hp := post_pc hes
      have hsp := EventFrame.estep_source_pc hes
      have hscan := scanCode_get he hci
      have hnn := scanCode_get hn hci
      rw [Nat.zero_add] at hscan hnn
      have hs : inS S s.pc = false := by
        by_contra hs
        have h3 : inS S s.pc = true := by simpa using hs
        simp [h3, hnl] at hnn
      simp only [hnl, hs, Bool.false_or, Bool.or_false, Bool.or_eq_true, Bool.not_eq_true',
        beq_iff_eq] at hscan
      rcases hscan with h1 | h1
      · exfalso
        rcases (by omega : t0.pc = s.pc ∨ t0.pc = s.pc + 1) with h2 | h2 <;> rw [h2] at h <;>
          simp_all
      · rcases (by omega : t0.pc = s.pc ∨ t0.pc = s.pc + 1) with h2 | h2
        · rw [h2] at h
          simp_all
        · omega
  · obtain ⟨w, h1, h2, hw, -⟩ := first_entry hb hrt (by simpa using h) hc
    exact ⟨w, ⟨k0, t0, hr0, h1⟩, hw, h2⟩

/-- **The forward scan**: from `lo` on every local step lands at a larger position. -/
def fwdAll (lo : Nat) : Bool :=
  scanCode (fun pc ins => decide (pc < lo) || !ins.op.isLocal ||
    (succs pc ins.op).all (fun q => decide (pc < q))) kernel.code 0

theorem tau_forward {lo} (h : fwdAll lo = true) {u v : TState} (hu : lo ≤ u.pc)
    (p : Relation.ReflTransGen (Tau kernel Assumptions.all L g) u v) : u = v ∨ u.pc < v.pc := by
  induction p using Relation.ReflTransGen.head_induction_on with
  | refl => exact .inl rfl
  | @head a b ht _ ih =>
    obtain ⟨ins, hc, -, hk⟩ := win_cases ht
    have hsc := scanCode_get h hc
    rw [Nat.zero_add] at hsc
    have hab : a.pc < b.pc := by
      rcases hk with ⟨-, hp, -⟩ | ⟨hl, hp, -⟩
      · omega
      · simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true] at hsc
        rcases hsc with (hlt | hn) | hall
        · omega
        · simp [hl] at hn
        · simpa using hall _ hp
    rcases ih (by omega) with rfl | h2
    · exact .inr hab
    · exact .inr (by omega)

theorem tau_same {lo} (h : fwdAll lo = true) {u v : TState} (hu : lo ≤ u.pc)
    (p : Relation.ReflTransGen (Tau kernel Assumptions.all L g) u v) (hpc : v.pc = u.pc) :
    u = v := by
  rcases tau_forward h hu p with h1 | h1
  · exact h1
  · omega

end PTX.Kernels.InklingRelDecode.Proof.Lib
