-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.WinLane

@[expose] public section

/-! # A window that only keeps registers

The window `S` need not be closed under the local steps: states that leave it never come back
(`enterOk S 0`), and a step from a position of `S` writes none of `R` (`keepOk`). A state in the
window is then reached from the last event with the registers `R` unchanged. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow

variable {L : Launch} {g : Nat}

/-- **The keeping scan**: a local instruction at a position of `S` writes none of `R`. -/
def keepOk (S : List (Nat × Nat)) (R : List Nat) : Bool :=
  scanCode (fun pc ins => !inS S pc || (!ins.op.isLocal ||
    (R.all (fun r => !(writesRegs ins.op).contains r) && !Assumptions.emuSites.contains pc)))
    kernel.code 0

theorem keep_step {S R} (hw : keepOk S R = true) {u u1 : TState}
    (ht : Tau kernel Assumptions.all L g u u1) (h : inS S u.pc = true) :
    ∀ r ∈ R, u1.regs r = u.regs r := by
  obtain ⟨ins, hc, -, hk⟩ := win_cases ht
  have := scanCode_get hw hc
  rw [Nat.zero_add] at this
  simp only [h, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, List.all_eq_true] at this
  rcases hk with ⟨-, -, hr⟩ | ⟨hl', -, hr⟩
  · exact fun r _ => hr r
  · rcases this with hl | ⟨hR, hemu⟩
    · simp [hl'] at hl
    · exact fun r hrR => hr r (by simpa using hR r hrR) fun hq =>
        absurd (List.contains_iff_mem.mp hq) (by simpa using hemu)

/-- **A state in the window comes from a state in the window with the registers `R`.** -/
theorem win_start_keep {S R} (hf : keepOk S R = true) (hb : enterOk S 0 = true)
    (h0 : inS S 0 = false) {u v : TState}
    (h : Relation.ReflTransGen (Tau kernel Assumptions.all L g) u v)
    (hv : inS S v.pc = true) : inS S u.pc = true ∧ ∀ r ∈ R, v.regs r = u.regs r := by
  induction h with
  | refl => exact ⟨hv, fun _ _ => rfl⟩
  | tail hab hbc ih =>
    rename_i b c
    have hb' : inS S b.pc = true := by
      by_contra hn
      have := win_back hb hbc hv (by simpa using hn)
      rw [this, h0] at hv
      cases hv
    obtain ⟨hu, hk⟩ := ih hb'
    exact ⟨hu, fun r hr => (keep_step hf hbc hb' r hr).trans (hk r hr)⟩

/-- **The last event before a state in a keeping window** (`lane_set` for `keepOk`). -/
theorem lane_set_keep {S R} (hf : keepOk S R = true) (hb : enterOk S 0 = true)
    (h0 : inS S 0 = false) {X : Execution}
    {t : TState} (hl : Iface.LaneState L X g t) (ht : inS S t.pc = true) :
    ∃ k e t0, (X.tr g)[k]? = some e ∧ Run kernel Assumptions.all L g {} ((X.tr g).take (k + 1))
      (some t0) ∧ (∃ s, EStep kernel Assumptions.all L g s e (some t0)) ∧
      e.pc ∈ entryEvents S ∧ inS S t0.pc = true ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t ∧
      ∀ r ∈ R, t.regs r = t0.regs r :=
  lane_set_gen (fun h hv => win_start_keep hf hb h0 h hv) h0 hl ht

end PTX.Kernels.InklingRelDecode.Proof.Lib
