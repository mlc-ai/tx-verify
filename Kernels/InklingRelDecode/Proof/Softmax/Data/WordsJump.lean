-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsOk
public import Lemmas.Flow.PhaseTableItem
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The moves of the bias words as jumps of the table

Each position of `wSpec` is one instruction, an item of a run: its step gives the table's facts
of the next position (`jump_item`), from the Boolean checks `wOk` and the values of `wV1`/`wV2`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {L : Launch} {g : Nat}

theorem wV1_pre (ws : Nat → Value) {i : Nat} (h : i < 64) : wV1 ws (263 + i) = ws i := by
  simp only [wV1]
  split_ifs <;> first | omega | (congr 1; omega)

theorem wV1_pack (ws : Nat → Value) {m : Nat} (h : m < 32) :
    wV1 ws (1916 + m) = packV (ws (2 * m)) (ws (2 * m + 1)) := by
  simp only [wV1]
  split_ifs <;> first | omega | (congr 2 <;> omega)

theorem wV1_nxt (ws : Nat → Value) {i : Nat} (h : i < 64) : wV1 ws (nxtReg i) = ws i := by
  simp only [wV1, nxtReg]
  split_ifs <;> first | omega | (congr 1; omega)

theorem wV2_nxt (ws : Nat → Value) {i : Nat} (h : i < 64) : wV2 ws (nxtReg i) = dflt := by
  simp only [wV2, nxtReg]
  split_ifs <;> first | rfl | omega

theorem dflt_bytes : dflt.bytes = 2 := rfl

theorem wV1_199 (ws : Nat → Value) : wV1 ws 199 = dflt := by simp [wV1]

theorem wV2_333 (ws : Nat → Value) : wV2 ws 333 = dflt := by simp [wV2, wV1]

theorem wV2_of (ws : Nat → Value) {r : Nat} (h : ¬(r = 332 ∨ 334 ≤ r ∧ r < 397)) :
    wV2 ws r = wV1 ws r := by simp [wV2, h]

theorem upd_fn (V : Nat → Value) (op : Op) (d : Nat) (srcs : List Nat) (f : List Value → Exec Value)
    (r : Nat) : (XItem.fn op d srcs f).upd V r =
      if r = d then okVal (.bits 32 0) (f (srcs.map V)) else V r := by
  simp [XItem.upd, XItem.vals, Function.update]

theorem wval {k : WK} {ws : Nat → Value} {pc : Nat} {sp : WSp} (h : wSpec pc = some sp)
    (hws : 679 ≤ pc → pc < 807 → inIvs (wIvs k) pc = true → ∀ i, ws i = dflt)
    (hin : inIvs (wIvs k) pc = true) (hp : pc = 1122 ∨ wPost (pc + 1) = wPost pc)
    (hn : pc ≠ 1122 ∨ ∀ r ∈ wKeys k 1123, ¬(r = 332 ∨ 334 ≤ r ∧ r < 397)) :
    ∀ r ∈ wKeys k (pc + 1), (if wPost (pc + 1) then wV2 ws else wV1 ws) r =
      sp.item.upd (if wPost pc then wV2 ws else wV1 ws) r := by
  intro r hr
  unfold wSpec at h
  split_ifs at h with h1 h2 h3 h4 h5
  · obtain rfl := Option.some.inj h
    have e0 : wPost pc = false := by simp [wPost]; omega
    have e1 : wPost (pc + 1) = false := by simp [wPost]; omega
    simp only [e0, e1, WSp.item, upd_fn, Bool.false_eq_true, ↓reduceIte, List.map_cons,
      List.map_nil, wV1_199, mv16E, dflt_bytes]
    split_ifs with hd
    · have : r = 263 + (pc - 679) / 2 := hd
      subst this
      rw [wV1_pre ws (by omega), hws h1.1 h1.2.1 hin]
      rfl
    · rfl
  · obtain rfl := Option.some.inj h
    have e0 : wPost pc = false := by simp [wPost]; omega
    have e1 : wPost (pc + 1) = false := by simp [wPost]; omega
    simp only [e0, e1, WSp.item, upd_fn, Bool.false_eq_true, ↓reduceIte, List.map_cons,
      List.map_nil]
    split_ifs with hd
    · have : r = 1916 + (pc - 816) := hd
      subst this
      rw [wV1_pack ws (by omega), wV1_pre ws (by omega), show 264 + 2 * (pc - 816) =
        263 + (2 * (pc - 816) + 1) by omega, wV1_pre ws (by omega)]
      rfl
    · rfl
  · obtain rfl := Option.some.inj h
    have e0 : wPost pc = false := by simp [wPost]; omega
    have e1 : wPost (pc + 1) = false := by simp [wPost]; omega
    simp only [e0, e1, WSp.item, upd_fn, Bool.false_eq_true, ↓reduceIte, List.map_cons,
      List.map_nil]
    split_ifs with hd
    · have hm : 1947 - (pc - 1014) = 1916 + (31 - (pc - 1014)) := by omega
      rw [hm] at hd
      subst hd
      rw [wV1_pack ws (by omega), wV1_nxt ws (by omega), wV1_nxt ws (by omega)]
      rfl
    · rfl
  · obtain rfl := Option.some.inj h
    subst h4
    have e0 : wPost 1122 = false := by decide
    have e1 : wPost (1122 + 1) = true := by decide
    simp only [e0, e1, WSp.item, upd_fn, Bool.false_eq_true, ↓reduceIte]
    split_ifs with hd
    · subst hd
      rw [wV2_333]
      rfl
    · rcases hn with hn | hn
      · exact absurd rfl hn
      · exact wV2_of ws (hn r hr)
  · obtain rfl := Option.some.inj h
    have e0 : wPost pc = true := by simp [wPost]; omega
    have e1 : wPost (pc + 1) = true := by simp [wPost]; omega
    simp only [e0, e1, WSp.item, upd_fn, ↓reduceIte, List.map_cons, List.map_nil, wV2_333,
      mv16E, dflt_bytes]
    split_ifs with hd
    · have : r = nxtReg ((pc - 1123) / 2) := hd
      subst this
      rw [wV2_nxt ws (by omega)]
      rfl
    · rfl

theorem wItem_rule (sp : WSp) {pc : Nat} (hp : intPc pc = true) :
    ∀ s : TState, s.pc = pc → sp.item.Rule Assumptions.all L g s := by
  cases sp
  · exact rule_mv16 pc hp
  · exact rule_mi16 pc hp
  · exact rule_pack32 pc hp

/-- **The moves of a path are jumps of its table.** -/
theorem w_jump (k : WK) (ws : Nat → Value)
    (hws : ∀ pc, 679 ≤ pc → pc < 807 → inIvs (wIvs k) pc = true → ∀ i, ws i = dflt) :
    ∀ pc, wSpecB pc = true → inIvs (wIvs k) pc = true → ∀ t : TState, t.pc = pc →
      t.fault = none → TabAt (wKeys k) wPost (wV1 ws) (wV2 ws) t →
      (∃ w, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t w ∧ t ≠ w ∧
        TabGood kernel (wIvs k) (wKeys k) wPost (wV1 ws) (wV2 ws) w) ∨
        Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) t := by
  intro pc hsp hin t hpc hf hT
  obtain ⟨sp, h⟩ := Option.isSome_iff_exists.mp hsp
  obtain ⟨hc, hk⟩ := wok_of k h
  simp only [wOkC, h, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
  simp only [wOk, h, hin, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at hk
  obtain ⟨⟨hint, hcode⟩, hp⟩ := hc
  obtain ⟨⟨⟨hrd, hcov⟩, hreg⟩, hn⟩ := hk
  refine jump_item (it := sp.item) (ivs := wIvs k) ⟨⟨hcode, smSegFree hint, wItem_rule sp hint⟩,
    trivial⟩ (by cases sp <;> rfl) hrd (by cases sp <;> rfl)
    (fun r hr => by simpa using List.all_eq_true.mp hcov r hr)
    (wval h (hws pc) hin hp (by
      rcases hn with hn | hn
      · exact .inl hn
      · exact .inr (fun r hr => by
        have := List.all_eq_true.mp hn r hr
        simp at this
        omega)))
    (by simpa using hreg) hpc hf hT

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
