-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Time
public import Kernels.TmlFa4Fwd.Proof.Correction.Places
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The order of a correction lane's states in its tile

A state at site `s` with `r` rescale rounds done is in a region of the tile of `R` rescale rounds
(`Reg`), and the states of a tile are ordered by `ordK`: the rounds done, then the code position. A
point at the site of an earlier state is passed once more by a later one (`passed_lt`), and a state
before a named-barrier site has an earlier time (`val_lt`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The region of a state in a tile of `R` rescale rounds. -/
def Reg (R : Nat) (s : Site) (r : Nat) : Prop :=
  (s.pc < 8006 ∧ r = 0) ∨ ((8006 ≤ s.pc ∧ s.pc ≤ 8446) ∧ r < R) ∨
    (8447 ≤ s.pc ∧ s.noTile = false ∧ r = R)

/-- The place of a state in its tile. -/
def ordK (s : Site) (r : Nat) : Nat := 16384 * r + s.pc

/-- The times a point has been passed. -/
def mult (s : Site) (r q : Nat) : Nat :=
  if 8006 ≤ q ∧ q ≤ 8446 then
    (if (8006 ≤ s.pc ∧ s.pc ≤ 8446) ∧ q < s.pc then 1 else 0) + r
  else if q < s.pc then 1 else 0

theorem pc_le (s : Site) : s.pc ≤ 9205 := by
  have h : allSites.all (fun s => decide (s.pc ≤ 9205)) = true := by decide +kernel
  simpa using List.all_eq_true.mp h s (mem_allSites s)

theorem passed_cons (q : Nat) (pts : List Nat) {s : Site} (hs : s.noTile = false) (r : Nat) :
    passed (q :: pts) s r = mult s r q + passed pts s r := by
  have hb : (if before s q = true then 1 else 0) + r * (if inRound q = true then 1 else 0) =
      mult s r q := by
    simp only [before, inRound, mult, hs, Bool.false_and, Bool.not_false, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq]
    split_ifs <;> simp_all
  rw [← hb]
  simp only [passed, List.countP_cons, Nat.mul_add]
  omega

theorem mult_le {R : Nat} {s s' : Site} {r r' : Nat} (h : Reg R s r) (h' : Reg R s' r')
    (hK : ordK s r < ordK s' r') (q : Nat) :
    mult s r q ≤ mult s' r' q ∧ (q = s.pc → mult s r q < mult s' r' q) := by
  have := pc_le s
  have := pc_le s'
  unfold ordK at hK
  unfold Reg at h h'
  unfold mult
  rcases h with h | h | h <;> rcases h' with h' | h' | h' <;>
    refine ⟨?_, ?_⟩ <;> (try rintro rfl) <;> split_ifs <;> omega

/-- **A point at an earlier state's site is passed once more by a later state.** -/
theorem passed_lt {R : Nat} {s s' : Site} {r r' : Nat} (h : Reg R s r) (h' : Reg R s' r')
    (hs : s.noTile = false) (hs' : s'.noTile = false) (hK : ordK s r < ordK s' r')
    (pts : List Nat) :
    passed pts s r + pts.countP (· = s.pc) ≤ passed pts s' r' := by
  induction pts with
  | nil => simp [passed]
  | cons q pts ih =>
    rw [passed_cons q pts hs, passed_cons q pts hs', List.countP_cons]
    obtain ⟨h1, h2⟩ := mult_le h h' hK q
    by_cases hq : q = s.pc
    · have := h2 hq
      simp only [hq, decide_true, ite_true] at this ⊢
      omega
    · simp only [hq, decide_false, Bool.false_eq_true, ite_false]
      omega

/-- The named-barrier sites with the softmax warps. -/
def Site.isNb : Site → Bool
  | .nb _ | .rbar _ | .fbar _ => true
  | _ => false

/-- **States at one place** of a named-barrier site are at one site with the same rounds done. -/
theorem ordK_eq {s s' : Site} {r r' : Nat} (hs : s'.isNb = true) (hK : ordK s r = ordK s' r') : s =
    s' ∧ r = r' := by
  have := pc_le s
  have := pc_le s'
  have hpc : s.pc = s'.pc ∧ r = r' := by
    unfold ordK at hK
    omega
  have hinj : allSites.all (fun s => (allSites.filter Site.isNb).all fun s' =>
      !decide (s.pc = s'.pc) || decide (s = s')) = true := by decide +kernel
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp hinj s (mem_allSites s)) s'
    (List.mem_filter.mpr ⟨mem_allSites s', hs⟩)
  exact ⟨by simpa [hpc.1] using h1, hpc.2⟩

/-! ### The times -/

/-- The slot (relative to the rounds done) and offset of a site of the rounds or of the final
stage. -/
def val (s : Site) : Option (Nat × Nat) :=
  match Progress.Cr.part s with
  | some (st, past) =>
    some ((ptsOf (.nb st)).countP (before s) - (if past then 1 else 0),
      Progress.bandC st.val + (Progress.Cr.tailOff s).getD (Progress.Cr.roundOff s))
  | none => none

/-- The offsets of two sites, in one round and in a round and a later one. -/
def pairOk (s s' : Site) (a b : Nat × Nat) : Bool :=
  (!decide (s.pc < s'.pc) ||
    !(decide (s.pc < 8006) || (decide (8006 ≤ s.pc) && decide (s.pc ≤ 8446) &&
      decide (8006 ≤ s'.pc) && decide (s'.pc ≤ 8446)) ||
      (decide (8447 ≤ s.pc) && decide (8447 ≤ s'.pc))) ||
    decide (4096 * a.1 + a.2 < 4096 * b.1 + b.2)) &&
  (!decide (s.pc ≤ 8446) || !decide (8006 ≤ s'.pc) ||
    decide (4096 * a.1 + a.2 < 4096 * b.1 + b.2 + 4096))

theorem pairOk_iff {s s' : Site} {a b : Nat × Nat} : pairOk s s' a b = true ↔
    (s.pc < s'.pc → (s.pc < 8006 ∨ (8006 ≤ s.pc ∧ s.pc ≤ 8446 ∧ 8006 ≤ s'.pc ∧ s'.pc ≤ 8446) ∨
      (8447 ≤ s.pc ∧ 8447 ≤ s'.pc)) → 4096 * a.1 + a.2 < 4096 * b.1 + b.2) ∧
    (s.pc ≤ 8446 → 8006 ≤ s'.pc → 4096 * a.1 + a.2 < 4096 * b.1 + b.2 + 4096) := by
  simp only [pairOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not]
  omega

private def pairChk (s s' : Site) : Bool :=
  match val s, val s' with
  | some a, some b => pairOk s s' a b
  | _, _ => true

set_option maxRecDepth 100000 in
private theorem pair_chk : allSites.all (fun s => (allSites.filter Site.isNb).all (pairChk s)) =
    true := by decide +kernel

private def slotChk (s : Site) : Bool :=
  match Progress.Cr.part s, val s with
  | some (st, past), some a => decide (a.1 ≤ 1) &&
      decide ((if past then 1 else 0) ≤ (ptsOf (.nb st)).countP (before s))
  | _, _ => true

private theorem slot_chk : allSites.all slotChk = true := by decide +kernel

private theorem ptsNb : ∀ st, (ptsOf (.nb st)).countP inRound = 1 := by decide +kernel

/-- The place of a site after `r` rounds, as a time. -/
def valT (p : Params) (r : Nat) (a : Nat × Nat) : Nat :=
  Progress.pipeBase p + 4096 * (r + a.1) + a.2

/-- The named-barrier events before a state, and its slot within the tile. -/
theorem slot_of {s : Site} {a : Nat × Nat} (ha : val s = some a) (r : Nat) :
    ∃ st past, Progress.Cr.part s = some (st, past) ∧
      a.2 = Progress.bandC st.val + (Progress.Cr.tailOff s).getD (Progress.Cr.roundOff s) ∧
      passed (ptsOf (.nb st)) s r - (if past then 1 else 0) = r + a.1 ∧ a.1 ≤ 1 := by
  have h1 := List.all_eq_true.mp slot_chk s (mem_allSites s)
  unfold val at ha
  split at ha
  · rename_i st past hpt
    cases ha
    simp only [slotChk, val, hpt, Bool.and_eq_true, decide_eq_true_eq] at h1
    refine ⟨st, past, hpt, rfl, ?_, h1.1⟩
    simp only [passed, ptsNb st]
    omega
  · cases ha

/-- The arithmetic of an earlier place: the offsets of one round, and of a round and the next. -/
theorem val_lt_of {R : Nat} {s s' : Site} {r r' : Nat} {a b : Nat × Nat}
    (h1 : s.pc < s'.pc → (s.pc < 8006 ∨ (8006 ≤ s.pc ∧ s.pc ≤ 8446 ∧ 8006 ≤ s'.pc ∧ s'.pc ≤ 8446) ∨
      (8447 ≤ s.pc ∧ 8447 ≤ s'.pc)) → 4096 * a.1 + a.2 < 4096 * b.1 + b.2)
    (h2 : s.pc ≤ 8446 → 8006 ≤ s'.pc → 4096 * a.1 + a.2 < 4096 * b.1 + b.2 + 4096)
    (h : Reg R s r) (h' : Reg R s' r') (hK : ordK s r < ordK s' r') (p : Params) :
    valT p r a < valT p r' b := by
  have := pc_le s
  have := pc_le s'
  unfold valT
  unfold ordK at hK
  unfold Reg at h h'
  rcases Nat.lt_trichotomy r r' with hu | hu | hu
  · have h5 := h2 (by omega) (by omega)
    omega
  · have h5 := h1 (by omega) (by omega)
    omega
  · omega

/-- **An earlier place than a named-barrier site's has an earlier time.** -/
theorem val_lt {R : Nat} {s s' : Site} {r r' : Nat} {a b : Nat × Nat} (ha : val s = some a)
    (hb : val s' = some b) (hs' : s'.isNb = true) (h : Reg R s r) (h' : Reg R s' r')
    (hK : ordK s r < ordK s' r') (p : Params) : valT p r a < valT p r' b := by
  have h2 := List.all_eq_true.mp (List.all_eq_true.mp pair_chk s (mem_allSites s)) s'
    (List.mem_filter.mpr ⟨mem_allSites s', hs'⟩)
  simp only [pairChk, ha, hb] at h2
  exact val_lt_of (pairOk_iff.mp h2).1 (pairOk_iff.mp h2).2 h h' hK p

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
