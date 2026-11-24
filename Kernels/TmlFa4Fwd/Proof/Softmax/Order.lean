-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Time
public import Kernels.TmlFa4Fwd.Proof.Softmax.Places
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The order of a softmax lane's states in its tile

A state at site `s` with `rb` biased and `rp` plain rounds done is in a region of the tile of `B`
biased and `P` plain rounds after the first (`Reg`), and the states of a tile are ordered by
`ordK`: the rounds done, then the code position. A point at the site of an earlier state is passed
once more by a later one (`passed_lt`), and an earlier state of the rounds has an earlier time
(`val_lt`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The region of a state in a tile of `B` biased and `P` plain rounds after the first. -/
def Reg (B P : Nat) (s : Site) (rb rp : Nat) : Prop :=
  (s.pos < 10064 ∧ rb = 0 ∧ rp = 0) ∨
    ((10064 ≤ s.pos ∧ s.pos ≤ 13307) ∧ rb < B ∧ rp = 0) ∨
    ((13322 ≤ s.pos ∧ s.pos ≤ 15209) ∧ rb = B ∧ rp < P) ∨
    (15228 ≤ s.pos ∧ s.noTile = false ∧ rb = B ∧ rp = P)

/-- The place of a state in its tile. -/
def ordK (s : Site) (rb rp : Nat) : Nat := 32768 * (rb + rp) + s.pos

/-- The times a point has been passed. -/
def mult (s : Site) (rb rp q : Nat) : Nat :=
  if 10064 ≤ q ∧ q ≤ 13307 then
    (if (10064 ≤ s.pos ∧ s.pos ≤ 13307) ∧ q < s.pos then 1 else 0) + rb
  else if 13322 ≤ q ∧ q ≤ 15209 then
    (if (13322 ≤ s.pos ∧ s.pos ≤ 15209) ∧ q < s.pos then 1 else 0) + rp
  else if q < s.pos then 1 else 0

theorem pos_le (s : Site) : s.pos < 32768 := by
  have h : allSites.all (fun s => decide (s.pos < 32768)) = true := by decide +kernel
  simpa using List.all_eq_true.mp h s (mem_allSites s)

private theorem posCode_chk : allSites.all (fun s => allSites.all fun s' =>
    !decide (s.pos = s'.pos) || decide (s = s') || s.noTile != s'.noTile) = true := by
  decide +kernel

/-- A site of a lane with a tile is determined by its position. -/
theorem pos_inj {s s' : Site} (h : s.pos = s'.pos) (hs : s.noTile = s'.noTile) : s = s' := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp posCode_chk s (mem_allSites s)) s'
    (mem_allSites s')
  simpa [h, hs] using h1

/-- Every site but the exit's is before it. -/
theorem pos_exit {s : Site} (h : ∀ l, s ≠ .exit l) : s.pos < 18410 := by
  have h1 : allSites.all (fun s => decide (s.pos < 18410) || decide (s = .exit true) ||
      decide (s = .exit false)) = true := by decide +kernel
  have h2 := List.all_eq_true.mp h1 s (mem_allSites s)
  simpa [h] using h2

theorem passed_cons (q : Nat) (pts : List Nat) {s : Site} (hs : s.noTile = false) (rb rp : Nat) :
    passed (q :: pts) s rb rp = mult s rb rp q + passed pts s rb rp := by
  have hb : (if before s q = true then 1 else 0) + rb * (if inBias q = true then 1 else 0) +
      rp * (if inPlain q = true then 1 else 0) = mult s rb rp q := by
    simp only [before, inBias, inPlain, mult, hs, Bool.false_and, Bool.not_false, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq]
    split_ifs <;> simp_all <;> omega
  rw [← hb]
  simp only [passed, List.countP_cons, Nat.mul_add]
  omega

theorem mult_le {B P : Nat} {s s' : Site} {rb rp rb' rp' : Nat} (h : Reg B P s rb rp)
    (h' : Reg B P s' rb' rp') (hK : ordK s rb rp < ordK s' rb' rp') (q : Nat) :
    mult s rb rp q ≤ mult s' rb' rp' q ∧
      (q = s.pos → mult s rb rp q < mult s' rb' rp' q) := by
  have := pos_le s
  have := pos_le s'
  unfold ordK at hK
  unfold Reg at h h'
  unfold mult
  rcases h with h | h | h | h <;> rcases h' with h' | h' | h' | h' <;>
    refine ⟨?_, ?_⟩ <;> (try rintro rfl) <;> split_ifs <;> omega

/-- **A point at an earlier state's site is passed once more by a later state.** -/
theorem passed_lt {B P : Nat} {s s' : Site} {rb rp rb' rp' : Nat} (h : Reg B P s rb rp)
    (h' : Reg B P s' rb' rp') (hs : s.noTile = false) (hs' : s'.noTile = false)
    (hK : ordK s rb rp < ordK s' rb' rp') (pts : List Nat) :
    passed pts s rb rp + pts.countP (· = s.pos) ≤ passed pts s' rb' rp' := by
  induction pts with
  | nil => simp [passed]
  | cons q pts ih =>
    rw [passed_cons q pts hs, passed_cons q pts hs', List.countP_cons]
    obtain ⟨h1, h2⟩ := mult_le h h' hK q
    by_cases hq : q = s.pos
    · have := h2 hq
      simp only [hq, decide_true, ite_true] at this ⊢
      omega
    · simp only [hq, decide_false, Bool.false_eq_true, ite_false]
      omega

/-! ### The times -/

/-- **States at one place** are at one site with the same rounds done. -/
theorem ordK_eq {B P : Nat} {s s' : Site} {rb rp rb' rp' : Nat} (h : Reg B P s rb rp)
    (h' : Reg B P s' rb' rp') (hK : ordK s rb rp = ordK s' rb' rp') :
    s.pos = s'.pos ∧ rb = rb' ∧ rp = rp' := by
  have := pos_le s
  have := pos_le s'
  unfold ordK at hK
  unfold Reg at h h'
  omega

/-- The slot (relative to the rounds done) and offset of a round site of stage `st`, as one
number. -/
def val (st : Nat) (s : Site) : Option (Nat × Nat) :=
  match Progress.Sm.place st s with
  | some (bd, past, o) =>
    some ((ptsOf true (.acquire 80)).countP (before s) - (if past then 1 else 0), bd + o)
  | none => none

/-- The largest sub-step of a site in the time table. -/
def sm : Site → Nat
  | .pst .first 0 | .pst .bias 0 => 1
  | _ => 0

private def rg (s : Site) : Nat :=
  if s.pos < 10064 then 0 else if s.pos ≤ 13307 then 1 else if s.pos ≤ 15209 then 2 else 3

private def lin (x : Nat × Nat) : Nat := 4096 * x.1 + x.2

private def pairChk (st : Nat) (s s' : Site) : Bool :=
  match val st s, val st s' with
  | some a, some b =>
    (!(decide (s.pos < s'.pos) && (rg s == 0 || rg s == rg s')) ||
      decide (lin a + sm s < lin b)) &&
    ((rg s == 3 || rg s' == 0) || decide (lin a + sm s < lin b + 4096))
  | _, _ => true

set_option maxRecDepth 100000 in
private theorem pair_chk : [0, 1].all (fun st => (allSites.filter fun s => (val st s).isSome).all
    fun s => (allSites.filter fun s => (val st s).isSome).all (pairChk st s)) = true := by
  decide +kernel

private theorem pair_ok {st : Nat} (hst : st < 2) {s s' : Site} {a b : Nat × Nat}
    (ha : val st s = some a) (hb : val st s' = some b) :
    (s.pos < s'.pos → (rg s = 0 ∨ rg s = rg s') → lin a + sm s < lin b) ∧
      (rg s ≠ 3 → rg s' ≠ 0 → lin a + sm s < lin b + 4096) := by
  have h1 := List.all_eq_true.mp pair_chk st (by
    rcases show st = 0 ∨ st = 1 by omega with rfl | rfl <;> simp)
  have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1 s
    (List.mem_filter.mpr ⟨mem_allSites s, by rw [ha]; rfl⟩)) s'
    (List.mem_filter.mpr ⟨mem_allSites s', by rw [hb]; rfl⟩)
  simp only [pairChk, ha, hb, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not, Bool.or_eq_false_iff,
    beq_iff_eq, beq_eq_false_iff_ne] at h2
  obtain ⟨h3, h4⟩ := h2
  exact ⟨fun h5 h6 => by
      rcases h3 with (h3 | ⟨h3, h3'⟩) | h3
      · exact (h3 h5).elim
      · exact (h6.elim h3 h3').elim
      · exact h3,
    fun h5 h6 => by
      rcases h4 with (h4 | h4) | h4
      · exact (h5 h4).elim
      · exact (h6 h4).elim
      · exact h4⟩

private def slotChk (st : Nat) (s : Site) : Bool :=
  match val st s with
  | some a => decide (a.1 ≤ 2) && ((rg s == 1 || rg s == 2) || decide (a.1 ≤ 1)) &&
      ([false, true].all fun b => match Progress.Sm.place st s with
        | some (_, past, _) =>
          decide ((if past then 1 else 0) ≤ (ptsOf b (.acquire 80)).countP (before s)) &&
          decide ((ptsOf b (.acquire 80)).countP (before s) =
            (ptsOf true (.acquire 80)).countP (before s))
        | none => true)
  | none => true

private theorem slot_chk : [0, 1].all (fun st => allSites.all (slotChk st)) = true := by
  decide +kernel

private theorem pts80 (b : Bool) : (ptsOf b (.acquire 80)).countP inBias = 1 ∧
    (ptsOf b (.acquire 80)).countP inPlain = 1 := by cases b <;> decide +kernel

/-- The place of a round site of stage `st` after `u` rounds, as a time. -/
def valT (p : Params) (u : Nat) (a : Nat × Nat) : Nat :=
  Progress.pipeBase p + 4096 * (u + a.1) + a.2

/-- The S-full polls before a round state, and its slot within the tile. -/
theorem slot_of {B P st : Nat} (hst : st < 2) {s : Site} {rb rp : Nat} {a : Nat × Nat}
    (ha : val st s = some a) (h : Reg B P s rb rp) (b : Bool) :
    ∃ bd past o, Progress.Sm.place st s = some (bd, past, o) ∧ a.2 = bd + o ∧
      passed (ptsOf b (.acquire 80)) s rb rp - (if past then 1 else 0) = rb + rp + a.1 ∧
      rb + rp + a.1 ≤ 1 + B + P := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp slot_chk st (by
    rcases show st = 0 ∨ st = 1 by omega with rfl | rfl <;> simp)) s (mem_allSites s)
  obtain ⟨t1, t2⟩ := pts80 b
  unfold val at ha
  split at ha
  · rename_i bd past o hpl
    cases ha
    simp only [slotChk, val, hpl, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      beq_iff_eq, List.all_eq_true] at h1
    obtain ⟨⟨h2, h3⟩, h4⟩ := h1
    obtain ⟨h5, h6⟩ := h4 b (by cases b <;> simp)
    refine ⟨bd, past, o, hpl, rfl, ?_, ?_⟩
    · simp only [passed, t1, t2]
      rw [h6] at h5 ⊢
      omega
    · have hr : (rg s = 1 ∨ rg s = 2) → 10064 ≤ s.pos ∧ s.pos ≤ 15209 := by
        intro h
        by_cases h1 : s.pos < 10064
        · simp [rg, h1] at h
        · by_cases h2 : s.pos ≤ 13307
          · omega
          · by_cases h3 : s.pos ≤ 15209
            · omega
            · simp [rg, h1, h2, h3] at h
      unfold Reg at h
      simp only
      generalize
        (ptsOf true (.acquire 80)).countP (before s) - (if past then 1 else 0) = x at h2 h3 ⊢
      rcases h3 with h3 | h3
      · have := hr h3
        omega
      · omega
  · cases ha

/-- **An earlier place of the rounds has an earlier time.** -/
theorem val_lt {B P st : Nat} (hst : st < 2) {s s' : Site} {rb rp rb' rp' : Nat}
    {a b : Nat × Nat} (ha : val st s = some a) (hb : val st s' = some b)
    (h : Reg B P s rb rp) (h' : Reg B P s' rb' rp') (hK : ordK s rb rp < ordK s' rb' rp') (p :
        Params) :
    valT p (rb + rp) a + sm s < valT p (rb' + rp') b := by
  obtain ⟨h1, h2⟩ := pair_ok hst ha hb
  have := pos_le s
  have := pos_le s'
  have hr : ∀ s : Site, rg s = (if s.pos < 10064 then 0 else if s.pos ≤ 13307 then 1
    else if s.pos ≤ 15209 then 2 else 3) := fun _ => rfl
  have e1 := hr s
  have e2 := hr s'
  unfold valT
  unfold lin at h1 h2
  unfold ordK at hK
  unfold Reg at h h'
  rcases Nat.lt_trichotomy (rb + rp) (rb' + rp') with hu | hu | hu
  · have h3 := h2 (by rw [e1]; split_ifs <;> omega) (by rw [e2]; split_ifs <;> omega)
    omega
  · have h3 := h1 (by omega) (by rw [e1, e2]; split_ifs <;> omega)
    omega
  · omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
