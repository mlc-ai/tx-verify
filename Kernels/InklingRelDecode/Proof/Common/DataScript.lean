-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.ElectOrdinal
public import Kernels.InklingRelDecode.Proof.Common.WarpColl
public import Kernels.InklingRelDecode.Proof.Prologue.Export.TimeNext
public import Kernels.InklingRelDecode.Proof.Softmax.Export.TcNext
public import Kernels.InklingRelDecode.Proof.Epilogue.Export.TcNext

@[expose] public section

/-! # The collectives of the data warps and their times

A data warp's collectives, in order: the startup's shuffle, the twelve elections of the barrier
initializations, five for each preloaded block (its shuffle and four elections), the Softmax
shuffles (three in round 0, nine in each later round) and the epilogue's shuffle when there are
blocks. `dataCn p lim n` is the pc of the `n`-th, `dataSlot p lim n` its time. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Descent

/-- The times of the sites of the data roles, as functions of the site (those of the roles'
`time`). -/
def proClock (s : Prologue.Site) : Nat := Lib.Slots.prologue + Prologue.allSites.idxOf s

def softClock (s : Softmax.Site) (i : Nat) : Nat :=
  match s with
  | .setMaxReg => Lib.Slots.enter | .bar0 => Lib.Slots.reuse | .pre j => 293+4*j.val
  | .epilogue => Lib.Slots.finish
  | s => Lib.Slots.softmax i+s.position

def epiClock (s : Epilogue.Site) : Nat := Lib.Slots.finish + 4*s.position

/-- The prologue's collective sites of a lane with `p` preloaded blocks. -/
def proColl (p : Nat) : List Prologue.Site :=
  (List.finRange 12).map .el ++ ((List.finRange 3).take p).flatMap fun b =>
    [.psh b, .pel b 0, .pel b 1, .pel b 2, .pel b 3]

/-- The Softmax shuffle site of the `m`-th shuffle of the loop. -/
def softSite (m : Nat) : Softmax.Site :=
  [.shfl4, .shfl5, .shfl6, .shfl7, .shfl8, .shfl9, .shfl10, .shfl11, .shfl12].getD
    (if m < 3 then m else (m - 3) % 9) .shfl4

/-- The round of the `m`-th shuffle of the loop. -/
def softRound (m : Nat) : Nat := if m < 3 then 0 else (m - 3) / 9 + 1

def dataCn (p lim n : Nat) : Option Nat :=
  if n = 0 then some 17
  else if n ≤ 12 + 5 * p then ((proColl p)[n - 1]?).map Prologue.Site.pc
  else if n - (13 + 5 * p) < Lib.shflBase lim then some (softSite (n - (13 + 5 * p))).pc
  else if n - (13 + 5 * p) = Lib.shflBase lim ∧ lim ≠ 0 then some 2603 else none

def dataSlot (p lim n : Nat) : Nat :=
  if n = 0 then 24
  else if n ≤ 12 + 5 * p then proClock (((proColl p)[n - 1]?).getD .sMax)
  else if n - (13 + 5 * p) < Lib.shflBase lim then
    softClock (softSite (n - (13 + 5 * p))) (softRound (n - (13 + 5 * p)))
  else epiClock .shfl

theorem proColl_length {p} (hp : p ≤ 3) : (proColl p).length = 12 + 5 * p := by
  interval_cases p <;> decide

/-- The collectives a prologue site follows: one for the startup, then the shuffles and
elections before it. -/
def proCount (p : Nat) (s : Prologue.Site) : Nat :=
  1 + Prologue.shflPosition p s + Prologue.electPosition p s

private def proOk (p : Nat) : Bool := Prologue.allSites.all fun s =>
  (match s.block with | some b => !decide (b.val < p) | none => false) ||
  ((isWarpAt s.pc == decide (s ∈ proColl p)) &&
    (!decide (s ∈ proColl p) || (proColl p)[proCount p s - 1]? == some s) &&
    (decide (s ∈ proColl p) ||
      if proCount p s ≤ 12 + 5 * p then
        match (proColl p)[proCount p s - 1]? with
        | some t => decide (proClock s < proClock t) && t.pc != s.pc
        | none => false
      else decide (proClock s < 1200)))

private theorem pro_ok : ∀ p < 4, proOk p = true := by decide +kernel

/-! ## The slots rise along the script -/

def ds_posOf (r : Nat) : Nat := [65, 68, 69, 72, 73, 74, 75, 79, 80].getD r 0

theorem ds_posOf_lt : ∀ r < 9, ∀ r' < 9, r < r' → ds_posOf r < ds_posOf r' := by decide

theorem ds_posOf_bound : ∀ r < 9, 65 ≤ ds_posOf r ∧ ds_posOf r ≤ 80 := by decide

def ds_softIdx (m : Nat) : Nat := if m < 3 then m else (m - 3) % 9

theorem ds_softIdx_lt (m : Nat) : ds_softIdx m < 9 := by unfold ds_softIdx; split_ifs <;> omega

theorem ds_soft_clock (m : Nat) :
    softClock (softSite m) (softRound m) = 1200 + 400 * softRound m + ds_posOf (ds_softIdx m) := by
  have h := ds_softIdx_lt m
  unfold softSite softRound ds_softIdx at *
  generalize (if m < 3 then m else (m - 3) % 9) = r at h ⊢
  interval_cases r <;> simp [softClock, Softmax.Site.position, ds_posOf, Lib.Slots.softmax,
    Lib.Slots.frame, Lib.Slots.stride] <;> omega

theorem ds_soft_mono {m m' : Nat} (h : m < m') :
    softClock (softSite m) (softRound m) < softClock (softSite m') (softRound m') := by
  rw [ds_soft_clock, ds_soft_clock]
  have a := ds_softIdx_lt m
  have b := ds_softIdx_lt m'
  have c := ds_posOf_bound _ a
  have d := ds_posOf_bound _ b
  by_cases hr : softRound m = softRound m'
  · have : ds_softIdx m < ds_softIdx m' := by
      unfold softRound ds_softIdx at *; split_ifs at * <;> omega
    have := ds_posOf_lt _ a _ b this
    omega
  · have : softRound m < softRound m' := by unfold softRound at *; split_ifs at * <;> omega
    omega

theorem ds_pro_clock_lt (s : Prologue.Site) : proClock s < 1200 := by
  have : Prologue.allSites.idxOf s ≤ Prologue.allSites.length := List.idxOf_le_length
  have h : Prologue.allSites.length < 1000 := by decide +kernel
  unfold proClock Lib.Slots.prologue
  omega

theorem ds_pro_clock_ge (s : Prologue.Site) : 100 ≤ proClock s := by
  unfold proClock Lib.Slots.prologue; omega

private def monoOk (p : Nat) : Bool := (List.range 28).all fun a => (List.range 28).all fun b =>
  decide (a < 1 ∨ b ≤ a ∨ 12 + 5 * p < b ∨
    proClock (((proColl p)[a - 1]?).getD .sMax) < proClock (((proColl p)[b - 1]?).getD .sMax))

private theorem mono_ok : ∀ p < 4, monoOk p = true := by decide +kernel

theorem ds_epi_clock : epiClock .shfl = Lib.Slots.finish + 4 := by
  simp [epiClock, Epilogue.Site.position]

theorem ds_finish_big : 1500 + 400 * 2 ^ 32 < Lib.Slots.finish := by
  simp [Lib.Slots.finish, Lib.Slots.frame, Lib.Slots.stride]

theorem ds_slot_pro {p lim n : Nat} (h1 : 1 ≤ n) (h : n ≤ 12 + 5 * p) :
    dataSlot p lim n = proClock (((proColl p)[n - 1]?).getD .sMax) := by
  have h0 : ¬ n = 0 := by omega
  simp [dataSlot, h0, h]

theorem ds_slot_soft {p lim n : Nat} (h : 12 + 5 * p < n)
    (hs : n - (13 + 5 * p) < Lib.shflBase lim) :
    dataSlot p lim n = 1200 + 400 * softRound (n - (13 + 5 * p)) +
      ds_posOf (ds_softIdx (n - (13 + 5 * p))) := by
  have h0 : ¬ n = 0 := by omega
  have h1 : ¬ n ≤ 12 + 5 * p := by omega
  simp [dataSlot, h0, h1, hs, ds_soft_clock]

theorem ds_slot_epi {p lim n : Nat} (h : 12 + 5 * p < n)
    (hs : ¬ n - (13 + 5 * p) < Lib.shflBase lim) :
    dataSlot p lim n = Lib.Slots.finish + 4 := by
  have h0 : ¬ n = 0 := by omega
  have h1 : ¬ n ≤ 12 + 5 * p := by omega
  simp [dataSlot, h0, h1, hs, ds_epi_clock]

theorem ds_round_lt {m lim : Nat} (hl : lim < 2 ^ 31) (h : m < Lib.shflBase lim) :
    softRound m < 2 ^ 32 := by
  unfold Lib.shflBase at h; unfold softRound; split_ifs at * <;> omega

/-- **The slots of the script rise.** -/
theorem data_slot_mono {p lim a b : Nat} (hp : p ≤ 3) (hl : lim < 2 ^ 31) (hab : a < b)
    (hb : (dataCn p lim b).isSome = true) : dataSlot p lim a < dataSlot p lim b := by
  have hbd : b ≤ 12 + 5 * p ∨ b - (13 + 5 * p) < Lib.shflBase lim ∨
      b - (13 + 5 * p) = Lib.shflBase lim := by
    unfold dataCn at hb
    split_ifs at hb <;> first | omega | simp at hb
  by_cases hb1 : b ≤ 12 + 5 * p
  · have ha1 : a ≤ 12 + 5 * p := by omega
    by_cases ha0 : a = 0
    · subst ha0
      have : dataSlot p lim 0 = 24 := by unfold dataSlot; simp
      rw [this, ds_slot_pro (by omega) hb1]
      have := ds_pro_clock_ge (((proColl p)[b - 1]?).getD .sMax)
      omega
    · rw [ds_slot_pro (by omega) ha1, ds_slot_pro (by omega) hb1]
      have := List.all_eq_true.mp (mono_ok p (by omega)) a (List.mem_range.mpr (by omega))
      have := List.all_eq_true.mp this b (List.mem_range.mpr (by omega))
      simp only [decide_eq_true_eq] at this
      omega
  · have bs : 1200 ≤ dataSlot p lim b := by
      by_cases hs : b - (13 + 5 * p) < Lib.shflBase lim
      · rw [ds_slot_soft (by omega) hs]; omega
      · rw [ds_slot_epi (by omega) hs]
        unfold Lib.Slots.finish Lib.Slots.frame Lib.Slots.stride; omega
    by_cases ha1 : a ≤ 12 + 5 * p
    · by_cases ha0 : a = 0
      · subst ha0
        have : dataSlot p lim 0 = 24 := by unfold dataSlot; simp
        omega
      · rw [ds_slot_pro (by omega) ha1]
        have := ds_pro_clock_lt (((proColl p)[a - 1]?).getD .sMax)
        omega
    · have hbs : b - (13 + 5 * p) < Lib.shflBase lim ∨ b - (13 + 5 * p) = Lib.shflBase lim := by
        omega
      by_cases hs : b - (13 + 5 * p) < Lib.shflBase lim
      · have has : a - (13 + 5 * p) < Lib.shflBase lim := by omega
        rw [ds_slot_soft (by omega) has, ds_slot_soft (by omega) hs, ← ds_soft_clock,
          ← ds_soft_clock]
        exact ds_soft_mono (by omega)
      · have has : a - (13 + 5 * p) < Lib.shflBase lim := by omega
        rw [ds_slot_soft (by omega) has, ds_slot_epi (by omega) hs]
        have := ds_round_lt hl has
        have := ds_finish_big
        have := ds_posOf_bound _ (ds_softIdx_lt (a - (13 + 5 * p)))
        omega

theorem ds_mem_all (s : Prologue.Site) : s ∈ Prologue.allSites := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- The pcs of the Softmax shuffles and the epilogue's. -/
def shufPcs : List Nat := [1261, 1838, 2234, 2242, 2244, 2246, 2248, 2253, 2255, 2603]

theorem ds_cn_mem {p lim n q : Nat} (h : 12 + 5 * p < n) (hq : dataCn p lim n = some q) :
    q ∈ shufPcs := by
  unfold dataCn at hq
  have h0 : ¬ n = 0 := by omega
  have h1 : ¬ n ≤ 12 + 5 * p := by omega
  simp only [h0, h1, ite_false] at hq
  split_ifs at hq <;> cases hq
  · have : softSite (n - (13 + 5 * p)) =
        [.shfl4, .shfl5, .shfl6, .shfl7, .shfl8, .shfl9, .shfl10, .shfl11, .shfl12].getD
          (ds_softIdx (n - (13 + 5 * p))) .shfl4 := rfl
    rw [this]
    have := ds_softIdx_lt (n - (13 + 5 * p))
    generalize ds_softIdx (n - (13 + 5 * p)) = r at this ⊢
    interval_cases r <;> decide
  · decide

theorem ds_cn_late {p lim n q : Nat} (h : 12 + 5 * p < n) (hq : dataCn p lim n = some q) :
    1261 ≤ q := by
  have := ds_cn_mem h hq
  simp only [shufPcs, List.mem_cons, List.not_mem_nil, or_false] at this
  omega

private theorem pro_facts {p : Nat} (hp : p ≤ 3) {s : Prologue.Site}
    (gate : ∀ b : Fin 3, s.block = some b → b.val < p) :
    (isWarpAt s.pc = decide (s ∈ proColl p)) ∧
    (s ∈ proColl p → (proColl p)[proCount p s - 1]? = some s) ∧
    (s ∉ proColl p → (proCount p s ≤ 12 + 5 * p →
        proClock s < proClock (((proColl p)[proCount p s - 1]?).getD .sMax) ∧
        (((proColl p)[proCount p s - 1]?).map Prologue.Site.pc ≠ some s.pc)) ∧
      (12 + 5 * p < proCount p s → proClock s < 1200)) := by
  have h := List.all_eq_true.mp (pro_ok p (by omega)) s (ds_mem_all s)
  have g : (match s.block with | some b => !decide (b.val < p) | none => false) = false := by
    cases hb : s.block with
    | none => rfl
    | some b => simp [gate b hb]
  rw [g, Bool.false_or] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun hm => ?_, fun hm => ?_⟩
  · rcases h2 with h2 | h2
    · simp [hm] at h2
    · exact h2
  · rcases h3 with h3 | h3
    · exact absurd h3 hm
    · constructor
      · intro hc
        simp only [hc, ite_true] at h3
        cases ht : (proColl p)[proCount p s - 1]? with
        | none => simp [ht] at h3
        | some t =>
          simp only [ht, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h3
          simpa [ht, Ne.symm] using h3
      · intro hc
        have : ¬ proCount p s ≤ 12 + 5 * p := by omega
        simpa [this] using h3

/-- **A prologue site is at a warp collective** exactly when the script has its pc at its count. -/
theorem pro_at_iff {p lim : Nat} (hp : p ≤ 3) {s : Prologue.Site}
    (gate : ∀ b : Fin 3, s.block = some b → b.val < p) :
    isWarpAt s.pc = true ↔ dataCn p lim (proCount p s) = some s.pc := by
  obtain ⟨h1, h2, h3⟩ := pro_facts hp gate
  have len := proColl_length hp
  constructor
  · intro h
    rw [h1] at h
    have hm := of_decide_eq_true h
    have e := h2 hm
    have lt := (List.getElem?_eq_some_iff.mp e).1
    have c0 : 1 ≤ proCount p s := by unfold proCount; omega
    have h0 : ¬ proCount p s = 0 := by omega
    have h1 : proCount p s ≤ 12 + 5 * p := by omega
    simp [dataCn, h0, h1, e]
  · intro h
    by_contra hn
    have hm : s ∉ proColl p := fun hm => hn (by rw [h1]; exact decide_eq_true hm)
    obtain ⟨a, -⟩ := h3 hm
    by_cases hc : proCount p s ≤ 12 + 5 * p
    · have c0 : 1 ≤ proCount p s := by unfold proCount; omega
      have h0 : ¬ proCount p s = 0 := by omega
      simp only [dataCn, h0, hc, ite_false, ite_true] at h
      exact (a hc).2 h
    · have := ds_cn_late (by omega) h
      have := s.pc_range
      omega

/-- The time of a prologue collective is its script slot. -/
theorem pro_slot_at {p lim : Nat} (hp : p ≤ 3) {s : Prologue.Site}
    (gate : ∀ b : Fin 3, s.block = some b → b.val < p) (h : isWarpAt s.pc = true) :
    dataSlot p lim (proCount p s) = proClock s := by
  obtain ⟨h1, h2, -⟩ := pro_facts hp gate
  rw [h1] at h
  have e := h2 (of_decide_eq_true h)
  have lt := (List.getElem?_eq_some_iff.mp e).1
  have len := proColl_length hp
  have c0 : 1 ≤ proCount p s := by unfold proCount; omega
  rw [ds_slot_pro c0 (by omega), e]
  rfl

/-- A prologue site that is no collective is earlier than every later slot. -/
theorem pro_slot_lt {p lim n : Nat} (hp : p ≤ 3) (hl : lim < 2 ^ 31) {s : Prologue.Site}
    (gate : ∀ b : Fin 3, s.block = some b → b.val < p) (h : isWarpAt s.pc = false)
    (hn : (dataCn p lim n).isSome = true) (hle : proCount p s ≤ n) :
    proClock s < dataSlot p lim n := by
  obtain ⟨h1, -, h3⟩ := pro_facts hp gate
  have hm : s ∉ proColl p := by
    intro hm; rw [h] at h1; simp [hm] at h1
  obtain ⟨a, b⟩ := h3 hm
  have len := proColl_length hp
  have c0 : 1 ≤ proCount p s := by unfold proCount; omega
  by_cases hc : proCount p s ≤ 12 + 5 * p
  · obtain ⟨hlt, -⟩ := a hc
    cases e : (proColl p)[proCount p s - 1]? with
    | none => have := List.getElem?_eq_none_iff.mp e; omega
    | some t =>
      simp only [e, Option.getD_some] at hlt
      have : dataSlot p lim (proCount p s) = proClock t := by rw [ds_slot_pro c0 hc, e]; rfl
      rcases Nat.eq_or_lt_of_le hle with rfl | hlt2
      · rw [this]; exact hlt
      · have := data_slot_mono hp hl hlt2 hn
        omega
  · have bound := b (by omega)
    have : 1200 ≤ dataSlot p lim n := by
      have hbd : n - (13 + 5 * p) < Lib.shflBase lim ∨ ¬ n - (13 + 5 * p) < Lib.shflBase lim := by
        omega
      rcases hbd with hs | hs
      · rw [ds_slot_soft (by omega) hs]; omega
      · rw [ds_slot_epi (by omega) hs]
        unfold Lib.Slots.finish Lib.Slots.frame Lib.Slots.stride; omega
    omega

/-! ## The startup states -/

/-- The collectives a startup site follows: the shuffle is made when the lane enters its role. -/
def startCount : Startup.Site → Nat
  | .enter _ => 1
  | _ => 0

/-- The clock of a startup site. -/
def startClock : Startup.Site → Nat
  | .alloc => 2 | .allocWr => 4 | .bar0 => 10 | .ld0 => 12 | .bar1 => 20
  | .relinq => 22 | .shfl => 24 | .enter _ => 26

private theorem cn_zero (p lim : Nat) : dataCn p lim 0 = some 17 := by simp [dataCn]

private theorem cn_one (p lim : Nat) : dataCn p lim 1 = some 130 := by
  have : ¬ (1 : Nat) = 0 := by omega
  simp [dataCn, this, proColl, Prologue.Site.pc, Prologue.elPc]

theorem ds_slot_ge_100 {p lim n : Nat} (h1 : 1 ≤ n) :
    100 ≤ dataSlot p lim n := by
  by_cases h : n ≤ 12 + 5 * p
  · rw [ds_slot_pro h1 h]; exact ds_pro_clock_ge _
  · have : 1200 ≤ dataSlot p lim n := by
      by_cases hs : n - (13 + 5 * p) < Lib.shflBase lim
      · rw [ds_slot_soft (by omega) hs]; omega
      · rw [ds_slot_epi (by omega) hs]
        unfold Lib.Slots.finish Lib.Slots.frame Lib.Slots.stride; omega
    omega

/-- A startup site is at a warp collective exactly when the script has its pc at its count. -/
theorem start_at_iff (p lim : Nat) (s : Startup.Site) :
    isWarpAt s.pc = true ↔ dataCn p lim (startCount s) = some s.pc := by
  cases s <;> simp only [startCount, cn_zero, cn_one, Startup.Site.pc] <;> first
    | decide +kernel
    | (rename_i r; cases r <;> simp [Startup.Entry.pc] <;> decide +kernel)

theorem start_slot_at (p lim : Nat) (s : Startup.Site) (h : isWarpAt s.pc = true) :
    dataSlot p lim (startCount s) = startClock s := by
  cases s with
  | shfl => simp [startCount, dataSlot, startClock]
  | enter r =>
    cases r <;> exact absurd h (by simp only [Startup.Site.pc, Startup.Entry.pc]; decide +kernel)
  | _ => exact absurd h (by simp only [Startup.Site.pc]; decide +kernel)

/-- A startup site that is no collective is earlier than every later slot. -/
theorem start_slot_lt {p lim n : Nat} (s : Startup.Site)
    (h : isWarpAt s.pc = false) (hle : startCount s ≤ n) :
    startClock s < dataSlot p lim n := by
  by_cases e : ∃ r, s = .enter r
  · obtain ⟨r, rfl⟩ := e
    have := ds_slot_ge_100 (p := p) (lim := lim) (show 1 ≤ n from hle)
    simp only [startClock]; omega
  · by_cases sh : s = .shfl
    · subst sh
      have : isWarpAt Startup.Site.shfl.pc = true := by simp only [Startup.Site.pc]; decide +kernel
      rw [this] at h; cases h
    · have c0 : startCount s = 0 := by cases s <;> simp_all [startCount]
      have clk : startClock s < 24 := by cases s <;> simp_all [startClock]
      by_cases n0 : n = 0
      · subst n0; simp [dataSlot]; omega
      · have := ds_slot_ge_100 (p := p) (lim := lim) (show 1 ≤ n by omega)
        omega

end PTX.Kernels.InklingRelDecode.Proof
