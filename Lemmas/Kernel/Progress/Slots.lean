-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Times in slots and item tables

A sequential schedule of a kernel that walks items, each in `n + 1` slots, gives every event a
time `clk n i s o`: offset `o` of slot `s` of item `i`. A `SlotClock` is such a function whose
times increase with the offset, with the slot of an item (offsets below `span`) and with the item
(slots up to `n`), and are at least `base`; `stdClock span base` is the standard one
(`slotClock_std`).

An item table (`ItemTab`) lists the offsets of the collective events of an item: before the trip
loop in slot 0 (`pre`), in trip `t` in slot `t + 1` (`trip`, `n - 1` trips), after the loop in slot
`n` (`post`). The `r`-th collective of item `i` is at `ItemTab.time`; the schedule `ItemTab.sched`
lists fixed times, then the collectives of the first `Ti` items, then a tail.

* With offsets more than one apart and below the span (`GapOk`), consecutive collectives are more
  than one apart (`ItemTab.sched_gap`).
* A state of region `k` (1 before the loop, 2 in trip `t`, 3 after it) with `a` of the region's
  collectives before it is at the schedule's time when it is the region's `a`-th collective
  (`ItemTab.sched_reg`), and earlier when its offset is below that collective's or the region has
  `a` collectives (`ItemTab.lt_sched_reg`). -/

namespace PTX.Sched

/-- **A clock in slots**: `clk n i s o` increases with the offset `o`, with the slot `s` of an
item for offsets below `span`, and with the item `i` for slots up to `n`; it is at least `base`,
and even at even offsets. -/
structure SlotClock (clk : Nat → Nat → Nat → Nat → Nat) (span base : Nat) : Prop where
  succ : ∀ {n i s o}, clk n i s (o + 1) = clk n i s o + 1
  slot : ∀ {n i s s' o o'}, s < s' → o < span → clk n i s o < clk n i s' o'
  item : ∀ {n i i' s s' o o'}, s ≤ n → i < i' → o < span → clk n i s o < clk n i' s' o'
  base : ∀ n i s o, base ≤ clk n i s o
  even : ∀ {n i s o}, o % 2 = 0 → clk n i s o % 2 = 0

/-- The standard clock: slot `s` of item `i` is the global slot `i (n + 1) + s`, `span` long,
after the fixed times below `base`. -/
def stdClock (span base n i s o : Nat) : Nat := base + span * (i * (n + 1) + s) + o

theorem slotClock_std {span base : Nat} (hs : span % 2 = 0) (hb : base % 2 = 0) :
    SlotClock (stdClock span base) span base where
  succ := by intros; unfold stdClock; omega
  slot := by
    intro n i s s' o o' h ho
    unfold stdClock
    have : span * (i * (n + 1) + s + 1) ≤ span * (i * (n + 1) + s') :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_succ] at this
    omega
  item := by
    intro n i i' s s' o o' hs hi ho
    unfold stdClock
    have h1 : (i + 1) * (n + 1) ≤ i' * (n + 1) := Nat.mul_le_mul_right _ hi
    have : span * (i * (n + 1) + s + 1) ≤ span * (i' * (n + 1) + s') :=
      Nat.mul_le_mul_left _ (by rw [Nat.succ_mul] at h1; omega)
    rw [Nat.mul_succ] at this
    omega
  base := by intros; unfold stdClock; omega
  even := by
    intro n i s o ho
    unfold stdClock
    have : span * (i * (n + 1) + s) % 2 = 0 := by
      rw [Nat.mul_mod, hs, Nat.zero_mul, Nat.zero_mod]
    omega

namespace SlotClock

variable {clk : Nat → Nat → Nat → Nat → Nat} {span base : Nat} (hc : SlotClock clk span base)
include hc

/-- Within a slot an earlier offset is earlier. -/
theorem lt_of_off {n i s o o' : Nat} (h : o < o') : clk n i s o < clk n i s o' := by
  induction o' with
  | zero => omega
  | succ o' ih =>
    rw [hc.succ]
    rcases Nat.lt_or_ge o o' with h' | h'
    · have := ih h'; omega
    · rw [show o = o' by omega]; omega

theorem le_of_off {n i s o o' : Nat} (h : o ≤ o') : clk n i s o ≤ clk n i s o' := by
  rcases Nat.lt_or_ge o o' with h' | h'
  · exact (hc.lt_of_off h').le
  · rw [show o = o' by omega]

/-- An earlier slot of an item, more than one earlier. -/
theorem succ_lt_slot {n i s s' o o' : Nat} (h : s < s') (ho : o + 1 < span) :
    clk n i s o + 1 < clk n i s' o' := by
  rw [← hc.succ]; exact hc.slot h ho

/-- An earlier item, more than one earlier. -/
theorem succ_lt_item {n i i' s s' o o' : Nat} (hs : s ≤ n) (hi : i < i') (ho : o + 1 < span) :
    clk n i s o + 1 < clk n i' s' o' := by
  rw [← hc.succ]; exact hc.item hs hi ho

/-- Every fixed time is before every slot. -/
theorem fixed_lt {x n i s o : Nat} (h : x < base) : x < clk n i s o :=
  h.trans_le (hc.base _ _ _ _)

end SlotClock

/-- Offsets more than one apart, the last more than one below `B`. -/
def GapOk (B : Nat) : List Nat → Bool
  | [] => true
  | [a] => decide (a + 1 < B)
  | a :: b :: l => decide (a + 1 < b) && GapOk B (b :: l)

theorem GapOk.step {B a : Nat} {l : List Nat} (h : GapOk B (a :: l) = true) : GapOk B l = true := by
  match l, h with
  | [], _ => rfl
  | b :: l, h => simp only [GapOk, Bool.and_eq_true] at h; exact h.2

theorem GapOk.lt {B : Nat} : ∀ {l : List Nat}, GapOk B l = true → ∀ {a : Nat}, a < l.length →
    l.getD a 0 + 1 < B
  | [], _, a, ha => absurd ha (Nat.not_lt_zero _)
  | [x], h, a, ha => by
    simp only [GapOk, decide_eq_true_eq] at h
    simp only [List.length_singleton, Nat.lt_one_iff] at ha
    subst ha; simpa using h
  | x :: y :: l, h, a, ha => by
    cases a with
    | zero =>
      have h1 := GapOk.lt (GapOk.step h) (a := 0) (by simp)
      simp only [GapOk, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [List.getD_cons_zero] at h1 ⊢
      omega
    | succ a =>
      have := GapOk.lt (GapOk.step h) (a := a) (by simp at ha ⊢; omega)
      simpa using this

theorem GapOk.gap {B : Nat} : ∀ {l : List Nat}, GapOk B l = true → ∀ {a : Nat},
    a + 1 < l.length → l.getD a 0 + 1 < l.getD (a + 1) 0
  | [], _, a, ha => absurd ha (Nat.not_lt_zero _)
  | [x], _, a, ha => by simp at ha
  | x :: y :: l, h, a, ha => by
    cases a with
    | zero =>
      simp only [GapOk, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa using h.1
    | succ a =>
      have := GapOk.gap (GapOk.step h) (a := a) (by simp at ha ⊢; omega)
      simpa using this

/-- A sorted list's entries more than one apart are increasing with the index. -/
theorem GapOk.mono {B : Nat} {l : List Nat} (h : GapOk B l = true) {a b : Nat} (hab : a < b)
    (hb : b < l.length) : l.getD a 0 + 1 < l.getD b 0 := by
  induction b with
  | zero => omega
  | succ b ih =>
    have h1 := GapOk.gap h (a := b) hb
    rcases Nat.lt_or_ge a b with h' | h'
    · have := ih h' (by omega); omega
    · rw [show a = b by omega]; exact h1


theorem ite_yes {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_no {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

/-- Positions in an item: `r = a + q t` with `a < q` for `r / q = t`, `r % q = a`. -/
theorem div_mod_of {q t a : Nat} (ha : a < q) : (a + q * t) / q = t ∧ (a + q * t) % q = a :=
  (Nat.div_mod_unique (by omega)).mpr ⟨rfl, ha⟩

/-- The warp collectives of an item: their offsets in slot 0 before the trip loop, in a trip's
slot, and in slot `n` after the loop. -/
structure ItemTab where
  pre : List Nat
  trip : List Nat
  post : List Nat

namespace ItemTab
variable (tb : ItemTab) {clk : Nat → Nat → Nat → Nat → Nat} {span base : Nat}

/-- The table's offsets are more than one apart and below the span. -/
def Ok (span : Nat) : Prop :=
  GapOk span tb.pre = true ∧ GapOk span tb.trip = true ∧ GapOk span tb.post = true

/-- The collectives of an item of `n - 1` trips. -/
def len (n : Nat) : Nat := tb.pre.length + tb.trip.length * (n - 1) + tb.post.length

/-- The slot of an item's `r`-th collective. -/
def slot (n r : Nat) : Nat :=
  if r < tb.pre.length then 0
  else if r - tb.pre.length < tb.trip.length * (n - 1) then
    (r - tb.pre.length) / tb.trip.length + 1
  else n

/-- The offset of an item's `r`-th collective in its slot. -/
def off (n r : Nat) : Nat :=
  if r < tb.pre.length then tb.pre.getD r 0
  else if r - tb.pre.length < tb.trip.length * (n - 1) then
    tb.trip.getD ((r - tb.pre.length) % tb.trip.length) 0
  else tb.post.getD (r - tb.pre.length - tb.trip.length * (n - 1)) 0

/-- The time of item `i`'s `r`-th collective. -/
def time (clk : Nat → Nat → Nat → Nat → Nat) (n i r : Nat) : Nat :=
  clk n i (tb.slot n r) (tb.off n r)

/-- The schedule: the fixed times, the collectives of the first `Ti` items, the tail after the
cluster's `T` items. -/
def sched (clk : Nat → Nat → Nat → Nat → Nat) (fix : List Nat) (tail : Nat → Nat) (n Ti T k : Nat) :
    Nat :=
  if k < fix.length then fix.getD k 0
  else if k - fix.length < Ti * tb.len n then
    tb.time clk n ((k - fix.length) / tb.len n) ((k - fix.length) % tb.len n)
  else clk n T 0 (tail (k - fix.length - Ti * tb.len n))

variable {tb}

theorem slot_le (n r : Nat) : tb.slot n r ≤ n := by
  unfold slot
  split_ifs with h1 h2
  · omega
  · have hq : 0 < tb.trip.length := by
      rcases Nat.eq_zero_or_pos tb.trip.length with h | h
      · rw [h] at h2; omega
      · exact h
    have := (Nat.div_lt_iff_lt_mul hq).mpr (by rw [Nat.mul_comm]; exact h2)
    omega
  · exact le_rfl

theorem off_lt (hok : tb.Ok span) {n r : Nat} (hr : r < tb.len n) : tb.off n r + 1 < span := by
  obtain ⟨h1, h2, h3⟩ := hok
  unfold off
  split_ifs with ha hb
  · exact GapOk.lt h1 ha
  · have hq : 0 < tb.trip.length := by
      rcases Nat.eq_zero_or_pos tb.trip.length with h | h
      · rw [h] at hb; omega
      · exact h
    exact GapOk.lt h2 (Nat.mod_lt _ hq)
  · unfold len at hr; exact GapOk.lt h3 (by omega)

/-- **Consecutive collectives of an item are more than one apart.** -/
theorem time_gap (hc : SlotClock clk span base)
    (hok : tb.Ok span) {n i r : Nat} (hn : 1 ≤ n) (hr : r + 1 < tb.len n) :
    tb.time clk n i r + 1 < tb.time clk n i (r + 1) := by
  have ho := off_lt hok (n := n) (r := r) (by omega)
  obtain ⟨h1, h2, h3⟩ := hok
  unfold time
  -- the slots and offsets of the two
  by_cases hp : r + 1 < tb.pre.length
  · have e1 : tb.slot n r = 0 := by simp [slot, show r < tb.pre.length by omega]
    have e2 : tb.slot n (r + 1) = 0 := by simp [slot, hp]
    have e3 : tb.off n r = tb.pre.getD r 0 := by simp [off, show r < tb.pre.length by omega]
    have e4 : tb.off n (r + 1) = tb.pre.getD (r + 1) 0 := by simp [off, hp]
    rw [e1, e2, e3, e4, ← hc.succ]
    exact hc.lt_of_off (GapOk.gap h1 hp)
  by_cases hq : r + 1 - tb.pre.length < tb.trip.length * (n - 1)
  · have hq0 : 0 < tb.trip.length := by
      rcases Nat.eq_zero_or_pos tb.trip.length with h | h
      · rw [h] at hq; omega
      · exact h
    have e2 : tb.slot n (r + 1) = (r + 1 - tb.pre.length) / tb.trip.length + 1 := by
      simp [slot, hp, hq]
    have e4 : tb.off n (r + 1) = tb.trip.getD ((r + 1 - tb.pre.length) % tb.trip.length) 0 := by
      simp [off, hp, hq]
    rw [e2, e4]
    by_cases hr0 : r < tb.pre.length
    · have e1 : tb.slot n r = 0 := by simp [slot, hr0]
      rw [e1]
      exact hc.succ_lt_slot (Nat.succ_pos _) ho
    · have hq' : r - tb.pre.length < tb.trip.length * (n - 1) := by omega
      have e1 : tb.slot n r = (r - tb.pre.length) / tb.trip.length + 1 := by
        simp [slot, hr0, hq']
      have e3 : tb.off n r = tb.trip.getD ((r - tb.pre.length) % tb.trip.length) 0 := by
        simp [off, hr0, hq']
      rw [e1]
      rw [e3] at ho ⊢
      -- `r - pre = a + q t`
      have hdm := Nat.mod_add_div (r - tb.pre.length) tb.trip.length
      have hlt := Nat.mod_lt (r - tb.pre.length) hq0
      generalize (r - tb.pre.length) % tb.trip.length = a at hdm hlt ho ⊢
      generalize (r - tb.pre.length) / tb.trip.length = t at hdm hlt ho ⊢
      have hx : r + 1 - tb.pre.length = (a + 1) + tb.trip.length * t := by omega
      rw [hx]
      by_cases ha : a + 1 < tb.trip.length
      · obtain ⟨d1, d2⟩ := div_mod_of (t := t) ha
        rw [d1, d2, ← hc.succ]
        exact hc.lt_of_off (GapOk.gap h2 ha)
      · have hx' : a + 1 + tb.trip.length * t = 0 + tb.trip.length * (t + 1) := by
          rw [Nat.mul_succ]; omega
        rw [hx', (div_mod_of (t := t + 1) hq0).1]
        exact hc.succ_lt_slot (Nat.lt_succ_self _) ho
  · -- the next is after the loop, in slot `n`
    have e2 : tb.slot n (r + 1) = n := by simp [slot, hp, hq]
    have e4 : tb.off n (r + 1) =
        tb.post.getD (r + 1 - tb.pre.length - tb.trip.length * (n - 1)) 0 := by
      simp [off, hp, hq]
    rw [e2, e4]
    by_cases hr0 : r < tb.pre.length
    · have e1 : tb.slot n r = 0 := by simp [slot, hr0]
      rw [e1]
      exact hc.succ_lt_slot (show 0 < n by omega) ho
    by_cases hq' : r - tb.pre.length < tb.trip.length * (n - 1)
    · have hq0 : 0 < tb.trip.length := by
        rcases Nat.eq_zero_or_pos tb.trip.length with h | h
        · rw [h] at hq'; omega
        · exact h
      have e1 : tb.slot n r = (r - tb.pre.length) / tb.trip.length + 1 := by
        simp [slot, hr0, hq']
      rw [e1]
      have hn2 : 2 ≤ n := by
        by_contra hc
        have h0 : n - 1 = 0 := by omega
        rw [h0, Nat.mul_zero] at hq'
        omega
      have hx : r - tb.pre.length = (tb.trip.length - 1) + tb.trip.length * (n - 2) := by
        have : tb.trip.length * (n - 1) = tb.trip.length * (n - 2) + tb.trip.length := by
          rw [← Nat.mul_succ]; congr 1; omega
        omega
      rw [hx, (div_mod_of (t := n - 2) (by omega : tb.trip.length - 1 < tb.trip.length)).1]
      exact hc.succ_lt_slot (show n - 2 + 1 < n by omega) ho
    · have e1 : tb.slot n r = n := by simp [slot, hr0, hq']
      have e3 : tb.off n r = tb.post.getD (r - tb.pre.length - tb.trip.length * (n - 1)) 0 := by
        simp [off, hr0, hq']
      rw [e1, e3, ← hc.succ]
      have hx : r + 1 - tb.pre.length - tb.trip.length * (n - 1) =
          r - tb.pre.length - tb.trip.length * (n - 1) + 1 := by omega
      rw [hx]
      refine hc.lt_of_off (GapOk.gap h3 ?_); unfold len at hr; omega

/-- An item's collective is more than one before every time of a later item. -/
theorem time_lt_item (hc : SlotClock clk span base)
    (hok : tb.Ok span) {n i i' r s o : Nat} (hr : r < tb.len n) (hi : i < i') :
    tb.time clk n i r + 1 < clk n i' s o :=
  hc.succ_lt_item (slot_le n r) hi (off_lt hok hr)

/-- An item's collective of the cluster is more than one before the tail. -/
theorem time_lt_tail (hc : SlotClock clk span base)
    (hok : tb.Ok span) {n i r T o : Nat} (hr : r < tb.len n) (hi : i < T) :
    tb.time clk n i r + 1 < clk n T 0 o :=
  time_lt_item hc hok hr hi

theorem time_base (hc : SlotClock clk span base) {n i r : Nat} : base ≤ tb.time clk n i r :=
  hc.base _ _ _ _

variable {fix : List Nat} {tail : Nat → Nat} {n Ti T : Nat}

/-- The schedule at item `i`'s `r`-th collective. -/
theorem sched_item {i r : Nat} (hi : i < Ti) (hr : r < tb.len n) :
    tb.sched clk fix tail n Ti T (fix.length + (tb.len n * i + r)) = tb.time clk n i r := by
  have hlt : tb.len n * i + r < Ti * tb.len n := by
    have : tb.len n * (i + 1) ≤ tb.len n * Ti := Nat.mul_le_mul_left _ hi
    rw [Nat.mul_succ] at this
    rw [Nat.mul_comm Ti]; omega
  obtain ⟨d1, d2⟩ := div_mod_of (t := i) hr
  unfold sched
  rw [ite_no (by omega), Nat.add_sub_cancel_left, ite_yes hlt, Nat.add_comm (tb.len n * i), d1, d2]

/-- The schedule after the first `Ti` items. -/
theorem sched_tail {m : Nat} (hm : Ti * tb.len n ≤ m) :
    tb.sched clk fix tail n Ti T (fix.length + m) = clk n T 0 (tail (m - Ti * tb.len n)) := by
  unfold sched
  rw [ite_no (by omega), Nat.add_sub_cancel_left, ite_no (by omega)]

/-- Every time of item `i` is before the schedule's first collective after the item. -/
theorem lt_sched_next (hc : SlotClock clk span base)
    {i s o : Nat} (hi : i < Ti) (hT : Ti ≤ T) (hs : s ≤ n) (ho : o < span) :
    clk n i s o < tb.sched clk fix tail n Ti T (fix.length + tb.len n * (i + 1)) := by
  by_cases h1 : i + 1 < Ti ∧ 0 < tb.len n
  · have := sched_item (clk := clk) (fix := fix) (tail := tail) (T := T) (r := 0) h1.1 h1.2
    rw [Nat.add_zero] at this
    rw [this]
    exact hc.item hs (Nat.lt_succ_self i) ho
  · rw [sched_tail (by
      rcases Nat.lt_or_ge (i + 1) Ti with h | h
      · have : tb.len n = 0 := by omega
        rw [this]; simp
      · rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ h)]
    exact hc.item hs (by omega) ho

/-- The fixed times are more than one apart and below the items' slots. -/
abbrev FixOk (base : Nat) (fix : List Nat) : Prop := GapOk base fix = true

/-- **Consecutive collectives of the schedule are more than one apart.** -/
theorem sched_gap (hc : SlotClock clk span base)
    (hok : tb.Ok span) (hfix : FixOk base fix) (htail : ∀ j, tail j + 1 < tail (j + 1))
    (hn : 1 ≤ n) (hT : Ti ≤ T) (k : Nat) :
    tb.sched clk fix tail n Ti T k + 1 < tb.sched clk fix tail n Ti T (k + 1) := by
  by_cases hk : k + 1 < fix.length
  · unfold sched
    rw [ite_yes (by omega), ite_yes hk]
    exact GapOk.gap hfix hk
  by_cases hk' : k < fix.length
  · have hfk := GapOk.lt hfix hk'
    have e1 : tb.sched clk fix tail n Ti T k = fix.getD k 0 := by unfold sched; rw [ite_yes hk']
    rw [e1]
    have hk1 : k + 1 = fix.length + 0 := by omega
    rw [hk1]
    unfold sched
    rw [ite_no (by omega), Nat.add_sub_cancel_left]
    split_ifs
    · exact hfk.trans_le (time_base hc)
    · exact hfk.trans_le (hc.base _ _ _ _)
  -- past the fixed times: `k = fix.length + m`
  obtain ⟨m, rfl⟩ : ∃ m, k = fix.length + m := ⟨k - fix.length, by omega⟩
  rw [Nat.add_assoc]
  by_cases hm : m < Ti * tb.len n
  · have hl : 0 < tb.len n := by
      rcases Nat.eq_zero_or_pos (tb.len n) with h | h
      · rw [h] at hm; omega
      · exact h
    have hdm := Nat.mod_add_div m (tb.len n)
    have hlt := Nat.mod_lt m hl
    have hiT : m / tb.len n < Ti := (Nat.div_lt_iff_lt_mul hl).mpr hm
    generalize m % tb.len n = r at hdm hlt
    generalize m / tb.len n = i at hdm hiT
    subst hdm
    rw [show r + tb.len n * i = tb.len n * i + r by omega, sched_item hiT hlt]
    by_cases hr : r + 1 < tb.len n
    · rw [Nat.add_assoc, sched_item hiT hr]
      exact time_gap hc hok hn hr
    · have hr1 : tb.len n * i + r + 1 = tb.len n * (i + 1) := by rw [Nat.mul_succ]; omega
      rw [hr1]
      by_cases hi1 : i + 1 < Ti
      · have := sched_item (clk := clk) (fix := fix) (tail := tail) (T := T) (r := 0) hi1 hl
        rw [Nat.add_zero] at this
        rw [this]
        exact time_lt_item hc hok hlt (Nat.lt_succ_self i)
      · rw [sched_tail (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega))]
        exact time_lt_tail hc hok hlt (by omega)
  · rw [sched_tail (by omega), sched_tail (by omega),
      show m + 1 - Ti * tb.len n = m - Ti * tb.len n + 1 by omega]
    rw [← hc.succ]
    exact hc.lt_of_off (htail _)

/-- The schedule at a fixed time. -/
theorem sched_fix {k : Nat} (hk : k < fix.length) :
    tb.sched clk fix tail n Ti T k = fix.getD k 0 := by
  unfold sched; rw [ite_yes hk]

/-- The schedule past the fixed times is in the items' slots or the tail. -/
theorem base_le_sched (hc : SlotClock clk span base)
    {k : Nat} (hk : fix.length ≤ k) : base ≤ tb.sched clk fix tail n Ti T k := by
  unfold sched
  rw [ite_no (by omega)]
  split_ifs
  · exact time_base hc
  · exact (hc.base _ _ _ _)

/-- Even offsets. -/
def EvenOk (l : List Nat) : Bool := l.all (· % 2 = 0)

theorem EvenOk.get {l : List Nat} (h : EvenOk l = true) (a : Nat) : l.getD a 0 % 2 = 0 := by
  rcases Nat.lt_or_ge a l.length with ha | ha
  · simp only [EvenOk, List.all_eq_true, decide_eq_true_eq] at h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, Option.getD_some]
    exact h _ (List.getElem_mem ha)
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none ha]

/-- **A schedule of even offsets has even times.** -/
theorem sched_even (hc : SlotClock clk span base)
    (hfix : EvenOk fix = true) (hp : EvenOk tb.pre = true)
    (hq : EvenOk tb.trip = true) (hr : EvenOk tb.post = true) (htail : ∀ j, tail j % 2 = 0)
    (k : Nat) : tb.sched clk fix tail n Ti T k % 2 = 0 := by
  unfold sched
  split_ifs
  · exact EvenOk.get hfix _
  · unfold time off
    split_ifs
    · exact hc.even (EvenOk.get hp _)
    · exact hc.even (EvenOk.get hq _)
    · exact hc.even (EvenOk.get hr _)
  · exact hc.even (htail _)

/-! ### The regions of an item -/

/-- The offsets of region `k`: before the loop (1), in a trip (2), after the loop (3). -/
def rlist (tb : ItemTab) : Nat → List Nat
  | 1 => tb.pre
  | 2 => tb.trip
  | _ => tb.post

/-- The collectives of the item before region `k` at trip `t`. -/
def rbase (tb : ItemTab) (n t : Nat) : Nat → Nat
  | 1 => 0
  | 2 => tb.pre.length + tb.trip.length * t
  | _ => tb.pre.length + tb.trip.length * (n - 1)

/-- The slot of region `k` at trip `t`. -/
def rslot (n t : Nat) : Nat → Nat
  | 1 => 0
  | 2 => t + 1
  | _ => n

/-- A region and trip of an item: region 2 at a loop trip. -/
def RegOk (n t k : Nat) : Prop := k = 1 ∨ (k = 2 ∧ t + 1 < n) ∨ k = 3

theorem rslot_le {n t k : Nat} (h : RegOk n t k) : rslot n t k ≤ n := by
  rcases h with rfl | ⟨rfl, h⟩ | rfl <;> simp only [rslot] <;> omega

theorem rbase_le {n t k : Nat} (h : RegOk n t k) :
    rbase tb n t k + (rlist tb k).length ≤ tb.len n := by
  have hm : ∀ t', t' + 1 < n → tb.trip.length * t' + tb.trip.length ≤ tb.trip.length * (n - 1) :=
    fun t' ht => by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  unfold len
  rcases h with rfl | ⟨rfl, h⟩ | rfl <;> simp only [rbase, rlist]
  · omega
  · have := hm t h; omega
  · omega

theorem time_pre {n i r : Nat} (h : r < tb.pre.length) :
    tb.time clk n i r = clk n i 0 (tb.pre.getD r 0) := by
  simp [time, slot, off, h]

theorem time_trip {n i r : Nat} (h1 : tb.pre.length ≤ r)
    (h2 : r - tb.pre.length < tb.trip.length * (n - 1)) :
    tb.time clk n i r = clk n i ((r - tb.pre.length) / tb.trip.length + 1)
      (tb.trip.getD ((r - tb.pre.length) % tb.trip.length) 0) := by
  have h1' : ¬ r < tb.pre.length := by omega
  simp [time, slot, off, h1', h2]

theorem time_post {n i r : Nat} (h1 : tb.pre.length ≤ r)
    (h2 : tb.trip.length * (n - 1) ≤ r - tb.pre.length) :
    tb.time clk n i r = clk n i n
      (tb.post.getD (r - tb.pre.length - tb.trip.length * (n - 1)) 0) := by
  have h1' : ¬ r < tb.pre.length := by omega
  have h2' : ¬ r - tb.pre.length < tb.trip.length * (n - 1) := by omega
  simp [time, slot, off, h1', h2']

/-- The `a`-th collective of a region. -/
theorem time_reg {n t k i a : Nat} (h : RegOk n t k) (ha : a < (rlist tb k).length) :
    tb.time clk n i (rbase tb n t k + a) = clk n i (rslot n t k) ((rlist tb k).getD a 0) := by
  rcases h with rfl | ⟨rfl, ht⟩ | rfl <;> simp only [rbase, rlist, rslot] at ha ⊢
  · rw [Nat.zero_add, time_pre ha]
  · have hlt : tb.trip.length * t + a < tb.trip.length * (n - 1) := by
      have : tb.trip.length * (t + 1) ≤ tb.trip.length * (n - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at this; omega
    have hx : tb.pre.length + tb.trip.length * t + a - tb.pre.length = a + tb.trip.length * t := by
      omega
    obtain ⟨d1, d2⟩ := div_mod_of (t := t) ha
    rw [time_trip (by omega) (by omega), hx, d1, d2]
  · rw [time_post (by omega) (by omega)]
    congr 2
    omega

/-- The collective after a region's last is in a later slot. -/
theorem time_reg_end (hc : SlotClock clk span base)
    {n t k i o : Nat} (hn : 1 ≤ n) (h : RegOk n t k) (ho : o < span)
    (hr : rbase tb n t k + (rlist tb k).length < tb.len n) :
    clk n i (rslot n t k) o < tb.time clk n i (rbase tb n t k + (rlist tb k).length) := by
  unfold len at hr
  rcases h with rfl | ⟨rfl, ht⟩ | rfl <;> simp only [rbase, rlist, rslot] at hr ⊢
  · rw [Nat.zero_add]
    by_cases h2 : tb.pre.length - tb.pre.length < tb.trip.length * (n - 1)
    · rw [time_trip le_rfl h2]
      exact hc.slot (Nat.succ_pos _) ho
    · rw [time_post le_rfl (by omega)]
      exact hc.slot (by omega) ho
  · have hx : tb.pre.length + tb.trip.length * t + tb.trip.length - tb.pre.length =
        0 + tb.trip.length * (t + 1) := by rw [Nat.mul_succ]; omega
    by_cases h2 : tb.pre.length + tb.trip.length * t + tb.trip.length - tb.pre.length <
        tb.trip.length * (n - 1)
    · have hq0 : 0 < tb.trip.length := by
        rcases Nat.eq_zero_or_pos tb.trip.length with h0 | h0
        · rw [h0] at h2; simp at h2
        · exact h0
      rw [time_trip (by omega) h2, hx, (div_mod_of (t := t + 1) hq0).1]
      exact hc.slot (by omega) ho
    · rw [time_post (by omega) (by omega)]
      exact hc.slot ht ho
  · omega

/-- **A collective of region `k` is at the schedule's time.** -/
theorem sched_reg {n t k i a : Nat} (h : RegOk n t k) (hi : i < Ti)
    (ha : a < (rlist tb k).length) :
    tb.sched clk fix tail n Ti T (fix.length + (tb.len n * i + (rbase tb n t k + a))) =
      clk n i (rslot n t k) ((rlist tb k).getD a 0) := by
  rw [sched_item hi (by have := rbase_le (tb := tb) h; omega), time_reg h ha]

/-- **A state of region `k` before the region's `a`-th collective is earlier than the schedule's
collective**: its offset is below that collective's, or the region has `a` collectives. -/
theorem lt_sched_reg (hc : SlotClock clk span base)
    {n t k i a o : Nat} (hn : 1 ≤ n) (h : RegOk n t k) (hi : i < Ti)
    (hT : Ti ≤ T) (ho : o < span)
    (hc : (a < (rlist tb k).length ∧ o < (rlist tb k).getD a 0) ∨ a = (rlist tb k).length) :
    clk n i (rslot n t k) o <
      tb.sched clk fix tail n Ti T (fix.length + (tb.len n * i + (rbase tb n t k + a))) := by
  have hle := rbase_le (tb := tb) h
  rcases hc with ⟨ha, hlt⟩ | rfl
  · rw [sched_reg h hi ha]
    exact hc.lt_of_off hlt
  by_cases hr : rbase tb n t k + (rlist tb k).length < tb.len n
  · rw [sched_item hi hr]
    exact time_reg_end hc hn h ho hr
  · have he : tb.len n * i + (rbase tb n t k + (rlist tb k).length) = tb.len n * (i + 1) := by
      rw [Nat.mul_succ]; omega
    rw [he]
    exact lt_sched_next hc hi hT (rslot_le h) ho

end ItemTab

end PTX.Sched
