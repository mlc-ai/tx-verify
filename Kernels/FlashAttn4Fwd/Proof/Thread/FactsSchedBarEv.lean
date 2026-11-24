-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedTc
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftBase
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrSync
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaWarp

@[expose] public section

/-! # The named-barrier events before a state

A thread's events on named barrier `id` before a state are a function of the state (`barCnt`):

* a softmax thread of warp `w`: its `bar.sync 2` and `bar.arrive 2` on barrier 2
  (`Counts.bar2`), its arrivals on its statistics barrier `w + 3` (`Counts.gen`); its barrier
  events are on these two (`soft_bar`);
* a correction thread of warp `w`: barrier 2 likewise, its syncs on the statistics barriers
  `w - 5` and `w - 1` of its two stages (`Counts.sync`; `corr_bar`);
* the MMA warp: its events on barrier 2 (`Counts.bar2`), its only barrier (`mma_event_class`);
* the prologue and the other roles make none. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The events on named barrier `id` before a state of thread `g`. -/
def barCnt (L : Launch) (g id : Nat) : ThreadD → Nat
  | .inr (.softmax s) =>
    (if id = 2 then Softmax.bar2Sync s + Softmax.bar2Arrive s else 0) +
      (if id = warpOf L g + 3 then (Softmax.trips L + 1) * s.i + Softmax.genPos s else 0)
  | .inr (.corr c) =>
    (if id = 2 then Correction.bar2Sync c + Correction.bar2Arrive c else 0) +
      (if id = warpOf L g - 5 then (Correction.trips L + 1) * c.i + Correction.syncPos L 0 c
        else 0) +
      (if id = warpOf L g - 1 then (Correction.trips L + 1) * c.i + Correction.syncPos L 1 c
        else 0)
  | .inr (.mma m) => if id = 2 then Mma.bar2A m.site else 0
  | _ => 0

theorem isBarId_of_kind {e : Event} {id : Nat} (h : Execution.isBarId id e = true) :
    ∃ c m, e.kind = .bar id c m := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [Execution.isBarId]

theorem prologue_not_bar {es : List Event} (h : ∀ x ∈ es, Prologue.ProKind x.kind) (id : Nat) :
    es.countP (Execution.isBarId id) = 0 := by
  refine List.countP_eq_zero.mpr fun x hx => ?_
  have := h x hx
  obtain ⟨pc, k⟩ := x
  cases k <;> simp_all [Prologue.ProKind, Execution.isBarId]

theorem mem_take_get' {g k : Nat} {x : Event} (hx : x ∈ (X.tr g).take k) :
    ∃ j, j < k ∧ X.get (g, j) = some x := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hjl : j < (X.tr g).length := by rw [List.length_take] at hj; omega
  refine ⟨j, by rw [List.length_take] at hj; omega, ?_⟩
  rw [List.getElem_take]
  exact List.getElem?_eq_getElem hjl

/-- Barrier 2's events among events whose barrier-2 events have 416 threads. -/
theorem bar2_count {es : List Event}
    (h : ∀ x ∈ es, ∀ c m, x.kind = .bar 2 c m → c = some 416) :
    es.countP (Execution.isBarId 2) = barEvents 2 416 .sync es + barEvents 2 416 .arrive es := by
  unfold barEvents
  refine countP_split (fun x hx => ?_) (fun x _ => ?_)
  · obtain ⟨pc, k⟩ := x
    cases k with
    | bar id c m =>
      by_cases hid : id = 2
      · subst hid
        have := h _ hx c m rfl
        subst this
        cases m <;> simp [Execution.isBarId, barIs]
      · cases c <;> cases m <;> simp [Execution.isBarId, barIs, hid]
    | _ => simp [Execution.isBarId, barIs]
  · obtain ⟨pc, k⟩ := x
    cases k with
    | bar id c m => cases c <;> cases m <;> simp [barIs]
    | _ => simp [barIs]

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **A softmax thread's events on each named barrier.** -/
theorem soft_barCnt {g k id : Nat} {s : Softmax.D} (hw : warpOf L g < 8)
    (hJ : Softmax.Counts L g s ((X.tr g).take k)) :
    ((X.tr g).take k).countP (Execution.isBarId id) = barCnt L g id (.inr (.softmax s)) := by
  have hform : ∀ x ∈ (X.tr g).take k, ∀ id' c m, x.kind = .bar id' c m →
      (id' = 2 ∧ c = some 416) ∨ (c = some 64 ∧ m = .arrive ∧ id' = warpOf L g + 3) := by
    intro x hx id' c m hk
    obtain ⟨j, -, hj⟩ := mem_take_get' hx
    obtain ⟨pc, k'⟩ := x
    simp only at hk
    subst hk
    exact soft_bar hpre hX ht hw hj
  have hid3 : warpOf L g + 3 = Softmax.kOf L g + 3 + 4 * Softmax.stOf L g := by
    simp only [Softmax.kOf, Softmax.stOf]; omega
  simp only [barCnt]
  by_cases h2 : id = 2
  · subst h2
    rw [bar2_count (fun x hx c m hk => ?_), hJ.bar2.1, hJ.bar2.2]
    · have : ¬ (2 = warpOf L g + 3) := by omega
      simp only [↓reduceIte, this, Nat.add_zero]
    · rcases hform x hx 2 c m hk with h | h
      · exact h.2
      · omega
  · by_cases h3 : id = warpOf L g + 3
    · subst h3
      have := soft_barOrd hpre hX ht hw k (id := warpOf L g + 3) (by omega)
      unfold barOrd at this
      rw [this, hid3, hJ.gen, ← hid3]
      simp [h2]
    · simp only [h2, h3, ↓reduceIte, Nat.add_zero]
      refine List.countP_eq_zero.mpr fun x hx hb => ?_
      obtain ⟨c, m, hk⟩ := isBarId_of_kind hb
      rcases hform x hx id c m hk with h | h
      · exact h2 h.1
      · exact h3 h.2.2

/-- **A correction thread's events on each named barrier.** -/
theorem corr_barCnt {g k id : Nat} {c : Correction.D} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (hJ : Correction.Counts L g c ((X.tr g).take k)) :
    ((X.tr g).take k).countP (Execution.isBarId id) = barCnt L g id (.inr (.corr c)) := by
  have hform : ∀ x ∈ (X.tr g).take k, ∀ id' cn m, x.kind = .bar id' cn m →
      (id' = 2 ∧ cn = some 416) ∨
        (cn = some 64 ∧ m = .sync ∧ ∃ st < 2, id' = warpOf L g - 5 + 4 * st) := by
    intro x hx id' cn m hk
    obtain ⟨j, -, hj⟩ := mem_take_get' hx
    obtain ⟨pc, k'⟩ := x
    simp only at hk
    subst hk
    exact corr_bar hpre hX ht hw hw' hj
  have hk0 := corr_kOf (L := L) hw hw'
  simp only [barCnt]
  by_cases h2 : id = 2
  · subst h2
    rw [bar2_count (fun x hx cn m hk => ?_), hJ.bar2.1, hJ.bar2.2]
    · simp only [↓reduceIte]
      have : (2 = warpOf L g - 5) = False := by simp; omega
      have : (2 = warpOf L g - 1) = False := by simp; omega
      simp [*]
    · rcases hform x hx 2 cn m hk with h | ⟨-, -, st, hst, h⟩
      · exact h.2
      · omega
  · have hsync : ∀ st < 2, id = warpOf L g - 5 + 4 * st →
        ((X.tr g).take k).countP (Execution.isBarId id) =
          (Correction.trips L + 1) * c.i + Correction.syncPos L st c := by
      intro st hst hid
      have := corr_barOrd hpre hX ht hw hw' k (id := id) h2
      unfold barOrd at this
      rw [this, ← hJ.sync st hst, hid, hk0]
      congr 1
      omega
    by_cases h5 : id = warpOf L g - 5
    · rw [hsync 0 (by decide) (by omega)]
      subst h5
      have a : ¬ (warpOf L g - 5 = 2) := by omega
      have b : ¬ (warpOf L g - 5 = warpOf L g - 1) := by omega
      simp [a, b]
    · by_cases h1 : id = warpOf L g - 1
      · rw [hsync 1 (by decide) (by omega)]
        subst h1
        have a : ¬ (warpOf L g - 1 = 2) := by omega
        have b : ¬ (warpOf L g - 1 = warpOf L g - 5) := by omega
        simp [a, b]
      · simp only [h2, h5, h1, ↓reduceIte, Nat.add_zero]
        refine List.countP_eq_zero.mpr fun x hx hb => ?_
        obtain ⟨cn, m, hk⟩ := isBarId_of_kind hb
        rcases hform x hx id cn m hk with h | ⟨-, -, st, hst, h⟩
        · exact h2 h.1
        · rcases (show st = 0 ∨ st = 1 by omega) with rfl | rfl
          · exact h5 (by omega)
          · exact h1 (by omega)

/-- **The MMA warp's events on each named barrier.** -/
theorem mma_barCnt {g k id : Nat} {m : Mma.D} (hw : warpOf L g = 12)
    (hJ : Mma.Counts L g m ((X.tr g).take k)) :
    ((X.tr g).take k).countP (Execution.isBarId id) = barCnt L g id (.inr (.mma m)) := by
  simp only [barCnt]
  by_cases h2 : id = 2
  · subst h2; simp only [↓reduceIte]; exact hJ.bar2
  · simp only [h2, ↓reduceIte]
    refine List.countP_eq_zero.mpr fun x hx hb => ?_
    obtain ⟨j, -, hj⟩ := mem_take_get' hx
    have hc := (mma_event_class hpre hX ht hw hj).1
    obtain ⟨cn, md, hk⟩ := isBarId_of_kind hb
    have hb' : Execution.isBar x = true := by
      obtain ⟨pc, k'⟩ := x; simp only at hk; subst hk; rfl
    rw [hc] at hb'
    obtain ⟨cn', md', hk'⟩ := isBarId_of_kind hb'
    rw [hk] at hk'
    cases hk'
    exact h2 rfl

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
