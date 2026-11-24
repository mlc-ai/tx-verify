-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.OrderBaseCausality
public import Lemmas.MBarrier.MBarrierHistory
public import Lemmas.Tcgen05.TcCommit
public import Lemmas.Tcgen05.TcMmaResultLayout
public import Lemmas.Tmem.TmemStore

namespace PTX.Tests.TmemWriters
open TcMma (byteInt s32)
noncomputable section

def launch : Launch := { grid := 1, block := 32, params := fun _ => none, sharedBase := 0,
                         clusterSize := 1 }
def smem : TcShared.Descriptor := ⟨0, 128, 256, 0, false, false, .none⟩
/-- A cta_group::1 kind::i8 128x8 MMA whose operands and D are in CTA `cta`. -/
def spec (cta : Nat) : TcMma.OperandSpec :=
  ⟨⟨.one, .i8 true true false, 128, 8, false, false, false, false, false⟩, smem, smem, cta, cta,
    none, {}⟩
def masks : List Nat := [0, 0, 0, 0]
def mb : Loc := ⟨.shared, 0, 4096⟩
def mmaAt (cta pc : Nat) : Event := ⟨pc, .tc (.mma 0 (spec cta) false masks)⟩
def mma (pc : Nat) : Event := mmaAt 0 pc
def cell0 : TcMma.Cell := ⟨0, 0, 0⟩

-- Two overwrites before the load, and another overwrite after wait::ld.
-- This fixture checks the ordering/read-source rules, not a whole kernel launch.
def X : Execution where
  tr := fun g => if g = 0 then [mma 0, mma 1, ⟨2, .tc (.commit (TcCommit.unicast mb))⟩,
    ⟨3, .wait mb 0 true⟩, ⟨4, .tc (.ld 0 [s32 0] .s32x32b)⟩, ⟨5, .tc .waitLd⟩, mma 6]
    else if g = 2 then [⟨7, .mbInit mb 1⟩] else []
  rf := fun _ _ => none

  async := {
    mmaOperands := fun i => if i == (0, 0) || i == (0, 1) then some ⟨[], []⟩ else none
    mmaDone := fun i => i == (0, 0) || i == (0, 1) }
  tcNotified := fun i => if i = (0, 2) then {0} else ∅
  objects m := if m = mb then
    match MBarrier.replay none [(.thread (2, 0), .init 1),
      (.async (0, 2) (.tcNotify 0), .arrive 1 0), (.thread (0, 3), .pollParity 0 true)] with
    | .ok xs => xs
    | .error _ => []
    else []

theorem baseCausality_forward {i j : Nat} (hij : i < j) (hj : j < 7) :
    baseCausality launch X (0, i) (0, j) :=
  .single (.inl (po_of_not_access rfl hij hj (by
    simp only [Execution.get, X, ite_true]
    rcases j with _ | _ | _ | _ | _ | _ | _ | j <;> simp [Event.acc, mma, mmaAt])))

theorem mma_indices {e : EvId} {cell : TcMma.Cell} (h : X.MmaCell e cell) :
    e = (0, 0) ∨ e = (0, 1) ∨ e = (0, 6) := by
  obtain ⟨d, s, accum, mask, row, col, ⟨pc, h⟩, _⟩ := h
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0
  · subst g
    match i with
    | 0 => exact .inl rfl
    | 1 => exact .inr (.inl rfl)
    | 6 => exact .inr (.inr rfl)
    | 2 | 3 | 4 | 5 | _ + 7 => simp [Execution.get, X, mma, mmaAt] at h
  · by_cases h2 : g = 2
    · subst g; cases i <;> simp [Execution.get, X, mma, mmaAt] at h
    · simp [Execution.get, X, hg, h2] at h

theorem no_store (e : EvId) (a : Nat) (vals : List Value) (sh : TcShape) :
    ¬ X.TSt e a vals sh := by
  rintro ⟨pc, h⟩
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0
  · subst g
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 => simp [Execution.get, X, mma, mmaAt] at h
  · by_cases h2 : g = 2
    · subst g; cases i <;> simp [Execution.get, X] at h
    · simp [Execution.get, X, hg, h2] at h

theorem no_cp (e : EvId) (c : TcCopy.Spec) : ¬ X.CpIssue e c := by
  rintro ⟨pc, h⟩
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0
  · subst g
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 => simp [Execution.get, X, mma, mmaAt] at h
  · by_cases h2 : g = 2
    · subst g; cases i <;> simp [Execution.get, X] at h
    · simp [Execution.get, X, hg, h2] at h

theorem no_shift (e : EvId) (s : TcShift.Spec) : ¬ X.ShiftIssue e s := by
  rintro ⟨pc, h⟩
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0
  · subst g
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 => simp [Execution.get, X, mma, mmaAt] at h
  · by_cases h2 : g = 2
    · subst g; cases i <;> simp [Execution.get, X] at h
    · simp [Execution.get, X, hg, h2] at h

theorem write_indices {e : EvId} {cell : TcMma.Cell} (h : TcMma.TmemWrite launch X e cell) :
    e = (0, 0) ∨ e = (0, 1) ∨ e = (0, 6) :=
  mma_indices (TcMma.tmemWrite_of_no_store no_store no_cp no_shift h)

theorem cell1 : X.MmaCell (0, 1) cell0 :=
  ⟨0, spec 0, false, masks, 0, 0, ⟨1, rfl⟩, rfl⟩

theorem pipe_before {i j : Nat} (hi : i = 0 ∨ i = 1 ∨ i = 6)
    (hj : j = 0 ∨ j = 1 ∨ j = 6) (hij : i < j) : TcMma.Before launch X (0, i) (0, j) := by
  have hiM : X.MmaIssue (0, i) 0 (spec 0) false masks := by
    rcases hi with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  have hjM : X.MmaIssue (0, j) 0 (spec 0) false masks := by
    rcases hj with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  exact .inr ⟨by simp [SameWarp, SameCta, launch, Launch.threads],
    .inl (baseCausality_forward hij (by rcases hj with rfl | rfl | rfl <;> decide)),
    0, spec 0, false, masks, 0, spec 0, false, masks, hiM, hjM,
    rfl, rfl, rfl, rfl, rfl⟩

-- The reader observes the second MMA; neither an older nor a future overwrite
-- forces rejection merely because there is more than one writer of the cell.
theorem candidate_observed : AsyncCopy.AsyncObserved X (0, 1) .mmaDone (0, 3) true .cta := by
  refine ⟨_, mb, ⟨(0, 2), TcCommit.unicast mb, 0, rfl, ⟨rfl, by decide,
    .inl ⟨0, spec 0, false, masks, ⟨1, rfl⟩⟩, _, ⟨2, rfl⟩⟩,
    ⟨2, rfl⟩, TcCommit.target_unicast rfl, by simp [X]⟩, ⟨3, 0, rfl⟩, ?_⟩
  exact ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      fun _ _ _ h2 _ => absurd h2 (by omega)⟩

theorem candidate_visible : TcMma.DoneBefore launch X (0, 1) (0, 4) :=
  .inl ⟨(0, 3), .cta, candidate_observed, ⟨⟨by decide, by decide, rfl⟩, ⟨by decide, by decide,
    rfl⟩⟩,
    baseCausality_forward (by decide) (by decide)⟩

theorem multiple_writers_stable : TcMma.ReadSource launch X .ld (0, 1) (0, 4) cell0 := by
  rw [TcMma.readSource_ld]
  refine ⟨by decide, .inl cell1, .inl (.inl candidate_visible), ?_, ?_⟩
  · intro y hy
    rcases write_indices hy with rfl | rfl | rfl
    · exact .inr (.inl (.inl (pipe_before (i := 0) (j := 1) (by decide) (by decide) (by decide))))
    · exact .inl rfl
    · exact .inr (.inr (.inl ⟨(0, 5), ⟨5, rfl⟩, rfl, by decide,
        .inl (baseCausality_forward (by decide) (by decide))⟩))
  · rintro cta r hr
    simp [X] at hr

theorem writes_ordered : TcMma.WritesSafe launch X := by
  intro e f cell he hf
  rcases write_indices he with rfl | rfl | rfl <;>
    rcases write_indices hf with rfl | rfl | rfl
  all_goals first
    | exact .inl rfl
    | exact .inr (.inl (.inl (pipe_before (by decide) (by decide) (by decide))))
    | exact .inr (.inr (.inl (pipe_before (by decide) (by decide) (by decide))))

theorem no_bar (e : EvId) (id pc : Nat) : ¬ X.IsBarrier e id none pc := by
  intro h
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0
  · subst g
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 => simp [Execution.IsBarrier, Execution.get, X, mma,
      mmaAt] at h
  · by_cases h2 : g = 2
    · subst g; cases i <;> simp [Execution.IsBarrier, Execution.get, X, mma, mmaAt] at h
    · simp [Execution.IsBarrier, Execution.get, X, hg, h2] at h

private theorem no_extra {e : EvId} {ev : Event} (h : X.get e = some ev) :
    (∀ m tx count scope, ev.kind ≠ .arrive m tx count true scope) ∧
    (∀ mask inst, ev.kind ≠ .warpBar mask inst) ∧
    (∀ a bs, ev.kind ≠ .wr a bs) ∧ (∀ a o n, ev.kind ≠ .rmw a o n) := by
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0
  · subst g
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 => (simp [Execution.get, X, mma,
                                                  mmaAt] at h; all_goals (subst h; simp))
  · by_cases h2 : g = 2
    · subst g
      cases i <;> simp [Execution.get, X, mma, mmaAt] at h
      subst h
      simp
    · simp [Execution.get, X, hg, h2] at h

theorem no_threadFence (e : EvId) (sem : FenceSem) (s : MbarScope) : ¬ X.ThreadFence e sem s := by
  rintro ⟨pc, h⟩
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0
  · subst g
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 => simp [Execution.get, X, mma, mmaAt] at h
  · by_cases h2 : g = 2
    · subst g; cases i <;> simp [Execution.get, X] at h
    · simp [Execution.get, X, hg, h2] at h

/-- The execution has no thread fence. -/
theorem no_fenceSync (e f : EvId) : ¬ FenceSync launch X e f := by
  rintro (⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨sem, s, hf | hf⟩, -⟩ |
    ⟨⟨s, -, hs, -⟩, -⟩)
  · exact no_threadFence e sem s hf
  · exact no_threadFence f sem s hf
  · exact no_threadFence e .sc s hs

/-- The execution has no release/acquire pair: every event is a fence-free tcgen05
operation, a wait or an initialization. -/
theorem no_sync (e f : EvId) : ¬ synchronizesWith launch X e f := by
  rintro ⟨a, b, bs, cs, hw, -, hrel, -⟩
  rcases hw with ⟨pc, hi⟩ | ⟨old, pc, hi⟩
  · exact False.elim ((no_extra hi).2.2.1 _ _ rfl)
  · exact False.elim ((no_extra hi).2.2.2 _ _ _ rfl)

theorem baseCausality_increasing {e f : EvId} (h : baseCausality launch X e f) : e.2 < f.2 := by
  have step : ∀ e f, (po X e f ∨ CtaBarSync launch X e f ∨ MSync launch X e f ∨
      ClusterSync launch X e f ∨ WarpBarSync launch X e f ∨ synchronizesWith launch X e f ∨
      FenceSync launch X e f) → e.2 < f.2 := by
    rintro e f (hp | hs | hm | hc | hw | hmem | hfs)
    · exact hp.2.1
    · simp [CtaBarSync, CtaBarK, CtaBarrier.GenerationOf, X] at hs
    · obtain ⟨x, w, m, rs, ac, ⟨tx, count, pc, ha⟩, _⟩ := hm
      exact False.elim ((no_extra ha).1 _ _ _ _ rfl)
    · simp [ClusterSync, ClusterBarrier.Synchronizes, ClusterBarrier.ArrivalOf, X] at hc
    · obtain ⟨i, j, ⟨_, mask, inst, ⟨pc, hi⟩, _⟩, _⟩ := hw
      exact False.elim ((no_extra hi).2.1 _ _ rfl)
    · exact absurd hmem (no_sync e f)
    · exact absurd hfs (no_fenceSync e f)
  induction h with
  | single h => exact step _ _ h
  | tail _ h ih => exact lt_trans ih (step _ _ h)

theorem no_fenceAfter (e : EvId) : ¬ X.FenceAfter e := by
  rintro ⟨pc, h⟩
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0
  · subst g
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 => simp [Execution.get, X, mma, mmaAt] at h
  · by_cases h2 : g = 2
    · subst g; cases i <;> simp [Execution.get, X] at h
    · simp [Execution.get, X, hg, h2] at h

/-- Without tcgen05 fences, a tcgen05 order of this execution is causality. -/
theorem tc_increasing {e f : EvId} (h : TcMma.TcBefore launch X e f) : e.2 < f.2 := by
  rcases h with h | ⟨-, -, -, ⟨f', -, hf, -⟩ | ⟨-, -, -, -, f', -, hf, -⟩⟩
  · exact baseCausality_increasing h
  all_goals exact (no_fenceAfter f' hf).elim

-- Selecting the older MMA would miss an intervening overwrite and is rejected.
theorem old_writer_not_stable : ¬ TcMma.ReadSource launch X .ld (0, 0) (0, 4) cell0 := by
  rw [TcMma.readSource_ld]
  rintro ⟨-, -, -, hcov, -⟩
  rcases hcov (0, 1) (.inl cell1) with heq | hwb | hwait | hpip
  · cases heq
  · -- the later MMA is not ordered before the older one
    rcases hwb with (hdone | hpiped) | hst | hcp
    · rcases hdone with ⟨w, ws, -, -, hbc⟩ | ⟨w, -, ⟨f', -, hf, -⟩⟩
      · exact absurd (baseCausality_increasing hbc) (by simp)
      · exact no_fenceAfter f' hf
    · have := tc_increasing hpiped.2.1
      omega
    · obtain ⟨a, vals, sh, pc, ht⟩ := hst.1
      exact no_store _ _ _ _ ⟨pc, ht⟩
    · obtain ⟨-, -, _, -, -, -, -, hc, -⟩ := hcp
      exact no_cp _ _ hc
  · -- a `wait::ld` after the load cannot precede it
    obtain ⟨w, -, -, hlt, htc⟩ := hwait
    have := tc_increasing htc
    omega
  · -- the load is not before the later MMA
    obtain ⟨-, htc, -⟩ := hpip
    have := tc_increasing htc
    omega

-- Two different warps have no implicit MMA pipeline, even at the same address/shape.
def twoWarps : Launch := { grid := 1, block := 64, params := fun _ => none, sharedBase := 0,
                           clusterSize := 1 }
def unordered : Execution where
  tr := fun g => if g = 0 ∨ g = 32 then [mma 0] else []
  rf := fun _ _ => none

theorem unordered_no_wait (e : EvId) (m : Loc) : ¬ unordered.AcquireWait e m := by
  rintro ⟨pc, parity, scope, h⟩
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0 ∨ g = 32
  · cases i <;> simp [Execution.get, unordered, hg, mma, mmaAt] at h
  · simp [Execution.get, unordered, hg] at h

theorem different_warps_no_order (e f : EvId)
    (hs : ¬ SameWarp twoWarps e.1 f.1) : ¬ TcMma.WriteBefore twoWarps unordered e f := by
  rintro (((⟨w, ws, ⟨_, m, ⟨c, _, _, _, _, _, _, hn⟩, _⟩, _, _⟩ |
      ⟨w, ⟨acq, ws, ⟨_, m, ⟨c, _, _, _, _, _, _, hn⟩, _⟩, _⟩, _⟩) | hp) |
        ⟨⟨a, vals, sh, pc, ht⟩, -⟩ |
        hcp)
  · exact Finset.notMem_empty _ hn
  · exact Finset.notMem_empty _ hn
  · exact hs hp.1
  rotate_left
  · exact hs hcp.1
  · obtain ⟨g, i⟩ := e
    by_cases hg : g = 0 ∨ g = 32
    · cases i <;> simp [Execution.get, unordered, hg, mma, mmaAt] at ht
    · simp [Execution.get, unordered, hg] at ht

theorem unordered_writes_rejected : TcMma.WritesUnsafe twoWarps unordered := by
  intro h
  have he : unordered.MmaCell (0, 0) cell0 := ⟨0, spec 0, false, masks, 0, 0, ⟨0, rfl⟩, rfl⟩
  have hf : unordered.MmaCell (32, 0) cell0 := ⟨0, spec 0, false, masks, 0, 0, ⟨0, rfl⟩, rfl⟩
  rcases h _ _ cell0 (.inl he) (.inl hf) with h | h | h
  · cases h
  · exact different_warps_no_order _ _ (by simp [SameWarp, SameCta, twoWarps, Launch.threads]) h
  · exact different_warps_no_order _ _ (by simp [SameWarp, SameCta, twoWarps, Launch.threads]) h

-- The same numerical lane/column in different CTAs denotes different Tensor Memory.
def separateCtas : Launch := { grid := 2, block := 32, params := fun _ => none, sharedBase := 0,
                               clusterSize := 1 }
def separate : Execution where
  tr := fun g => if g = 0 then [mmaAt 0 0] else if g = 32 then [mmaAt 1 0] else []
  rf := fun _ _ => none

theorem separate_cell {e : EvId} {cell : TcMma.Cell} (h : separate.MmaCell e cell) :
    (e = (0, 0) ∧ cell.cta = 0) ∨ (e = (32, 0) ∧ cell.cta = 1) := by
  obtain ⟨d, s, accum, mask, row, col, ⟨pc, h⟩, hw⟩ := h
  have hc := TcMma.resultCell_cta (TcMma.writeCell_resultCell hw)
  obtain ⟨g, i⟩ := e
  by_cases h0 : g = 0
  · subst g
    cases i with
    | zero =>
      simp only [Execution.get, separate, mmaAt, ite_true, List.getElem?_cons_zero,
        Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at h
      obtain ⟨-, -, rfl, -, -⟩ := h
      exact .inl ⟨rfl, by rcases hc with hc | hc <;> exact hc⟩
    | succ i => simp [Execution.get, separate] at h
  · by_cases h32 : g = 32
    · subst g
      cases i with
      | zero =>
        simp only [Execution.get, separate, mmaAt, ite_eq_right h0, ite_true,
          List.getElem?_cons_zero,
          Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at h
        obtain ⟨-, -, rfl, -, -⟩ := h
        exact .inr ⟨rfl, by rcases hc with hc | hc <;> exact hc⟩
      | succ i => simp [Execution.get, separate] at h
    · simp [Execution.get, separate, h0, h32] at h

theorem separate_write {e : EvId} {cell : TcMma.Cell}
    (h : TcMma.TmemWrite separateCtas separate e cell) : separate.MmaCell e cell := by
  apply TcMma.tmemWrite_of_no_store _ _ _ h
  · rintro ⟨g, i⟩ a vals sh ⟨pc, ht⟩
    by_cases h0 : g = 0
    · subst g; cases i <;> simp [Execution.get, separate, mmaAt] at ht
    · by_cases h32 : g = 32
      · subst g; cases i <;> simp [Execution.get, separate, mmaAt] at ht
      · simp [Execution.get, separate, h0, h32] at ht
  · rintro ⟨g, i⟩ c ⟨pc, ht⟩
    by_cases h0 : g = 0
    · subst g; cases i <;> simp [Execution.get, separate, mmaAt] at ht
    · by_cases h32 : g = 32
      · subst g; cases i <;> simp [Execution.get, separate, mmaAt] at ht
      · simp [Execution.get, separate, h0, h32] at ht
  · rintro ⟨g, i⟩ s ⟨pc, ht⟩
    by_cases h0 : g = 0
    · subst g; cases i <;> simp [Execution.get, separate, mmaAt] at ht
    · by_cases h32 : g = 32
      · subst g; cases i <;> simp [Execution.get, separate, mmaAt] at ht
      · simp [Execution.get, separate, h0, h32] at ht

theorem separate_cta_writes_allowed : TcMma.WritesSafe separateCtas separate := by
  intro e f cell he hf
  replace he := separate_write he
  replace hf := separate_write hf
  rcases separate_cell he with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
    rcases separate_cell hf with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
  all_goals first
    | exact .inl rfl
    | omega

/-- The MMA of CTA 1 does not write CTA 0's cell: a read of that cell has no other writer. -/
theorem other_cta_does_not_overwrite {e : EvId}
    (h : TcMma.TmemWrite separateCtas separate e cell0) : e = (0, 0) := by
  rcases separate_cell (separate_write h) with ⟨rfl, -⟩ | ⟨-, hc⟩
  · rfl
  · cases hc

namespace Handoff

-- The loading thread does not poll the mbarrier; the waiting thread hands completion
-- to it through a CTA barrier. These are relation-level fixtures.
private def handoffLanes : List (Nat × EvId) := (List.range 32).map fun g =>
  (g, (g, if g = 0 then 3 else if g = 2 then 1 else 0))

private def handoffState : CtaBarrier.State := {
  slots := fun id => if id = 0 then { generation := 1 } else {} }

def Y : Execution where
  tr := fun g => if g = 0 then [mma 0, ⟨1, .tc (.commit (TcCommit.unicast mb))⟩,
    ⟨2, .wait mb 0 true⟩, ⟨3, .bar 0⟩]
    else if g = 1 then [⟨3, .bar 0⟩, ⟨4, .tc (.ld 0 [] .s32x32b)⟩]
    else if g = 2 then [⟨5, .mbInit mb 1⟩, ⟨3, .bar 0⟩]
    else if g < 32 then [⟨3, .bar 0⟩] else []
  rf := fun _ _ => none

  async := {
    mmaOperands := fun i => if i == (0, 0) then some ⟨[], []⟩ else none
    mmaDone := fun i => i == (0, 0) }
  tcNotified := fun i => if i = (0, 1) then {0} else ∅
  barriers c := if c = 0 then [.arrival 0 0 none handoffLanes] else []
  objects m := if m = mb then
    match MBarrier.replay none [(.thread (2, 0), .init 1),
      (.async (0, 1) (.tcNotify 0), .arrive 1 0), (.thread (0, 2), .pollParity 0 true)] with
    | .ok xs => xs
    | .error _ => []
    else []

theorem wait_to_consumer : baseCausality launch Y (0, 2) (1, 1) := by
  apply Relation.TransGen.single
  refine .inr (.inl ⟨by simp [SameCta, launch, Launch.threads], 0, 3, 0, ?_, ?_, by decide, by
    decide, by decide⟩)
  · refine ⟨by decide, ⟨none, 3, _, rfl⟩, 0, {}, 0, none, handoffLanes, 0,
      rfl, rfl, by decide, rfl, handoffState, rfl⟩
  · refine ⟨by decide, ⟨none, 3, rfl⟩, 0, {}, 0, none, handoffLanes, 1,
      rfl, rfl, by decide, rfl, handoffState, rfl⟩

theorem nonwaiting_consumer_sees_mma : TcMma.DoneBefore launch Y (0, 0) (1, 1) := by
  refine .inl ⟨(0, 2), .cta, ?_, ⟨⟨by decide, by decide, rfl⟩, ⟨by decide, by decide, rfl⟩⟩,
    wait_to_consumer⟩
  refine ⟨_, mb, ⟨(0, 1), TcCommit.unicast mb, 0, rfl, ⟨rfl, by decide,
    .inl ⟨0, spec 0, false, masks, ⟨0, rfl⟩⟩, _, ⟨1, rfl⟩⟩,
    ⟨1, rfl⟩, TcCommit.target_unicast rfl, by simp [Y]⟩, ⟨2, 0, rfl⟩, ?_⟩
  exact ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      fun _ _ _ h2 _ => absurd h2 (by omega)⟩

end Handoff

end
end PTX.Tests.TmemWriters
