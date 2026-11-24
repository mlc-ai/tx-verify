-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Mathlib.Tactic

/-!
# Litmus tests of fences (MEM-RELEASE-ACQUIRE, MEM-FENCE-SC, MEM-MODEL-CAUSALITY)

* §8.10.6 Message Passing: T0 `st [data], 1; fence.sys; st.relaxed.sys [flag], 1`, T1
  `ld.relaxed.sys [flag]; fence.sys; ld [data]`. When the flag load reads T0's flag store, the
  release pattern "F1; W2" synchronizes with the acquire pattern "R1; F2", so the data load
  cannot read the initial `data` (forbidden outcome). When the flag load reads the initial flag,
  nothing synchronizes the threads and reading the initial `data` is not excluded (allowed).
* The same with `fence.cta` in two CTAs: the fences' scopes do not include the other thread, so
  the patterns do not synchronize.
* §8.10.6 Store Buffering with `fence.sc.sys`: whichever order the Fence-SC order chooses, one of
  the two loads must read the other thread's store, so both reading 0 is excluded. With
  `fence.acq_rel` in their place, both reading 0 is not excluded.
* The bytes an async proxy fence orders (`AsyncFenceCovers`).
-/

namespace PTX.Tests.FenceLitmus
noncomputable section

/-- Two threads in two CTAs and two clusters; `.sys` includes both, `.cta` neither. -/
private def L : Launch := { grid := 2, block := 1, params := fun _ => none }
private def bytes (n : Nat) : List Byte := (Value.bits 32 (BitVec.ofNat 64 n)).toBytes
private def x : Loc := ⟨.global, 0, 0⟩
private def y : Loc := ⟨.global, 0, 4⟩
/-- `st.global.u32` / `ld.global.u32` (weak) of `x`. -/
private def xA : Acc := { loc := x, size := 4 }
/-- `st.relaxed.sys` / `ld.relaxed.sys` of `y`. -/
private def yR : Acc := { loc := y, size := 4, relaxed := true, scope := .sys }

/-- The baseCausality steps other than program order and `FenceSync` cannot hold in an execution of
`L` without barrier, mbarrier or release/acquire events. -/
private theorem baseCausality_same_thread {X : Execution}
    (hw : ∀ e a bs, X.MemWrites (.thread e) a bs → a.release = false)
    (harr : ∀ e m tx c r s pc, X.get e ≠ some ⟨pc, .arrive m tx c r s⟩)
    (hf : ∀ e f, FenceSync L X e f → e.1 = f.1) {e f : EvId} (h : baseCausality L X e f) :
    e.1 = f.1 := by
  have step : ∀ e f, (po X e f ∨ CtaBarSync L X e f ∨ MSync L X e f ∨ ClusterSync L X e f ∨
      WarpBarSync L X e f ∨ synchronizesWith L X e f ∨ FenceSync L X e f) → e.1 = f.1 := by
    intro e f hs
    rcases hs with hp | ⟨⟨-, -, hc⟩, -⟩ | ⟨x', w, m, rs, as, ⟨tx, cnt, pc, hx⟩, -⟩ |
      ⟨⟨h1, h2, hc⟩, -⟩ | ⟨i, j, ⟨⟨⟨-, -, hc⟩, -⟩, -⟩, -⟩ | ⟨a, -, bs, -, hwr, -, hrel, -⟩ | hfs
    · exact hp.1
    · simpa [L] using hc
    · exact absurd hx (harr _ _ _ _ _ _ _)
    · have h1' : e.1 < 2 := by simpa [L, Launch.threads] using h1
      have h2' : f.1 < 2 := by simpa [L, Launch.threads] using h2
      obtain ⟨a, _⟩ := e
      obtain ⟨b, _⟩ := f
      simp only at h1' h2' hc ⊢
      interval_cases a <;> interval_cases b <;> first | rfl | (revert hc; decide)
    · simpa [L] using hc
    · rw [hw _ _ _ hwr] at hrel; cases hrel
    · exact hf _ _ hfs
  induction h with
  | single hs => exact step _ _ hs
  | tail _ hs ih => exact ih.trans (step _ _ hs)

/-- Without reads from writes and without `fence.sc`, there is no fence synchronization. -/
private theorem no_fenceSync {X : Execution} (hrf : ∀ r k, X.rf r k = none)
    (hsc : ∀ e s, ¬ X.ThreadFence e .sc s) (e f : EvId) : ¬ FenceSync L X e f := by
  rintro (⟨w, r, a, b, bs, cs, se, sf, -, -, -, -, -, -, -, -, hpos, -, -, -, -, hk⟩ |
    ⟨⟨s, -, hs, -⟩, -⟩)
  · have := hk 0 hpos
    rw [hrf] at this
    cases this
  · exact hsc _ _ hs

/-! ## Message passing with fences -/

/-- T0: `st [x], 1; fence.acq_rel.sc'; st.relaxed.sys [y], 1`. T1: `ld.relaxed.sys [y]` reading
1 from T0's store when `seen` (else 0 from W0), `fence.acq_rel.sc'`, `ld [x]` reading 0 from W0. -/
private def mp (sc : MbarScope) (seen : Bool) : Execution where
  tr g := if g = 0 then [⟨0, .wr xA (bytes 1)⟩, ⟨1, .fence .acqRel sc⟩, ⟨2, .wr yR (bytes 1)⟩]
    else if g = 1 then [⟨0, .rd yR ((bytes (if seen then 1 else 0)).map some)⟩,
      ⟨1, .fence .acqRel sc⟩, ⟨2, .rd xA ((bytes 0).map some)⟩]
    else []
  rf r _ := if seen ∧ r = .thread (1, 0) then some (.thread (0, 2)) else none

private theorem mp_writes {sc : MbarScope} {seen : Bool} {e : EvId} {a : Acc} {bs : List Byte}
    (h : (mp sc seen).MemWrites (.thread e) a bs) : a.release = false := by
  obtain ⟨g, i⟩ := e
  rcases h with ⟨pc, h⟩ | ⟨o, pc, h⟩ <;> simp only [Execution.get, mp] at h <;>
    split_ifs at h <;> rcases i with _ | _ | _ | i <;> simp at h <;>
    (try obtain ⟨-, rfl, -⟩ := h) <;> rfl

private theorem mp_arrive {sc : MbarScope} {seen : Bool} (e : EvId) (m : Loc) (tx c : Nat)
    (r : Bool) (s : MbarScope) (pc : Nat) :
    (mp sc seen).get e ≠ some ⟨pc, .arrive m tx c r s⟩ := by
  obtain ⟨g, i⟩ := e
  simp only [Execution.get, mp]
  split_ifs <;> rcases i with _ | _ | _ | i <;> simp

private theorem mp_noSc {sc : MbarScope} {seen : Bool} (e : EvId) (s : MbarScope) :
    ¬ (mp sc seen).ThreadFence e .sc s := by
  rintro ⟨pc, h⟩
  obtain ⟨g, i⟩ := e
  simp only [Execution.get, mp] at h
  split_ifs at h <;> rcases i with _ | _ | _ | i <;> simp at h

private theorem po_mp {sc : MbarScope} {seen : Bool} (g : Nat) (hg : g = 0 ∨ g = 1) {i j : Nat}
    (hij : i < j) (hj : j < 3) (hne : ((mp sc seen).get (g, i)).bind Event.acc = none ∨
      ((mp sc seen).get (g, j)).bind Event.acc = none) : po (mp sc seen) (g, i) (g, j) := by
  refine ⟨rfl, hij, by rcases hg with rfl | rfl <;> simp [mp, hj], fun hs => ?_⟩
  rcases hne with h | h
  · have := hs.2 (j - i) le_rfl
    rw [show i + (j - i) = j by omega] at this
    rw [h] at this
    have h1 := hs.1
    simp only [Option.map_none] at this
    rw [this] at h1
    cases h1
  · have h1 := hs.1
    rw [h] at h1
    cases h1

/-- Forbidden: when the flag load reads T0's flag store, the release pattern synchronizes with the
acquire pattern. -/
theorem mp_sync : FenceSync L (mp .sys true) (0, 1) (1, 1) :=
  Or.inl ⟨(0, 2), (1, 0), yR, yR, bytes 1, (bytes 1).map some, .sys, .sys,
    Or.inl ⟨2, by simp [Execution.get, mp]⟩, Or.inl rfl,
    Or.inl ⟨⟨0, by simp [Execution.get, mp]⟩, Or.inl rfl⟩,
    Or.inr ⟨.acqRel, ⟨1, by simp [Execution.get, mp]⟩, rfl, rfl, by decide⟩,
    Or.inr ⟨.acqRel, ⟨1, by simp [Execution.get, mp]⟩, rfl, rfl, by decide⟩,
    ⟨.acqRel, .sys, Or.inl ⟨1, by simp [Execution.get, mp]⟩⟩, rfl, rfl, by decide,
    by simp [MbarScopeIncludes, yR, L, Launch.threads],
    by simp [MbarScopeIncludes, yR, L, Launch.threads],
    by simp [MbarScopeIncludes, L, Launch.threads],
    by simp [MbarScopeIncludes, L, Launch.threads], fun k _ => by simp [mp]⟩

theorem mp_baseCausality : baseCausality L (mp .sys true) (0, 0) (1, 2) :=
  .tail (.tail (.single (Or.inl (po_mp 0 (Or.inl rfl) (by decide) (by decide)
    (Or.inr (by simp [Execution.get, mp, Event.acc]))))) (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr mp_sync)))))))
    (Or.inl (po_mp 1 (Or.inr rfl) (by decide) (by decide)
      (Or.inl (by simp [Execution.get, mp, Event.acc]))))

/-- So the data load reading the initial `data` is rejected by MEM-READ-AXIOMS. -/
example : ¬ Hidden L (mp .sys true) := by
  intro h
  have := h (.thread (1, 2)) xA ((bytes 0).map some) 0 (.thread (0, 0)) xA (bytes 1)
    (Or.inl ⟨2, by simp [Execution.get, mp]⟩) (by decide) (Or.inl ⟨0, by simp [Execution.get, mp]⟩)
    (by simp [Acc.Covers, Loc.InRange, xA, Loc.at]) (.direct (.inl mp_baseCausality))
  simp [mp] at this

/-- Allowed: when the flag load reads the initial flag, no edge crosses the threads, so the data
store is not before the data load. -/
example : ¬ modelCausality L (mp .sys false) x (.thread (0, 0)) (.thread (1, 2)) := by
  rintro (hb | ⟨_, _, _, _, hr, _, _, _, _⟩)
  · exact absurd (baseCausality_same_thread (fun _ _ _ => mp_writes) mp_arrive
      (fun e f hf => absurd hf (no_fenceSync (by simp [mp]) mp_noSc e f)) hb) (by decide)
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, hzero, _⟩ := hr
    cases hzero

/-- Scope mismatch: with `fence.cta` in two CTAs the fences' scopes do not include each other's
thread, so the release pattern does not synchronize with the acquire pattern. -/
example : ¬ FenceSync L (mp .cta true) (0, 1) (1, 1) := by
  rintro (⟨w, r, a, b, bs, cs, se, sf, hw, -, -, hrel, -, -, -, -, -, -, -, hse, -, -⟩ |
    ⟨⟨s, -, hs, -⟩, -⟩)
  · rcases hrel with ⟨rfl, hr, -⟩ | ⟨sem, ⟨pc, h⟩, -⟩
    · rw [mp_writes hw] at hr; cases hr
    · simp [Execution.get, mp] at h
      obtain ⟨-, -, rfl⟩ := h
      simp [MbarScopeIncludes, SameCta, L, Launch.threads] at hse
  · exact mp_noSc _ _ hs

/-! ## Store buffering with `fence.sc` -/

/-- T0: `st [x], 1; fence.sem.sys; ld [y]`, T1: `st [y], 1; fence.sem.sys; ld [x]`, both loads
reading 0 from W0, with the Fence-SC order `rel`. -/
private def sb (sem : FenceSem) (rel : EvId → EvId → Prop) : Execution where
  tr g := if g = 0 then [⟨0, .wr xA (bytes 1)⟩, ⟨1, .fence sem .sys⟩,
      ⟨2, .rd { xA with loc := y } ((bytes 0).map some)⟩]
    else if g = 1 then [⟨0, .wr { xA with loc := y } (bytes 1)⟩, ⟨1, .fence sem .sys⟩,
      ⟨2, .rd xA ((bytes 0).map some)⟩]
    else []
  rf _ _ := none
  fenceSC := rel

private theorem po_sb {sem : FenceSem} {rel : EvId → EvId → Prop} (g : Nat) (hg : g = 0 ∨ g = 1)
    {i j : Nat} (hij : i < j) (hj : j < 3)
    (hne : ((sb sem rel).get (g, i)).bind Event.acc = none ∨
      ((sb sem rel).get (g, j)).bind Event.acc = none) : po (sb sem rel) (g, i) (g, j) := by
  refine ⟨rfl, hij, by rcases hg with rfl | rfl <;> simp [sb, hj], fun hs => ?_⟩
  rcases hne with h | h
  · have := hs.2 (j - i) le_rfl
    rw [show i + (j - i) = j by omega, h] at this
    have h1 := hs.1
    simp only [Option.map_none] at this
    rw [this] at h1
    cases h1
  · have h1 := hs.1
    rw [h] at h1
    cases h1

private theorem sc_strong {rel : EvId → EvId → Prop} (g h : Nat) (hg : g = 0 ∨ g = 1)
    (hh : h = 0 ∨ h = 1) : ScStrong L (sb .sc rel) (g, 1) (h, 1) := by
  refine ⟨.sys, .sys, ⟨1, ?_⟩, ⟨1, ?_⟩, Or.inr ⟨?_, ?_⟩⟩ <;>
    rcases hg with rfl | rfl <;> rcases hh with rfl | rfl <;>
    simp [Execution.get, sb, MbarScopeIncludes, L, Launch.threads]

/-- The path from one thread's store through its `fence.sc`, the other thread's `fence.sc` and to
the other thread's load. -/
private theorem sb_baseCausality {rel : EvId → EvId → Prop} (g h : Nat) (hg : g = 0 ∨ g = 1)
    (hh : h = 0 ∨ h = 1) (hr : rel (g, 1) (h, 1)) : baseCausality L (sb .sc rel) (g, 0) (h, 2) := by
  have p0 : po (sb .sc rel) (g, 0) (g, 1) := po_sb g hg (by decide) (by decide)
    (Or.inr (by rcases hg with rfl | rfl <;> simp [Execution.get, sb, Event.acc]))
  have p1 : po (sb .sc rel) (h, 1) (h, 2) := po_sb h hh (by decide) (by decide)
    (Or.inl (by rcases hh with rfl | rfl <;> simp [Execution.get, sb, Event.acc]))
  have s : FenceSync L (sb .sc rel) (g, 1) (h, 1) := Or.inr ⟨sc_strong g h hg hh, hr⟩
  exact .tail (.tail (.single (Or.inl p0)) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr s))))))) (Or.inl p1)

/-- Forbidden: with `fence.sc.sys`, any Fence-SC order that MEM-FENCE-SC accepts orders one
thread's store before the other thread's load, so both loads reading 0 is rejected. -/
theorem sb_sc (rel : EvId → EvId → Prop)
    (hok : FenceScOk L (sb .sc rel) (baseCausality L (sb .sc rel))) :
    ¬ Hidden L (sb .sc rel) := by
  intro h
  rcases hok.total (0, 1) (1, 1) (sc_strong 0 1 (Or.inl rfl) (Or.inr rfl)) (by decide) with
    hr | hr
  · have := h (.thread (1, 2)) xA ((bytes 0).map some) 0 (.thread (0, 0)) xA (bytes 1)
      (Or.inl ⟨2, by simp [Execution.get, sb]⟩) (by decide)
      (Or.inl ⟨0, by simp [Execution.get, sb]⟩) (by simp [Acc.Covers, Loc.InRange, xA, Loc.at])
      (.direct (.inl (sb_baseCausality 0 1 (Or.inl rfl) (Or.inr rfl) hr)))
    simp [sb] at this
  · have := h (.thread (0, 2)) { xA with loc := y } ((bytes 0).map some) 0 (.thread (1, 0))
      { xA with loc := y } (bytes 1) (Or.inl ⟨2, by simp [Execution.get, sb]⟩) (by decide)
      (Or.inl ⟨0, by simp [Execution.get, sb]⟩) (by simp [Acc.Covers, Loc.InRange, xA, y, Loc.at])
      (.direct (.inl (sb_baseCausality 1 0 (Or.inr rfl) (Or.inl rfl) hr)))
    simp [sb] at this

/-- An execution without `fence.sc` accepts any Fence-SC order. -/
example (rel : EvId → EvId → Prop) :
    FenceScOk L (sb .acqRel rel) (baseCausality L (sb .acqRel rel)) :=
  fenceScOk_of_noSc fun e s ⟨pc, h⟩ => by
    obtain ⟨g, i⟩ := e
    simp only [Execution.get, sb] at h
    split_ifs at h <;> rcases i with _ | _ | _ | i <;> simp at h

/-- Allowed: with `fence.acq_rel.sys` instead, nothing synchronizes the threads, so T0's store is
not before T1's load and both loads may read 0. -/
example (rel : EvId → EvId → Prop) :
    ¬ modelCausality L (sb .acqRel rel) x (.thread (0, 0)) (.thread (1, 2)) := by
  intro h
  have hv : baseCausality L (sb .acqRel rel) (0, 0) (1, 2) := by
    rcases h with hb | ⟨_, _, _, _, hr, _, _, _, _⟩
    · exact hb
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, hzero, _⟩ := hr
      cases hzero
  have hsc : ∀ e s, ¬ (sb .acqRel rel).ThreadFence e .sc s := fun e s ⟨pc, h⟩ => by
    obtain ⟨g, i⟩ := e
    simp only [Execution.get, sb] at h
    split_ifs at h <;> rcases i with _ | _ | _ | i <;> simp at h
  refine absurd (baseCausality_same_thread ?_ ?_ (fun e f hf => absurd hf (no_fenceSync
    (fun _ _ => rfl) hsc e f)) hv) (by decide)
  · rintro ⟨g, i⟩ a bs (⟨pc, h⟩ | ⟨o, pc, h⟩) <;> simp only [Execution.get, sb] at h <;>
      split_ifs at h <;> rcases i with _ | _ | _ | i <;> simp at h <;>
      (try obtain ⟨-, rfl, -⟩ := h) <;> rfl
  · rintro ⟨g, i⟩ m tx c r s pc
    simp only [Execution.get, sb]
    split_ifs <;> rcases i with _ | _ | _ | i <;> simp

/-! ## Async proxy fences -/

private def L2 : Launch := { grid := 4, block := 32, clusterSize := 2, params := fun _ => none }
-- `.global` orders global bytes only; `.shared::cta` the fence's own CTA; `.shared::cluster` the
-- CTAs of its cluster; no state space every byte.
example : AsyncFenceCovers L2 (some .global) 0 ⟨.global, 0, 8⟩ := rfl
example : ¬ AsyncFenceCovers L2 (some .global) 0 ⟨.shared, 0, 8⟩ := by simp [AsyncFenceCovers]
example : AsyncFenceCovers L2 (some (.shared .cta)) 33 ⟨.shared, 1, 8⟩ := by
  simp [AsyncFenceCovers, L2]
example : ¬ AsyncFenceCovers L2 (some (.shared .cta)) 0 ⟨.shared, 1, 8⟩ := by
  simp [AsyncFenceCovers, L2]
example : AsyncFenceCovers L2 (some (.shared .cluster)) 0 ⟨.shared, 1, 8⟩ :=
  ⟨rfl, by decide, by decide, by decide⟩
example : ¬ AsyncFenceCovers L2 (some (.shared .cluster)) 0 ⟨.shared, 2, 8⟩ :=
  fun ⟨_, _, _, h⟩ => absurd h (by decide)
example (l : Loc) : AsyncFenceCovers L2 none 0 l := trivial

end
end PTX.Tests.FenceLitmus
