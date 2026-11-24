-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairRecord
import Lemmas.Tmem.AllocResult
public import Mathlib.Tactic.FinCases

/-! The allocation-result rule (OBJ-TMEM-ALLOC-RESULT): an allocation's column is selected when
it completes, not when it is requested.

Litmus (§9.7.18.7.1: "The tcgen05.alloc blocks if the requested amount of Tensor Memory is not
available and unblocks as soon as the requested amount of Tensor Memory becomes available for
allocation."). In one CTA, warp 0 holds all 512 columns; warp 1 then requests 32 columns. No
column is available, so warp 1 waits: the execution `held` with its request pending satisfies
the Tensor Memory conditions of `Consistent` (provenance and replay, blocking, completion
prefixes and the result rule). Once warp 0 releases its columns, warp 1's request completes
with column 0 and lane 0 stores that address (`released`, which extends `held`). -/

namespace PTX.Tests.TmemAllocResult
open Tmem.Pair
noncomputable section

private def L : Launch := { grid := 1, block := 64, params := fun _ => none }
private def dst : Loc := ⟨.shared, 0, 0⟩
private def dst1 : Loc := ⟨.shared, 0, 4⟩
private def address (col : Nat) : List Byte := (Value.bits 32 (BitVec.ofNat 64 col)).toBytes

private def allocA : Event := ⟨0, .tc (.resource .one (some dst) (.alloc 512))⟩
private def storeA : Event := ⟨0, .wr { loc := dst, size := 4 } (address 0)⟩
private def deallocA : Event := ⟨2, .tc (.resource .one none (.dealloc 0 512))⟩
private def allocB : Event := ⟨1, .tc (.resource .one (some dst1) (.alloc 32))⟩
private def storeB : Event := ⟨1, .wr { loc := dst1, size := 4 } (address 0)⟩

/-- Warp 0's allocation of all 512 columns, its release, and warp 1's allocation. -/
private def rA : Requests := ⟨⟨0, 0, fun _ => 0, 0, some dst, .alloc 512⟩, .one, .alloc 512 0⟩
private def rD : Requests :=
  ⟨⟨0, 0, fun lane => if lane.val = 0 then 2 else 1, 2, none, .dealloc 0 512⟩, .one,
    .dealloc 0 512⟩
private def rB (col : Nat) : Requests :=
  ⟨⟨0, 1, fun _ => 0, 1, some dst1, .alloc 32⟩, .one, .alloc 32 col⟩

/-- Warp 0 holds the columns; warp 1's request is pending. -/
private def held : Execution := {
  tr := fun g => if g = 0 then [allocA, storeA] else if g < 32 then [allocA]
    else if g < 64 then [allocB] else []
  rf := fun _ _ => none
  tmemHistory := fun k => if k = 0 then [rA] else [] }

/-- Warp 0 released its columns; warp 1's allocation completed at column 0. -/
private def released : Execution := {
  tr := fun g => if g = 0 then [allocA, storeA, deallocA] else if g < 32 then [allocA, deallocA]
    else if g = 32 then [allocB, storeB] else if g < 64 then [allocB] else []
  rf := fun _ _ => none
  tmemHistory := fun k => if k = 0 then [rA, rD, rB 0] else [] }

/-! ### No column is available while warp 0 holds all of them -/

-- Completing warp 1's request at any column after warp 0's allocation is blocked: an issued
-- request cannot select a column, so it can only wait.
example (col : Nat) : runRequests {} [rA, rB col] = .blocked := by
  simp only [runRequests, rA, rB, Tmem.perform, Tmem.validColumns, Tmem.available]
  simp [Tmem.disjoint, show 480 < col ∨ col < 512 by omega]

-- After the release, column 0 is available again.
example : runRequests {} [rA, rD, rB 0] =
    .done { previousColumns := some 32, nextLifetime := 2, live := [⟨1, 0, 32⟩] } := by
  decide

-- Two warps requesting 256 columns each from an empty allocator both complete, at the columns
-- the allocator selects at completion.
example : runRequests {}
    [⟨⟨0, 0, fun _ => 0, 0, some dst, .alloc 256⟩, .one, .alloc 256 0⟩,
     ⟨⟨0, 1, fun _ => 0, 1, some dst1, .alloc 256⟩, .one, .alloc 256 256⟩] ≠ .blocked := by
  decide

/-! ### `held`: the pending request -/

private theorem held_get (g j : Nat) : held.get (g, j) =
    (if g = 0 then [allocA, storeA] else if g < 32 then [allocA]
      else if g < 64 then [allocB] else [])[j]? := rfl

private theorem held_tcK {g : Nat} (hg : g < 64) : held.TcK (g, 0) 0 := by
  refine ⟨⟨if g < 32 then allocA else allocB, ?_, ?_⟩, by simp⟩
  · rw [held_get]; split_ifs <;> first | rfl | omega
  · split_ifs <;> rfl

private theorem rA_valid (X : Execution) (hget : ∀ lane : Fin 32, X.get (lane.val, 0) = some allocA)
    (hk : ∀ lane : Fin 32, X.TcK (lane.val, 0) 0) : rA.Valid L X := by
  refine ⟨by decide, rfl, by decide, by decide, fun lane => ?_, 0, fun lane => ?_⟩
  · simpa [WarpRequest.event, rA, L, allocA] using hget lane
  · simpa [WarpRequest.event, rA, L] using hk lane

private theorem held_rA : rA.Valid L held :=
  rA_valid held (fun lane => by rw [held_get]; split_ifs <;> first | rfl | omega)
    (fun lane => held_tcK (by omega))

private theorem held_covered_warp0 {g : Nat} (hg : g < 32) : Covered L held (g, 0) :=
  ⟨[rA.own], .inl ⟨0, rA, by simp [held], rfl, rfl⟩, rA.own, List.mem_singleton_self _,
    ⟨g, hg⟩, by simp [WarpRequest.event, rA, L]⟩

/-- Warp 1's request is not covered: it is pending. -/
theorem held_pending (lane : Nat) (h : lane < 32) : ¬ Covered L held (32 + lane, 0) := by
  rintro ⟨ws, ⟨key, x, hx, -, rfl⟩ | ⟨q, hq, -⟩, w, hw, l, hl⟩
  · by_cases hk : key = 0
    · subst hk
      simp only [held, ite_true, List.mem_singleton] at hx
      subst hx
      rw [List.mem_singleton.mp hw] at hl
      simp [WarpRequest.event, rA, L] at hl
      omega
    · simp [held, hk] at hx
  · cases hq

example : HistoriesOk L held := by
  refine ⟨fun key => ?_, (fun q hq => by cases hq), List.Pairwise.nil⟩
  by_cases hk : key = 0
  · subst hk
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [held, ite_true, List.mem_singleton] at hx
      subst hx
      exact held_rA
    · intro x hx
      simp only [held, ite_true, List.mem_singleton] at hx
      subst hx
      rfl
    · simp only [held, ite_true]
      decide
  · simp [RequestHistory, held, hk, runRequests]

example : Tmem.Pair.Blocking L held := by
  rintro ⟨g, j⟩ pc group d a he hl
  have hlt := len_of_get he
  simp only [held] at hl hlt
  by_cases h0 : g = 0
  · subst h0
    simp at hl hlt
    have hj : j = 0 := by omega
    subst hj
    rw [held_get] at he
    simp only [ite_true, List.getElem?_cons_zero, Option.some.injEq, allocA, Event.mk.injEq,
      Kind.tc.injEq, TcKind.resource.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    intro n hn
    have hEq : Needs L held (0, 0) = resourceNeeds L held (0, 0) .one (.alloc 512) := by
      unfold Needs
      rw [held_get]
      rfl
    rw [hEq] at hn
    have hleader : allocResultNeeds L held (0, 0) (.alloc 512) = [] := rfl
    simp only [resourceNeeds, hleader, List.append_nil, needsIf, tcNeeds, warpLanes,
      List.mem_append, List.mem_map, List.mem_range, List.mem_cons] at hn
    rcases hn with ⟨h, ⟨l, hl, rfl⟩, rfl⟩ | rfl | hn
    · have hl32 : l < 32 := by simpa [warpSize, L] using hl
      have hw : warpLane L 0 l = l := by simp [warpLane, laneOf]
      refine ⟨.thread (l, 0), ?_, 0, by rw [hw], ?_⟩
      · show ∃ ev, held.get (l, 0) = some ev
        rw [held_get]
        split_ifs <;> exact ⟨_, rfl⟩
      · simpa [hw] using held_tcK (g := l) (by omega)
    · exact ⟨0, rA, by simp [held], ⟨0, by decide⟩, by simp [WarpRequest.event, rA, L]⟩
    · have hh : held.tmemHistory (0 / L.block) = [rA] := rfl
      have hr : ¬ ReuseRelease L held (0, 0) 0 := by
        rintro ⟨i, r, d, n, base, b', n', hi, -, -, -, hj, -⟩
        rw [hh] at hi
        have : i < 1 := (List.getElem?_eq_some_iff.mp hi).1
        omega
      rw [hh] at hn
      split_ifs at hn
      · simp only [List.length_singleton, List.range_one, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, hr, ite_false, List.mem_singleton] at hn
        subst hn
        exact held_covered_warp0 (by decide)
      · cases hn
  · split_ifs at hl <;> simp at hl

example : CompletionClosed L held := by
  intro ws hws earlier he w group hv hb
  · rcases hws with ⟨key, x, hx, -, rfl⟩ | ⟨q, hq, -⟩
    · by_cases hk : key = 0
      · subst hk
        simp only [held, ite_true, List.mem_singleton] at hx
        subst hx
        rw [List.mem_singleton.mp he] at hb
        have := hb.2.2 0
        simp [rA] at this
      · simp [held, hk] at hx
    · cases hq

/-- The result rule holds: warp 0's lane 0 stored the column of its completed allocation, and
warp 1's pending request has no column and no store yet. -/
example : ResultOk L held := by
  intro i pc group d n he key x base hx hwi hwa pc' a bs hs
  by_cases hk : key = 0
  · subst hk
    simp only [held, ite_true, List.mem_singleton] at hx
    subst hx
    simp only [rA] at hwa
    cases hwa
    have hi : i = (0, 0) := by rw [← hwi]; simp [WarpRequest.event, rA, L]
    subst hi
    rw [held_get] at hs
    simp [storeA] at hs
    rw [← hs.2.2]
    rfl
  · simp [held, hk] at hx

/-! ### `released`: the release lets the request complete -/

private theorem released_get (g j : Nat) : released.get (g, j) =
    (if g = 0 then [allocA, storeA, deallocA] else if g < 32 then [allocA, deallocA]
      else if g = 32 then [allocB, storeB] else if g < 64 then [allocB] else [])[j]? := rfl

example : held.le released := by
  refine ⟨fun g => ?_, fun _ _ _ => rfl, AsyncCopy.Extends.refl _,
    fun _ => List.prefix_refl _, fun _ => List.prefix_refl _, fun _ => List.prefix_refl _,
    fun _ => Clc.Extends.refl _, ⟨fun _ _ h => h, fun _ _ h => h⟩,
    TensorCopy.snapshotExtends_refl _, TensorStore.snapshotExtends_refl _,
    ⟨fun k => ?_, List.prefix_refl _⟩,
    fun _ _ _ _ _ _ => rfl, fun _ => Finset.Subset.refl _⟩
  · simp only [held, released]
    split_ifs <;> simp
  · simp only [held, released]
    split_ifs <;> simp

/-- Warp 1's request is covered once it completes. -/
example (lane : Nat) (h : lane < 32) : Covered L released (32 + lane, 0) :=
  ⟨[(rB 0).own], .inl ⟨0, rB 0, by simp [released], rfl, rfl⟩, (rB 0).own,
    List.mem_singleton_self _, ⟨lane, h⟩, by simp [WarpRequest.event, rB, L]⟩

example : ∀ key, runRequests {} (released.tmemHistory key) ≠ .blocked := by
  intro key
  by_cases hk : key = 0
  · subst hk
    simp only [released, ite_true]
    decide
  · simp [released, hk, runRequests]

/-- Lane 0 of warp 1 stored column 0, the column of its completed allocation. -/
example : ResultOk L released := by
  intro i pc group d n he key x base hx hwi hwa pc' a bs hs
  by_cases hk : key = 0
  · subst hk
    simp only [released, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · simp only [rA] at hwa
      cases hwa
      have hi : i = (0, 0) := by rw [← hwi]; simp [WarpRequest.event, rA, L]
      subst hi
      rw [released_get] at hs
      simp [storeA] at hs
      rw [← hs.2.2]
      rfl
    · simp [rD] at hwa
    · simp only [rB] at hwa
      cases hwa
      have hi : i = (32, 0) := by rw [← hwi]; simp [WarpRequest.event, rB, L]
      subst hi
      rw [released_get] at hs
      simp [storeB] at hs
      rw [← hs.2.2]
      rfl
  · simp [released, hk] at hx

/-- A store of another column than the completed allocation's is excluded. -/
example : ¬ ResultOk L { released with
    tr := fun g => if g = 32 then [allocB, ⟨1, .wr { loc := dst1, size := 4 } (address 64)⟩]
      else released.tr g } := by
  intro h
  have := h (32, 0) 1 .one (some dst1) 32 rfl 0 (rB 0) 0 (by simp [released])
    (by simp [WarpRequest.event, rB, L]) rfl 1 _ _ rfl
  exact absurd this (by decide)

/-! ### Returning the allocation address to a participating lane -/

private def loadAddress : Event := ⟨3, .rd { loc := dst, size := 4 } [none, none, none, none]⟩

private def readback : Execution := { held with tr := fun g =>
  if g = 1 ∨ g = 33 then [allocA, loadAddress] else held.tr g }

-- The allocator's representative store hands off each result byte to lane 1.
private theorem resultBefore (k : Fin 4) :
    AllocResultBefore L readback (dst.at k.val) (0, 1) (1, 1) := by
  have hbyte : dst.InRange 4 (dst.at k.val) := ⟨rfl, rfl, by simp [Loc.at], by
    simp [Loc.at, dst]⟩
  refine ⟨0, dst, { loc := dst, size := 4 }, [none, none, none, none], ?_,
    by decide, hbyte, ⟨3, rfl⟩, hbyte⟩
  refine ⟨by unfold SameWarp SameCta; decide, rfl, rfl, rfl,
    0, 0, .one, 512, 0, address 0, rfl, rfl, rfl, ?_, ?_, rfl⟩
  all_goals exact ⟨⟨allocA, rfl, rfl⟩, rfl⟩

example (k : Fin 4) : modelCausality L readback (dst.at k.val)
    (.thread (0, 1)) (.thread (1, 1)) :=
  modelCausality.of_allocResultBefore L (resultBefore k)

-- Identical instruction operands and ordinal in another warp do not share the result.
example : ¬ AllocResultBefore L readback dst (0, 1) (33, 1) := by
  rintro ⟨_, _, _, _, ⟨hsame, _⟩, _⟩
  exact (by unfold SameWarp SameCta; decide : ¬ SameWarp L 0 33) hsame

example : ¬ AllocResultBefore L readback dst1 (0, 1) (1, 1) := by
  rintro ⟨_, loc, _, _, ⟨_, _, _, _, j, site, group, n, _, _, hj, ha, _⟩, _, hb, _⟩
  have hj0 : j = 0 := by simp at hj; omega
  subst j
  change some allocA = some ⟨site, .tc (.resource group (some loc) (.alloc n))⟩ at ha
  simp [allocA] at ha
  obtain ⟨_, _, rfl, _⟩ := ha
  exact (by decide : ¬ dst.InRange 4 dst1) hb

end
end PTX.Tests.TmemAllocResult
