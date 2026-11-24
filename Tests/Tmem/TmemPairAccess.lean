-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemRun

namespace PTX.Tests.TmemPairAccess
open Tmem.Pair
noncomputable section

private def L : Launch := { grid := 2, block := 32, clusterSize := 2, params := fun _ => none }
private def a : Event := ⟨0, .tc (.resource .two (some ⟨.shared, 0, 0⟩) (.alloc 32))⟩
private def d : Event := ⟨1, .tc (.resource .two none (.dealloc 0 32))⟩
private def X : Execution := {
  tr := fun _ => [a, d, a, d], rf := fun _ _ => none }
private def request (i : Nat) : Requests :=
  ⟨⟨0, 0, fun _ => i, 0, some ⟨.shared, 0, 0⟩, .alloc 32⟩, .two, .alloc 32 0⟩

-- The first lifetime ends at the first matching attempt, with no completed pair record.
example : OwnRelease L X (request 0) (0, 1) := by
  refine ⟨32, 0, 1, rfl, ⟨.two, rfl⟩, .inl ⟨0, rfl, by decide, ?_⟩⟩
  intro f pc _ _ _ hf
  change 0 < f.2 at hf
  change 1 ≤ f.2
  omega

-- Address reuse does not make the first lifetime's release become the later one.
example : ¬ OwnRelease L X (request 0) (0, 3) := by
  rintro ⟨n, base, pc, he, _, ⟨lane, hg, _, hfirst⟩ | ⟨-, hw⟩⟩
  swap
  · exact hw rfl
  have hn : n = 32 := by cases he; rfl
  have hb : base = 0 := by cases he; rfl
  subst n
  subst base
  have hle := hfirst (0, 1) 1 .two rfl rfl (by change 0 < 1; decide)
  omega

example : OwnRelease L X (request 2) (0, 3) := by
  refine ⟨32, 0, 1, rfl, ⟨.two, rfl⟩, .inl ⟨0, rfl, by decide, ?_⟩⟩
  intro f pc _ _ _ hf
  change 2 < f.2 at hf
  change 3 ≤ f.2
  omega

-- Any warp of the CTA may release an allocation (§9.7.18.5 Table 55): a matching deallocation
-- by warp 1 is a release attempt of warp 0's allocation.
private def L2 : Launch := { grid := 1, block := 64, params := fun _ => none }
private def X2 : Execution := {
  tr := fun g => if g = 0 then [a] else if g = 32 then [d] else [], rf := fun _ _ => none }
example : OwnRelease L2 X2 (request 0) (32, 0) :=
  ⟨32, 0, 1, rfl, ⟨.two, rfl⟩, .inr ⟨rfl, by decide⟩⟩

-- A peer-wait/return or merely preceding the release does not replace wait::ld.
example (Y : Execution) (e d : EvId) (a : Nat) (vals : List Value)
    (sh : TcShape) (hl : Y.TLd e a vals sh) (hn : ∀ w, ¬ Y.WaitLd w) :
    ¬ TcMma.CompletedBefore L Y e d := by
  intro h
  obtain ⟨w, hw, _⟩ := h.1 ⟨a, vals, sh, hl⟩
  exact hn w hw

end
end PTX.Tests.TmemPairAccess
