-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Tmem.TmemPairHistory

namespace PTX.Tests.TmemPairCoverage
open Tmem.Pair
noncomputable section

private def L : Launch := { grid := 2, block := 32, params := fun _ => none, clusterSize := 2 }
private def pending (a : Tmem.Request) : Execution := {
  tr := fun _ => [⟨0, .tc (.resource .two none a)⟩], rf := fun _ _ => none }
private def advanced (a : Tmem.Request) : Execution := {
  tr := fun g => if g < 64 then [⟨0, .tc (.resource .two none a)⟩, ⟨1, .exit⟩] else [],
  rf := fun _ _ => none }

private theorem uncovered (a : Tmem.Request) (i : EvId) : ¬ Covered L (advanced a) i := by
  rintro ⟨_, ⟨_, _, hr, _⟩ | ⟨_, hr, _⟩, _⟩ <;> cases hr

-- A partial allocation may await its peer. The rule does not force completion
-- merely because the requested allocation event is the last recorded event.
example : AllocBlocking L (pending (.alloc 32)) := by
  intro i pc group dst n he hn
  change i.2 + 1 < 1 at hn
  omega

-- Advancing past allocation without its joint resource record is forbidden.
example : ¬ AllocBlocking L (advanced (.alloc 32)) := by
  intro h
  exact uncovered _ _ (h (0, 0) 0 .two none 32 rfl (by decide))

-- An ordinary dealloc need not wait for its peer before its issuer returns.
-- Optional blocking choices must be represented separately, not inferred here.
example : AllocBlocking L (advanced (.dealloc 0 32)) := by
  rintro ⟨g, i⟩ pc group dst n he _
  simp only [Execution.get, advanced] at he
  split_ifs at he
  · rcases i with _ | _ | i <;> simp at he
  · simp at he

example : ¬ Drained L (advanced (.dealloc 0 32)) := by
  intro h
  exact uncovered _ _ (h (0, 0) 0 .two none (.dealloc 0 32) rfl)

-- Even after every thread exits, unfinished collective work prevents Complete.
example : ¬ Complete L (advanced (.dealloc 0 32)) := by
  intro h
  exact uncovered _ _ (h.2.2 (0, 0) 0 .two none (.dealloc 0 32) rfl)

-- Existing programs with no allocation-management instructions incur no extra work.
example (X : Execution)
    (h : ∀ i pc group dst action, X.get i ≠ some ⟨pc, .tc (.resource group dst action)⟩) :
    Drained L X := by
  intro i pc group dst action hi
  exact False.elim (h i pc group dst action hi)

-- An issuer returns from a deallocation only once its CTA's allocator has performed its warp's
-- request, whatever its peer-wait choice.
example : ¬ Tmem.Pair.Blocking L (advanced (.dealloc 0 32)) := by
  intro h
  obtain ⟨cta, r, hr, -⟩ := h.performed (i := (0, 0)) (pc := 0) (group := .two) (dst := none)
    (request := .dealloc 0 32) rfl (by decide)
  cases hr

/-- Both CTAs' allocators performed their halves; the halves are not paired. -/
private def halves : Execution := { advanced (.dealloc 0 32) with
  tmemHistory := fun cta => if cta < 2 then
    [⟨⟨cta, 0, fun _ => 0, 0, none, .dealloc 0 32⟩, .two, .dealloc 0 32⟩] else [] }

private theorem halves_event {g i : Nat} {pc : Nat} {group : CtaGroup} {dst : Option Loc}
    {a : Tmem.Request} (he : halves.get (g, i) = some ⟨pc, .tc (.resource group dst a)⟩) :
    g < 64 ∧ i = 0 ∧ group = .two ∧ a = .dealloc 0 32 := by
  simp only [Execution.get, halves, advanced] at he
  split_ifs at he with hg
  · rcases i with _ | _ | i <;> simp at he
    exact ⟨hg, rfl, he.2.1.symm, he.2.2.2.symm⟩
  · simp at he

-- Without the peer wait, the deallocation returns once its own CTA's half is performed.
example : Tmem.Pair.Blocking L halves := by
  rintro ⟨g, i⟩ pc group dst a he _
  obtain ⟨hg, rfl, rfl, rfl⟩ := halves_event he
  have hmw : ¬ Tmem.Pair.MustWait halves (g, 0) := by
    rintro ⟨pc', group', dst', a', he', h⟩
    simp only [he, Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at he'
    obtain ⟨-, rfl, -, rfl⟩ := he'
    simp [halves, advanced] at h
  have hneeds : Needs L halves (g, 0) =
      tcNeeds L halves (g, 0) ++ [Need.cond (Tmem.Pair.Performed L halves (g, 0))] := by
    simp [Needs, he, KindNeeds, resourceNeeds, Tmem.Pair.allocResultNeeds, needsIf, hmw]
  intro n hn
  rw [hneeds, List.mem_append, List.mem_singleton] at hn
  rcases n with f | holds
  · dsimp only
    rcases hn with hn | hn
    · rw [tcNeeds, List.mem_map] at hn
      obtain ⟨h, hmem, heq⟩ := hn
      have hlt : h < 64 := by
        simp only [warpLanes, List.mem_map, List.mem_range] at hmem
        obtain ⟨l, hl, rfl⟩ := hmem
        have hl32 : l < 32 := lt_of_lt_of_le hl (by unfold warpSize; exact Nat.min_le_left _ _)
        have hg' : g % 32 + 32 * (g / 32) = g := Nat.mod_add_div g 32
        simp only [warpLane, laneOf, L]
        omega
      cases heq
      refine ⟨.thread (h, 0), ⟨⟨0, .tc (.resource .two none (.dealloc 0 32))⟩, ?_⟩, 0, rfl, ?_⟩
      · simp [Execution.get, halves, advanced, hlt]
      · refine ⟨⟨⟨0, .tc (.resource .two none (.dealloc 0 32))⟩, ?_, rfl⟩, rfl⟩
        simp [Execution.get, halves, advanced, hlt]
    · exact absurd hn (by simp)
  · rcases hn with hn | hn
    · exact absurd hn (by simp [tcNeeds])
    · simp only [Need.cond.injEq] at hn
      rw [hn]
      have hcta : g / 32 ≤ 1 := by
        have hg' : g % 32 + 32 * (g / 32) = g := Nat.mod_add_div g 32
        omega
      have hg' : g % 32 + 32 * (g / 32) = g := Nat.mod_add_div g 32
      exact ⟨g / 32, ⟨⟨g / 32, 0, fun _ => 0, 0, none, .dealloc 0 32⟩, .two,
        .dealloc 0 32⟩, by simp [halves, hcta],
        ⟨g % 32, Nat.mod_lt _ (by decide)⟩, by
          simp only [WarpRequest.event, L]
          ext
          · simp
            omega
          · rfl⟩

-- Choosing the peer wait requires the pairing, which the halves alone do not give. Choosing to
-- wait cannot be evaded by later changing the choice to false.
private def waiting : Execution := { halves with tmemPairBlocks := fun _ => true }

example : ¬ Tmem.Pair.Blocking L waiting := by
  intro h
  have hc := h.covered (i := (0, 0)) ⟨0, .two, none, .dealloc 0 32, rfl, .inr rfl⟩ (by decide)
  obtain ⟨_, ⟨_, r, hr, hg, _⟩ | ⟨_, hr, _⟩, _⟩ := hc
  · change r ∈ (if _ < 2 then _ else []) at hr
    split_ifs at hr
    · simp only [List.mem_singleton] at hr
      subst hr
      cases hg
    · cases hr
  · cases hr

example : ¬ waiting.le halves := by
  intro h
  have he : waiting.get (0, 0) = some ⟨0, .tc (.resource .two none (.dealloc 0 32))⟩ := rfl
  have hf := Execution.le_tmemPairBlocks h he
  cases hf

-- Performed halves are not a complete operation.
example : ¬ Drained L halves := by
  intro h
  obtain ⟨_, ⟨_, r, hr, hg, _⟩ | ⟨_, hr, _⟩, _⟩ := h (0, 0) 0 .two none (.dealloc 0 32) rfl
  · change r ∈ (if _ < 2 then _ else []) at hr
    split_ifs at hr
    · simp only [List.mem_singleton] at hr
      subst hr
      cases hg
    · cases hr
  · cases hr

-- A waiting request at the trace boundary may remain pending.
example : Tmem.Pair.Blocking L { pending (.dealloc 0 32) with tmemPairBlocks := fun _ => true } :=
    by
  intro i _ _ _ _ _ hn
  change i.2 + 1 < 1 at hn
  omega

-- Allocation does not get the optional early-return choice.
example : MustWait (advanced (.alloc 32)) (0, 0) :=
  ⟨0, .two, none, .alloc 32, rfl, trivial⟩

end
end PTX.Tests.TmemPairCoverage
