-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.CtaBarAppendWarp
public import Lemmas.Quiet.Base

@[expose] public section

/-! # A warp's named-barrier arrival is recorded under quiet extensions

`NamedBar.arrive_release` of `Lemmas/Step/CtaBarAppendWarp.lean` under `Assumption.WfQuiet`. -/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **A thread at an unrecorded arrival whose warp has arrived is recorded in an extension.** In a
maximal execution with no CTA barrier fault, let thread `g`'s last event be an unrecorded arrival
on named barrier `id < 16` with the valid operand `cnt`, and let every lane of its warp have made
its arrival on `id` of the same ordinal with operand `cnt`. Then a maximal execution with the
same traces records `g`'s arrival. -/
theorem arrive_release_preserving_objectsQ (hmax : Maximal L K A mem0 X) {sel : Nat → Bool}
    (hA : Assumption.WfQuiet sel L K mem0 A) (hf : ¬ CtaBarFault L X) {g pc id n : Nat}
    {cnt : Option Nat} {m : BarMode} (hg : g < L.threads) (hid : id < 16)
    (hn : target L.block cnt = .ok n)
    (hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id cnt m⟩)
    (hnr : (g, (X.tr g).length - 1) ∉ (X.barriers (g / L.block)).flatMap Record.refs)
    (hlane : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 → ∃ j pc' m',
      X.get (g / L.block * L.block + lt, j) = some ⟨pc', .bar id cnt m'⟩ ∧
      ((X.tr (g / L.block * L.block + lt)).take j).countP (Execution.isBarId id) =
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)) :
    ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧ Y.objects = X.objects ∧
      (g, (X.tr g).length - 1) ∈ (Y.barriers (g / L.block)).flatMap Record.refs := by
  have hX := hmax.1
  have hb := block_pos_of_thread_lt hg
  have hc := cta_lt hg
  have hgl : g % L.block < L.block := Nat.mod_lt _ hb
  have hgeq : g / L.block * L.block + g % L.block = g := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod g L.block
  have hgno : ∀ k pc', X.get (g / L.block * L.block + g % L.block, k) ≠ some ⟨pc', .exit⟩ := by
    intro k pc' hk
    rw [hgeq] at hk
    have hl := Execution.exit_last hX hg hk
    have hk' : k = (X.tr g).length - 1 := by omega
    rw [hk', hlast] at hk
    cases hk
  have hlast' : X.get (g / L.block * L.block + g % L.block,
      (X.tr (g / L.block * L.block + g % L.block)).length - 1) = some ⟨pc, .bar id cnt m⟩ := by
    rw [hgeq]; exact hlast
  have hlane' : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 →
      (∃ pc m, X.get (g / L.block * L.block + lt,
        (X.tr (g / L.block * L.block + lt)).length - 1) = some ⟨pc, .bar id cnt m⟩) ∧
      (g / L.block * L.block + lt, (X.tr (g / L.block * L.block + lt)).length - 1) ∉
        (X.barriers (g / L.block)).flatMap Record.refs := by
    intro lt hlt hlw
    obtain ⟨j, pc', m', hget, hord⟩ := hlane lt hlt hlw
    have hnrj : (g / L.block * L.block + lt, j) ∉
        (X.barriers (g / L.block)).flatMap Record.refs := by
      intro hrec
      apply hnr
      have := recorded_of_lane hX hc hlt hgl hlw hget hlast'
        (by rw [hord, hgeq]) hrec hgno
      rwa [hgeq] at this
    have hdiv := (lane_cta (c := g / L.block) hb hlt).1
    rcases recorded_or_last hX hget with hrec | hl
    · rw [hdiv] at hrec
      exact absurd hrec hnrj
    · simp only at hl
      have hj : (X.tr (g / L.block * L.block + lt)).length - 1 = j := by omega
      rw [hj]
      exact ⟨⟨pc', m', hget⟩, hnrj⟩
  have hmaxY := append_warp_in_history hmax hA.ctaHistory
    (fun h => hf (h.ctaBarFault hc)) hc (w := g % L.block / 32) (by omega) hid hn hlane'
  refine ⟨_, hmaxY, rfl, rfl, ?_⟩
  rw [withCtaHistory_barriers_self, List.flatMap_append]
  refine List.mem_append_right _ ?_
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, warpRecord, Record.refs]
  refine List.mem_map.mpr ⟨(g % L.block, (g / L.block * L.block + g % L.block,
    (X.tr (g / L.block * L.block + g % L.block)).length - 1)),
    mem_fullLanes.mpr ⟨hgl, rfl, rfl⟩, ?_⟩
  simp only [hgeq]

/-- **A thread at an unrecorded arrival whose warp has arrived is recorded in an extension.** In a
maximal execution with no CTA barrier fault, let thread `g`'s last event be an unrecorded arrival
on named barrier `id < 16` with the valid operand `cnt`, and let every lane of its warp have made
its arrival on `id` of the same ordinal with operand `cnt`. Then a maximal execution with the
same traces records `g`'s arrival. -/
theorem arrive_releaseQ (hmax : Maximal L K A mem0 X) {sel : Nat → Bool}
    (hA : Assumption.WfQuiet sel L K mem0 A) (hf : ¬ CtaBarFault L X) {g pc id n : Nat}
    {cnt : Option Nat} {m : BarMode} (hg : g < L.threads) (hid : id < 16)
    (hn : target L.block cnt = .ok n)
    (hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id cnt m⟩)
    (hnr : (g, (X.tr g).length - 1) ∉ (X.barriers (g / L.block)).flatMap Record.refs)
    (hlane : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 → ∃ j pc' m',
      X.get (g / L.block * L.block + lt, j) = some ⟨pc', .bar id cnt m'⟩ ∧
      ((X.tr (g / L.block * L.block + lt)).take j).countP (Execution.isBarId id) =
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)) :
    ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧
      (g, (X.tr g).length - 1) ∈ (Y.barriers (g / L.block)).flatMap Record.refs := by
  obtain ⟨Y, hY, hTrace, _, hRecord⟩ :=
    arrive_release_preserving_objectsQ hmax hA hf hg hid hn hlast hnr hlane
  exact ⟨Y, hY, hTrace, hRecord⟩

end

end PTX.NamedBar
