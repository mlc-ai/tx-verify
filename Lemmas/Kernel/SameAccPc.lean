-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.FrameU
public import Lemmas.Kernel.ElemSub

@[expose] public section

/-! # Two elements of one vector access are at one instruction

A proof tool. If event `j + 1` of a thread continues the vector access of event `j`
(`SameAccess`), its element index is at least one, so the thread's sub-step before it is nonzero
(`fires_elem`). A machine whose steps keep the pc whenever the sub-step they reach is nonzero
(`hstable`) puts both events at one pc. -/

namespace PTX.Frame

open PTX PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {C : (g : Nat) → Code K A L g} {g j : Nat}

/-- The shifted footprint of the next element has a positive element index. -/
theorem sameAccess_elem {e e' : Event} (he : X.get (g, j) = some e)
    (he' : X.get (g, j + 1) = some e') (hs : SameAccess X (g, j) (g, j + 1)) :
    ∃ a a', e.acc = some a ∧ e'.acc = some a' ∧ a'.elem = a.elem + 1 := by
  obtain ⟨h1, h2⟩ := hs
  have h := h2 1 (by simp)
  simp only [he, he', Option.bind_some] at h1 h
  cases hA : e.acc with
  | none => rw [hA] at h; rw [h] at h1; simp at h1
  | some a =>
    rw [hA] at h
    simp only [Option.map_some] at h
    refine ⟨a, _, rfl, h, ?_⟩
    simp [Acc.shift]

/-- An access event is no undefined behaviour. -/
theorem acc_kind_ne_ub {e : Event} {a : Acc} (h : e.acc = some a) : ∀ f, e.kind ≠ .ub f := by
  intro f hk
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  simp [Event.acc] at h

/-- The state before the second element of a vector access has a nonzero sub-step. -/
theorem sameAccess_sub (hC : ∀ g < L.threads, (C g).SoundU) (hX : Consistent L K A mem0 X)
    {e e' : Event} (he : X.get (g, j) = some e) (he' : X.get (g, j + 1) = some e')
    (hs : SameAccess X (g, j) (g, j + 1)) {d' : (C g).D}
    (hd' : stateAt C X g (j + 1) = some (some d')) : (C g).sub d' ≠ 0 := by
  obtain ⟨a, a', hA, hA', hel⟩ := sameAccess_elem he he' hs
  obtain ⟨t, ins, o, hat, -, -, hf⟩ := fired_siteU hC hX he' hd' (acc_kind_ne_ub hA')
  have hel' := fires_elem hf hA'
  rw [← hat.2.1]
  omega

/-- **Consecutive elements of one vector access are at one pc**, for a machine whose step to the
state of the second keeps the pc when that state has a nonzero sub-step. -/
theorem sameAccess_pc (hC : ∀ g < L.threads, (C g).SoundU) (hX : Consistent L K A mem0 X)
    {e e' : Event} (he : X.get (g, j) = some e) (he' : X.get (g, j + 1) = some e')
    (hs : SameAccess X (g, j) (g, j + 1)) {d d' : (C g).D}
    (hd : stateAt C X g j = some (some d)) (hd' : stateAt C X g (j + 1) = some (some d'))
    (hstable : (C g).sub d' ≠ 0 → (C g).pc d' = (C g).pc d) : e.pc = e'.pc := by
  obtain ⟨a, a', hA, hA', hel⟩ := sameAccess_elem he he' hs
  have hu : ∀ e : Event, ∀ a, e.acc = some a → ∀ f, e.kind ≠ .ub f :=
    fun _ _ h => acc_kind_ne_ub h
  obtain ⟨t, ins, o, hat, -, -, hf⟩ := fired_siteU hC hX he' hd' (hu e' a' hA')
  have hsub : t.sub = (C g).sub d' := hat.2.1
  have hel' := fires_elem hf hA'
  have hne : (C g).sub d' ≠ 0 := by
    rw [← hsub]; omega
  rw [event_pcU hC hX he hd (hu e a hA), event_pcU hC hX he' hd' (hu e' a' hA'), hstable hne]
end PTX.Frame
