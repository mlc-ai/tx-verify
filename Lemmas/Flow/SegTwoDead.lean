-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegDead

@[expose] public section

/-! # A two-lane template instance on any input values

A proof tool. A `segmentExact` instance reads each input register as an `.f32` number
(`execSegment`): when an input holds no number (a NaN, an infinity, a value of another kind) the
step faults (`execSegment_two_error`). `SegD.segTwo` takes a two-lane instance as a piece between
facts by any value function `V`: when both inputs read as numbers, the outputs receive the
template's function of their numbers (`rd32`), as `Seg.segTwo` says; otherwise the thread is
dead. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

variable {K : Kernel} {L : Launch} {g : Nat}

/-- A value that reads as a number reads as its `rd32`. -/
theorem valFloat_rd32 {v : Value} {x : ℝ} (h : valFloat .f32 v = .ok x) :
    valFloat .f32 v = .ok (rd32 v) := by
  rw [h, rd32, h]
  rfl

/-- **A two-lane instance faults** when an input holds no number. -/
theorem execSegment_two_error {σ : Type} [DecidableEq σ] {fn : ℝ → ℝ} {m : SegMatch σ}
    {i₀ o₀ i₁ o₁ : σ} {v₀ v₁ : Value} {t : TState}
    (hio : m.shape.io = [(i₀, o₀), (i₁, o₁)])
    (hc : m.shape.defines ∨ ∀ p ∈ m.shape.consts, t.regs (m.regOf p.1) = some p.2)
    (h₀ : t.regs (m.regOf i₀) = some v₀) (h₁ : t.regs (m.regOf i₁) = some v₁)
    (hno : ¬ ((∃ x, valFloat .f32 v₀ = .ok x) ∧ ∃ y, valFloat .f32 v₁ = .ok y)) :
    ∃ f, execSegment fn m t = .error f := by
  unfold execSegment
  simp only [hio, List.mapM_cons, List.mapM_nil, readReg, h₀, h₁, bind, Except.bind, pure,
    Except.pure]
  simp only [hc, ↓reduceIte]
  cases hx : valFloat .f32 v₀ with
  | error f => exact ⟨f, rfl⟩
  | ok x =>
    cases hy : valFloat .f32 v₁ with
    | error f => exact ⟨f, rfl⟩
    | ok y => exact absurd ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ hno

/-- **A two-lane instance of a `segmentExact` template, as a piece on any input values**: when
both inputs read as numbers, the outputs receive the template's function of their numbers, a
defining shape sets its constants and every other live register keeps its value; otherwise the
thread is dead. -/
theorem SegD.segTwo {σ : Type} [DecidableEq σ] {name why : String} {T : SegTemplate σ}
    {sites : List Nat} {a : Assumption} {A A₁ A₂ : List Assumption} {m : SegMatch σ} {pc : Nat}
    {op : Op} {i₀ o₀ i₁ o₁ : σ} {liveS liveT : List Nat} {V : Nat → Value}
    (ha : a = segmentExact K name T sites why)
    (hA : A = A₁ ++ a :: A₂) (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hs : sites.contains pc = true) (hm : T.matchAt K pc = some m)
    (hio : m.shape.io = [(i₀, o₀), (i₁, o₁)])
    (hcst : m.shape.defines = true ∨ ((∀ p ∈ m.shape.consts, m.regOf p.1 ∈ liveS) ∧
      m.shape.consts.map (fun p => V (m.regOf p.1)) = m.shape.consts.map Prod.snd))
    (hi₀ : m.regOf i₀ ∈ liveS) (hi₁ : m.regOf i₁ ∈ liveS)
    (hnd : (segKeys m o₀ o₁).Nodup)
    (hcov : ∀ r ∈ liveT, r ∈ segKeys m o₀ o₁ ∨
      (r ∉ segKeys m o₀ o₁ ++ m.shape.writes.map m.regOf ∧ r ∈ liveS))
    (hA₁ : SegFreePc A₁ pc) :
    SegD K A L g 1 pc (factsFrom liveS V) m.stop
      (factsFrom liveT (valueEx V (segVals m T.fn o₀ o₁ (rd32 (V (m.regOf i₀)))
        (rd32 (V (m.regOf i₁))))))
      ((∃ x, valFloat .f32 (V (m.regOf i₀)) = .ok x) ∧
        ∃ y, valFloat .f32 (V (m.regOf i₁)) = .ok y) := by
  intro t h
  refine ⟨fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ => ?_, fun hno => ?_⟩
  · have hseg := Seg.segTwoAt (L := L) (g := g) (base := V) (ex := []) ha hA hc hl hs hm hio
      hcst hi₀ (valFloat_rd32 hx) hi₁ (valFloat_rd32 hy) hnd hcov hA₁ t h
    rw [List.append_nil] at hseg
    exact hseg
  · subst ha hA
    have hR := h.2.2.2.2
    have h₀ : t.regs (m.regOf i₀) = some (V (m.regOf i₀)) := holds_mem hR (mem_factsFrom hi₀)
    have h₁ : t.regs (m.regOf i₁) = some (V (m.regOf i₁)) := holds_mem hR (mem_factsFrom hi₁)
    have hcst' : m.shape.defines ∨ ∀ p ∈ m.shape.consts, t.regs (m.regOf p.1) = some p.2 := by
      rcases hcst with hd | ⟨hin, heq⟩
      · exact .inl hd
      · refine .inr fun p hp => ?_
        rw [holds_mem hR (mem_factsFrom (hin p hp))]
        have := congrArg (fun l => l[m.shape.consts.idxOf p]?) heq
        simp only [List.getElem?_map, List.getElem?_idxOf hp, Option.map_some] at this
        exact congrArg some (Option.some.inj this)
    obtain ⟨f, hf⟩ := execSegment_two_error (fn := T.fn) hio hcst' h₀ h₁ hno
    have hsel := segmentExact_select (K := K) (name := name) (why := why) (L := L) (g := g)
      (h.1 ▸ hs) h.2.1 h.2.2.1 (h.1 ▸ hm)
    rw [hf] at hsel
    have he : execLocalA (A₁ ++ segmentExact K name T sites why :: A₂) L g t op = .error f :=
      execLocalA_select (hA₁.at h.1) hsel
    exact dead_of_error (h.1 ▸ hc) hl h.2.2.2.1 he

end
end PTX.Flow
