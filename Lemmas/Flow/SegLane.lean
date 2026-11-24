-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.FloatRun

@[expose] public section

/-! # A two-lane template segment read by a lane function

A proof tool. `Seg.segTwo` takes a two-lane instance of a `segmentExact` template, whose lanes
are read as numbers (`valFloat`) and written as the template's function of them, so it needs
real inputs. A kernel assumption may take the same template with its own lane reading: tml-fa4's
`swExp2` reads a lane by `swExp2Lane`, which also gives `0` for the `-∞` encoding (a masked bias
half on a padding row). Its segment rule is `execSegment`'s register effect with that reader.

* `execSegmentLane lane m t`: `execSegment`'s effect with the lane reader `lane : Value → Exec ℝ`
  (a kernel shows its own rule's function equal to it, by definition);
* `execSegmentLane_two`: on two lanes whose readings are `y₀`, `y₁`, the outputs hold
  `.float .f32 y₀` and `.float .f32 y₁`;
* `Seg.segLaneTwo`: the piece, for any assumption `a` whose segment at `pc` is
  `execSegmentLane lane m` on states at `pc` (`hrule`), from facts whose input lanes read as `y₀`,
  `y₁` (any values the reader accepts, `-∞` included). With `lane := fun v => T.fn <$> valFloat
  .f32 v` it is `Seg.segTwo`'s statement for finite inputs. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

variable {K : Kernel} {L : Launch} {g : Nat}

open Classical in
/-- The register effect of a template segment whose lanes are read by `lane`: `execSegment`'s,
with `lane` in place of the template function of the lane's number. -/
def execSegmentLane {σ : Type} [DecidableEq σ] (lane : Value → Exec ℝ) (m : SegMatch σ)
    (t : TState) : Exec TState := do
  let reg := fun slot => (m.reg.lookup slot).getD 0
  unless m.shape.defines ∨ ∀ p ∈ m.shape.consts, t.regs (reg p.1) = some p.2 do
    throw .badValue
  let outs ← m.shape.io.mapM fun (input, output) => do
    let x ← lane (← readReg t (reg input))
    pure (reg output, Value.float .f32 x)
  let cleared := m.shape.writes.foldl (fun rs slot => Function.update rs (reg slot) none) t.regs
  let consts := if m.shape.defines then
      m.shape.consts.foldl (fun rs (slot, v) => Function.update rs (reg slot) (some v)) cleared
    else cleared
  let regs := outs.foldl (fun rs (d, v) => Function.update rs d (some v)) consts
  pure { t with regs := regs, pc := m.stop, sub := 0, acc := [] }

/-- The values a two-lane segment writes: the outputs `y₀`, `y₁` and a defining shape's
constants. -/
def segValsY {σ : Type} [DecidableEq σ] (m : SegMatch σ) (o₀ o₁ : σ) (y₀ y₁ : ℝ) :
    List (Nat × Value) :=
  [(m.regOf o₀, .float .f32 y₀), (m.regOf o₁, .float .f32 y₁)] ++
    (if m.shape.defines then m.shape.consts.map fun p => (m.regOf p.1, p.2) else [])

theorem segVals_eq_segValsY {σ : Type} [DecidableEq σ] {m : SegMatch σ} {fn : ℝ → ℝ}
    {o₀ o₁ : σ} {x₀ x₁ : ℝ} : segVals m fn o₀ o₁ x₀ x₁ = segValsY m o₀ o₁ (fn x₀) (fn x₁) := rfl

theorem segValsY_keys {σ : Type} [DecidableEq σ] {m : SegMatch σ} {o₀ o₁ : σ}
    {y₀ y₁ : ℝ} : (segValsY m o₀ o₁ y₀ y₁).map Prod.fst = segKeys m o₀ o₁ := by
  unfold segValsY segKeys
  split <;> simp

/-- **Two lanes read by `lane`**: the outputs hold the readings. -/
theorem execSegmentLane_two {σ : Type} [DecidableEq σ] {lane : Value → Exec ℝ} {m : SegMatch σ}
    {t : TState} {i₀ o₀ i₁ o₁ : σ} {v₀ v₁ : Value} {y₀ y₁ : ℝ}
    (hio : m.shape.io = [(i₀, o₀), (i₁, o₁)])
    (hc : m.shape.defines ∨ ∀ p ∈ m.shape.consts, t.regs (m.regOf p.1) = some p.2)
    (h₀ : t.regs (m.regOf i₀) = some v₀) (hy₀ : lane v₀ = .ok y₀)
    (h₁ : t.regs (m.regOf i₁) = some v₁) (hy₁ : lane v₁ = .ok y₁) :
    execSegmentLane lane m t = .ok { t with
      regs := segRegs m t [(m.regOf o₀, .float .f32 y₀), (m.regOf o₁, .float .f32 y₁)],
      pc := m.stop, sub := 0, acc := [] } := by
  unfold execSegmentLane
  simp only [hio, List.mapM_cons, List.mapM_nil, readReg, h₀, h₁, hy₀, hy₁,
    bind, Except.bind, pure, Except.pure]
  simp only [hc, ↓reduceIte]
  rfl

/-- **A two-lane template segment read by a lane function, as a piece**: an assumption `a`
whose segment at `pc` is `execSegmentLane lane m`; the outputs receive the readings of the inputs
(`-∞` included where `lane` accepts it), a defining shape sets its constants, the other
registers the segment writes are dead at the end and every other live register keeps its
value. -/
theorem Seg.segLaneTwo {σ : Type} [DecidableEq σ] {lane : Value → Exec ℝ} {a : Assumption}
    {A₁ A₂ : List Assumption} {m : SegMatch σ} {pc : Nat} {op : Op}
    {i₀ o₀ i₁ o₁ : σ} {y₀ y₁ : ℝ} {liveS liveT : List Nat} {base : Nat → Value}
    {ex : List (Nat × Value)} (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hrule : ∀ t : TState, t.pc = pc → t.sub = 0 → t.acc = [] →
      a.segmentRule L g t = some (execSegmentLane lane m t))
    (hio : m.shape.io = [(i₀, o₀), (i₁, o₁)])
    (hcst : m.shape.defines = true ∨ ((∀ p ∈ m.shape.consts, m.regOf p.1 ∈ liveS) ∧
      m.shape.consts.map (fun p => valueEx base ex (m.regOf p.1)) = m.shape.consts.map Prod.snd))
    (hi₀ : m.regOf i₀ ∈ liveS) (hy₀ : lane (valueEx base ex (m.regOf i₀)) = .ok y₀)
    (hi₁ : m.regOf i₁ ∈ liveS) (hy₁ : lane (valueEx base ex (m.regOf i₁)) = .ok y₁)
    (hnd : (segKeys m o₀ o₁).Nodup)
    (hcov : ∀ r ∈ liveT, r ∈ segKeys m o₀ o₁ ∨
      (r ∉ segKeys m o₀ o₁ ++ m.shape.writes.map m.regOf ∧ r ∈ liveS))
    (hA₁ : SegFreePc A₁ pc) :
    Seg K (A₁ ++ a :: A₂) L g 1 pc
      (factsFrom liveS (valueEx base ex)) m.stop
      (factsFrom liveT (valueEx base (segValsY m o₀ o₁ y₀ y₁ ++ ex))) := by
  intro t h
  have hR := h.2.2.2.2
  have hcst' : m.shape.defines ∨ ∀ p ∈ m.shape.consts, t.regs (m.regOf p.1) = some p.2 := by
    rcases hcst with hd | ⟨hin, heq⟩
    · exact .inl hd
    · refine .inr fun p hp => ?_
      rw [holds_mem hR (mem_factsFrom (hin p hp))]
      have := congrArg (fun l => l[m.shape.consts.idxOf p]?) heq
      simp only [List.getElem?_map, List.getElem?_idxOf hp, Option.map_some] at this
      exact congrArg some (Option.some.inj this)
  have hex := execSegmentLane_two (lane := lane) hio hcst' (holds_mem hR (mem_factsFrom hi₀)) hy₀
    (holds_mem hR (mem_factsFrom hi₁)) hy₁
  have hrun := run_select (A₂ := A₂) hc hl h
    (show a.segmentRule L g t = some (.ok _) by rw [hrule t h.1 h.2.1 h.2.2.1, hex]) hA₁
  refine ⟨_, hrun, rfl, rfl, rfl, h.2.2.2.1, ?_⟩
  simp only [segKeys, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    not_or] at hnd
  have hne : m.regOf o₀ ≠ m.regOf o₁ := hnd.1.1
  refine holds_ext (W := segKeys m o₀ o₁ ++ m.shape.writes.map m.regOf) hR
    (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_append, not_or, List.mem_map, not_exists, not_and] at hr
    refine segRegs_keep (fun s hs he => hr.2 s hs he) (fun q hq => ?_) (fun hd q hq he => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact fun he => hr.1 (by simp only at he; simp [segKeys, ← he])
      · exact fun he => hr.1 (by simp only at he; simp [segKeys, ← he])
    · exact hr.1 (by simp only [segKeys, hd, ↓reduceIte]; simp only [List.mem_append,
        List.mem_map]; exact .inr ⟨q, hq, he⟩)
  · rw [segValsY_keys] at hr
    simp only [segKeys, List.cons_append, List.nil_append, List.mem_cons] at hr
    show segRegs m t _ r = _
    rcases hr with rfl | rfl | hr
    · rw [(segRegs_two_out (m := m) (t := t)).2 hne]
      simp [segValsY]
    · rw [(segRegs_two_out (m := m) (t := t)).1]
      simp [segValsY, List.lookup, beq_false_of_ne (Ne.symm hne)]
    · split at hr
      · rename_i hd
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
        simp only [hd, ↓reduceIte] at hnd
        have h0 : m.regOf p.1 ≠ m.regOf o₀ := fun he =>
          hnd.1.2 (he ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
        have h1 : m.regOf p.1 ≠ m.regOf o₁ := fun he =>
          hnd.2.1 (he ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
        rw [segRegs_const hd hp hnd.2.2 (fun q hq => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl
          · exact Ne.symm h0
          · exact Ne.symm h1)]
        simp only [segValsY, hd, ↓reduceIte, List.cons_append, List.nil_append, List.lookup,
          beq_false_of_ne h0, beq_false_of_ne h1]
        exact (lookup_map_get (f := fun p => m.regOf p.1) (v := Prod.snd) _ hnd.2.2 hp).symm
      · cases hr
  · rw [segValsY_keys]
    exact hcov r hr

end
end PTX.Flow
