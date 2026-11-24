-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RowSum.Proof.Interface
public import Lemmas.Execution.NoAsync

@[expose] public section

/-! # `row_sum`: the events of an execution

The events of a possible execution are the reads of the elements of the rows, the stores of their
sums, the exits, and the undefined behaviour after a read of bytes other than the launch
content. The rows of `A` and the elements of `B` are disjoint locations. -/

namespace PTX.Kernels.RowSum.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B M K : Nat} {x : Nat → ℝ} {mem0 : Mem0} {X : Execution}

theorem noTma : kernel.NoTma := rfl

theorem noShfl : kernel.NoShfl := rfl

/-- **The events of a possible execution.** -/
theorem event_cases (htf : ThreadFacts L A B M K x X)
    (hX : Consistent L kernel Prod mem0 X) {e : EvId} {ev : Event} (h : X.get e = some ev) :
    e.1 < L.threads ∧
      ((e.1 < M ∧ e.2 < K ∧ ∃ bs, ev = rdE A K e.1 e.2 bs) ∨
       (e.1 < M ∧ e.2 = K ∧ ∃ d, stateAt L A B M K X e.1 K = some (some d) ∧ d.i = K ∧
          ev = wrE B e.1 d.a) ∨
       ev = exE ∨
       (∃ pc f, ev = ⟨pc, .ub f⟩ ∧ 0 < e.2 ∧ ∃ bs,
          X.get (e.1, e.2 - 1) = some (rdE A K e.1 (e.2 - 1) bs) ∧
          bs ≠ good x K e.1 (e.2 - 1))) := by
  have hg := Frame.lt_of_get hX h
  refine ⟨hg, ?_⟩
  obtain ⟨g, k⟩ := e
  simp only at hg ⊢
  cases hs : stateAt L A B M K X g k with
  | none =>
    obtain ⟨pc, f, j, bs, rfl, rfl, hj, hbs⟩ := htf.dead hg h hs
    exact .inr (.inr (.inr ⟨pc, f, rfl, by omega, bs, by simpa using hj, by simpa using hbs⟩))
  | some σ =>
    cases σ with
    | none => exact absurd hs (htf.tracked g k hg)
    | some d =>
      rcases htf.event hg h hs with ⟨-, hgM, hk, hik, bs, rfl⟩ | ⟨hsite, hgM, rfl, hiK, rfl⟩ |
        ⟨-, rfl⟩
      · exact .inl ⟨hgM, hk, bs, rfl⟩
      · exact .inr (.inl ⟨hgM, rfl, d, hs, hiK, rfl⟩)
      · exact .inr (.inr (.inl rfl))

theorem reads_cases (htf : ThreadFacts L A B M K x X) (hX : Consistent L kernel Prod mem0 X)
    {e : EvId} {a : Acc} {bs : List (Option Byte)} (h : X.Reads e a bs) :
    e.1 < M ∧ e.2 < K ∧ a = { loc := gA A K e.1 e.2, size := 4 } := by
  obtain ⟨pc, hp⟩ := h
  rcases (event_cases htf hX hp).2 with ⟨h1, h2, bs', he⟩ | ⟨-, -, _, -, -, he⟩ | he | ⟨_, _, he, -⟩
  · simp only [rdE, Event.mk.injEq, Kind.rd.injEq] at he
    exact ⟨h1, h2, he.2.1⟩
  all_goals simp [wrE, exE] at he

theorem writes_cases (htf : ThreadFacts L A B M K x X) (hX : Consistent L kernel Prod mem0 X)
    {w : EvId} {a : Acc} {bs : List Byte} (h : X.Writes w a bs) :
    w.1 < L.threads ∧ w.1 < M ∧ w.2 = K ∧ a = { loc := gB B w.1, size := 4 } := by
  obtain ⟨pc, hp⟩ := h
  obtain ⟨hg, hc⟩ := event_cases htf hX hp
  rcases hc with ⟨-, -, _, he⟩ | ⟨h1, h2, d, -, -, he⟩ | he | ⟨_, _, he, -⟩
  · simp [rdE] at he
  · simp only [wrE, Event.mk.injEq, Kind.wr.injEq] at he
    exact ⟨hg, h1, h2, he.2.1⟩
  all_goals simp [exE] at he

theorem no_nc (htf : ThreadFacts L A B M K x X) (hX : Consistent L kernel Prod mem0 X) {e : EvId}
    {a : Acc} {bs : List (Option Byte)} : ¬ X.NcReads e a bs := by
  rintro ⟨pc, hp⟩
  rcases (event_cases htf hX hp).2 with ⟨-, -, _, he⟩ | ⟨-, -, _, -, -, he⟩ | he | ⟨_, _, he, -⟩ <;>
    simp [rdE, wrE, exE] at he

theorem no_bar (htf : ThreadFacts L A B M K x X) (hX : Consistent L kernel Prod mem0 X) {e : EvId}
    {id : Nat} {count : Option Nat} {pc : Nat} : ¬ X.IsBarrier e id count pc := by
  intro hp
  rcases (event_cases htf hX hp).2 with ⟨-, -, _, he⟩ | ⟨-, -, _, -, -, he⟩ | he | ⟨_, _, he, -⟩ <;>
    simp [rdE, wrE, exE] at he

/-- `A` and `B` are disjoint, and distinct elements of `B` are disjoint. -/
theorem covers_gA_gB (hpre : Pre L A B M K x mem0) {g i h : Nat} (hg : g < M) (hi : i < K)
    (hh : h < M) {l : Loc} (h1 : Acc.Covers { loc := gA A K g i, size := 4 } l)
    (h2 : Acc.Covers { loc := gB B h, size := 4 } l) : False := by
  have := hpre.disjoint
  have := row_le hg (show i + 1 ≤ K by omega)
  simp only [Acc.Covers, Loc.InRange, gA, gB] at h1 h2
  omega

theorem covers_gB_gB {B g h : Nat} {l : Loc} (h1 : Acc.Covers { loc := gB B g, size := 4 } l)
    (h2 : Acc.Covers { loc := gB B h, size := 4 } l) : g = h := by
  simp only [Acc.Covers, Loc.InRange, gB] at h1 h2
  omega

end
end PTX.Kernels.RowSum.Proof
