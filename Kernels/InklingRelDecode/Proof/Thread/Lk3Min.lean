-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LkSm

@[expose] public section

/-!
# The rescale test as a function of the four scratch words

The softmax region's lazy-rescale test reads the four scratch words (`ldL`, the word `tid % 4`),
takes the minimum over the lanes `l`, `l ^ 2` (`shfl11`, `min.f32` into `m2`), and then over the
lanes `l`, `l ^ 1` (`shfl12`, `%p170 = min(m2, received) >= 1.0`). This file is the machine's
part of the value chain: what the successor of `shfl11` and the decision at `shfl12` are as
functions of the numbers the words and the shuffles carry. A value that reads as an extended real
(`ReadsAs`) is all the chain needs: the minimum of two such values is the value of the minimum, so
the decision at `shfl12` is a function of the numbers (`p170_readsAs`), and two states whose
`m2` and received word give the same minimum take the same decision (`p170_congr`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Lk

noncomputable section
set_option maxRecDepth 100000

/-- The value `v` reads as the extended real `x` (`readEReal`: a `.f32` number, an infinity or a
zero; a NaN does not read). -/
abbrev ReadsAs (v : Value) (x : EReal) : Prop := readEReal .f32 v = some (.ok x)

theorem ReadsAs.of_erealValue {x : EReal} (h : x ≠ ⊤) : ReadsAs (erealValue .f32 x) x :=
  readEReal_erealValue h

theorem ReadsAs.unique {v : Value} {x y : EReal} (hx : ReadsAs v x) (hy : ReadsAs v y) : x = y := by
  unfold ReadsAs at hx hy
  rw [hx] at hy
  exact (Except.ok.inj (Option.some.inj hy))

/-- **`min.f32` of two values that read as numbers** is the value of the minimum. -/
theorem minE_readsAs {a b : Value} {x y : EReal} (ha : ReadsAs a x) (hb : ReadsAs b y) :
    minE [a, b] = .ok (erealValue .f32 (min x y)) := by
  unfold minE
  simp only [idealMin, ha, hb, bindRead, pure, Except.pure]

/-- **The decision `%p170` of `shfl12`** for the state's `m2` and the received word, which read as
`x` and `y`: the comparison `min(x, y) >= 1.0` (unordered `geu`) on the value of the minimum. -/
theorem p170_readsAs (d : D) {recv : Value} {x y : EReal} (hx : ReadsAs d.stg.m2 x)
    (hy : ReadsAs recv y) :
    d.p170 recv = setpE (.unord .ge) false (erealValue .f32 (min x y)) (b32 1065353216) := by
  unfold D.p170
  rw [minE_readsAs hx hy]
  rfl

/-- The state after the `shfl11` exchange: at `shfl12`, with `m2` recorded. -/
def D.toShfl12 (d : D) (v : Value) : D := { d with site := .shfl12, stg := { d.stg with m2 := v } }

/-- **The successor of `shfl11`**: `m2` is the value of the minimum of the loaded word and the
received one, when both read as numbers. -/
theorem next_shfl11 (L : Launch) (g : Nat) {d : D} {e : Event} {m : ShflMode} {a : Value}
    {b c : Nat} {recv : Value} {ok : Bool} {x y : EReal} (hs : d.site = .shfl11)
    (he : e.kind = .shfl m a b c recv ok) (hx : ReadsAs d.stg.ld x) (hy : ReadsAs recv y) :
    Sm.next L g d e = some (some (d.toShfl12 (erealValue .f32 (min x y)))) := by
  simp only [Sm.next, hs, he, minE_readsAs hx hy, D.toShfl12]

/-- **A successor of `shfl12` is the successor of a shuffle**: the event is a shuffle. -/
theorem shfl12_kind {L : Launch} {g : Nat} {d t : D} {e : Event}
    (hn : Sm.next L g d e = some (some t)) (hs : d.site = .shfl12) :
    ∃ (m : ShflMode) (a : Value) (b c : Nat) (recv : Value) (ok : Bool),
      e.kind = .shfl m a b c recv ok := by
  simp only [Sm.next, hs] at hn
  cases hk : e.kind <;> simp only [hk] at hn <;>
    first | (simp at hn; done) | exact ⟨_, _, _, _, _, _, rfl⟩

/-- **The branch to the P store at `shfl12`** is taken exactly when the decision `%p170` of the
received word holds and the edge's update succeeds. -/
theorem branchBar20_iff {L : Launch} {g : Nat} {d : D} {e : Event} {m : ShflMode} {a : Value}
    {b c : Nat} {r : Value} {ok : Bool} (hs : d.site = .shfl12) (he : e.kind = .shfl m a b c r ok) :
    BranchBar20 L g d e ↔ d.p170 r = .ok true ∧ d.updOk = true := by
  unfold BranchBar20
  simp only [Sm.next, hs, he]
  rcases hq : d.p170 r with f | p
  · simp
  · cases p
    · simp
    · simp only [↓reduceIte, Sm.toBar20]
      by_cases hu : d.updOk = true
      · simp [hu]
      · simp [hu]

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
