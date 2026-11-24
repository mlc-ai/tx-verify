-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.RefDef
public import Kernels.TmlFa4Fwd.Proof.Correction.Ref
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases
import Kernels.TmlFa4Fwd.Proof.Correction.RefStep
public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
public import Kernels.TmlFa4Fwd.Proof.Correction.Shapes
public import Kernels.TmlFa4Fwd.Proof.Correction.Steps
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The correction warps' reference invariant

`Ref` is the count conjuncts (`RefCounts`) and the nonnegativity of the row sums from their read to
the LSE stores; `Expect` is what an event must return: a 32-bit word at the scheduler's reads and
shuffles and the request's reads, a real `f32` payload at the scale reads, a nonnegative one at the
row-sum reads, the pattern of an extended real below `+∞` at the row-maximum reads, and real `f32`
payloads at the Tensor Memory loads. `ref_next` is the `ref_next` obligation of the counted machine:
under `Ref`, an expected event of the state's shape that is no undefined behaviour does not stop the
machine and leads to a state satisfying `Ref`.

The LSE's logarithms take the kernel's `lg2` rule on a positive row sum and Core's table on a zero
one (`lg2(+0) = -inf`, after which the code's `selp` stores `-inf`). A row sum is zero on a padding
row whose bias values are all `-inf` on a tile without plain rounds, so the machine follows both.
It stops at the final stage's last arrival unless both row sums are nonnegative, and at the first
LSE store unless the second one is (a stop on a recorded value, recorded in `DECISIONS.md` as a
deviation from rule M1). `Expect` asks the row-sum reads to return nonnegative numbers, so that
the machine does not stop there under `Ref`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-! ### The counted machine -/

theorem stepAt_counted (hp : Pre p L m) (hg : g < L.threads) (d : (MC p L g).D) :
    (MC p L g).StepAt d :=
  Code.counted_steps (stepAt hp hg d.1) d.2

theorem shape_counted (hp : Pre p L m) : (MC p L g).Shape (fun d e => Ev p L g d.1 e) :=
  Code.Shape.counted (shape hp)

/-! ### Reference invariant and expected values -/

/-- The first state satisfies the reference invariant. -/
theorem ref_init : Ref p L g (MC p L g).init := by
  show Ref p L g (D.mk' .setmax {}, fun _ => 0)
  refine ⟨⟨0, 0, ?_⟩, fun st h => absurd h (by fin_cases st <;> decide)⟩
  refine ⟨fun c _ => ?_, rfl, le_refl _, fun _ => rfl, fun _ => rfl, fun h => absurd h (by decide),
    fun h => absurd h (by decide)⟩
  show 0 = passed (ptsOf c) .setmax 0
  unfold passed
  have : (ptsOf c).countP (before .setmax) = 0 := by
    rw [List.countP_eq_zero]
    intro q hq
    have := List.all_eq_true.mp setmax_first q (ptsOf_sub c q hq)
    simpa using this
  rw [this]; simp

/-! ### No stop -/

set_option hygiene false in
/-- A branch of a stopping step contradicts the sub-step, the expected value or the
nonnegativity. -/
macro "ns_close" : tactic => `(tactic| (
  first
    | (cases h; done)
    | (exfalso
       have h1 := hpos 1 (by try_rt ((try dsimp only); decide))
       first
         | (have h0 := hpos 0 (by try_rt ((try dsimp only); decide))
            simp only [rsOf] at h0 h1; first | (simp_all; done) | (simp_all; linarith))
         | (simp only [rsOf] at h1; first | (simp_all; done) | (simp_all; linarith)))
    | (exfalso; simp_all [kIn, Site.isFst]; done)
    | (exfalso
       obtain ⟨_, _, hx⟩ := hE _ _ ‹_›
       simp_all; done)
    | (exfalso
       obtain ⟨_, _, _, hx⟩ := hE _ _ ‹_›
       simp_all; done)
    | (exfalso
       obtain ⟨_, hx⟩ := hE _ _ _ _ _ _ ‹_›
       simp_all; done)
    | (exfalso
       have hx := hE _ _ _ ‹_›
       simp_all; done)))

set_option hygiene false in
/-- Unfold a stopping step at a site with literal fields and close its branches. -/
macro "ns_all" : tactic => `(tactic| (
  simp only [ExpectD] at hE
  simp only [succ, word32, real32, max32, scAt, D.mk', D.ite, afterTotal, loopHead, scanExit,
    passStart, afterTiles, enterRounds, roundEnd, afterVote, afterFinal, afterLse,
    Fin.isValue, ↓reduceIte, Bool.false_eq_true] at h
  repeat' (first | (cases h; done) | split at h |
    simp only [Option.map_some, Option.map_none, reduceCtorEq] at h)
  all_goals ns_close))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- **Under `Ref`, an expected event does not stop the machine.** -/
theorem not_stop {d : D} {e : Event} {n : Cnt → Nat} (hJ : Ref p L g (d, n))
    (hE : ExpectD d e) (h : succ p L g d e = some none) : False := by
  obtain ⟨⟨r, ℓ, hQ⟩, hpos⟩ := hJ
  have hsub := hQ.sub
  obtain ⟨s, v, k⟩ := d
  simp only at hpos hsub
  cases s with
  | word sk | down sk | total sk => cases sk <;> ns_all
  | up sk j => cases sk <;> fin_cases j <;> ns_all
  | vote l | pre l | tiles l | wend l | barEnd l | exit l => cases l <;> ns_all
  | arr a | nb a | lse a => fin_cases a <;> ns_all
  | rarr a b | fdone a b => fin_cases a <;> fin_cases b <;> ns_all
  | rscale st =>
    simp only [succ] at h
    split at h
    · rename_i a bs hk
      obtain ⟨x, hx⟩ := hE a bs hk
      rw [hx] at h
      simp only [scale32_val, Option.some.injEq, reduceCtorEq] at h
    · cases h
  | _ => ns_all

/-! ### `Ref` is kept -/

theorem succ_fsum {st : Fin 2} {v : V} {k : Fin 4} {e : Event} {d' : D}
    (h : succ p L g ⟨.fsum st, v, k⟩ e = some (some d')) :
    ∃ a bs x, e.kind = .rd a bs ∧ rebuild 3 bs = .ok (fv x) ∧
      d' = D.mk' (.fmax st) (setRs v x st) := by
  simp only [succ, real32] at h
  split at h <;> try cases h
  rename_i a bs heq
  split at h <;> try cases h
  rename_i w hw
  split at h <;> try cases h
  exact ⟨a, bs, _, heq, hw, rfl⟩

theorem rsOf_setRs (v : V) (x : ℝ) (st st' : Fin 2) :
    rsOf (setRs v x st) st' = if st' = st then x else rsOf v st' := by
  fin_cases st <;> fin_cases st' <;> rfl

/-- The row sums' nonnegativity after a step. -/
theorem pos_step {d d' : D} {e : Event} (hpos : ∀ st, rsPos st d.site = true → 0 ≤ rsOf d.v st)
    (hE : ExpectD d e) (h : succ p L g d e = some (some d')) :
    ∀ st, rsPos st d'.site = true → 0 ≤ rsOf d'.v st := by
  rcases succ_cases h with ⟨rfl, -⟩ | ⟨-, -, rfl⟩ | hF
  · exact hpos
  · exact hpos
  · obtain ⟨s, v, k⟩ := d
    by_cases hfs : s.isFsum = true
    · cases s <;> simp [Site.isFsum] at hfs
      rename_i st0
      obtain ⟨a, bs, x, hk, hx, rfl⟩ := succ_fsum h
      simp only [ExpectD] at hE
      obtain ⟨x', hx', hpx⟩ := hE a bs hk
      rw [hx] at hx'
      have : x = x' := by injection hx' with h1; injection h1
      subst this
      intro st hst
      simp only [D.mk', rsOf_setRs]
      split
      · exact hpx
      · refine hpos st ?_
        fin_cases st0 <;> fin_cases st <;> simp_all [rsPos, Site.pc]
    · have hm := moveOk_of hF.1
      have hfs' : s.isFsum = false := by simpa using hfs
      have hrs : rsOk s d'.site = true := by
        simp only [moveOk, Bool.and_eq_true] at hm; exact hm.2
      simp only [rsOk, hfs', Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_true'] at hrs
      obtain ⟨h0, h1⟩ := hrs
      intro st hst
      have htail : tailR d'.site = true := by
        simp only [rsPos, tailR, Bool.and_eq_true, decide_eq_true_eq] at hst ⊢
        omega
      have hR := hF.2.2.2.2.2 hfs' htail
      have : rsOf d'.v st = rsOf v st := by
        fin_cases st
        · exact hR.1
        · exact hR.2
      rw [this]
      refine hpos st ?_
      fin_cases st
      · rcases h0 with h0 | h0 <;> simp_all
      · rcases h1 with h1 | h1 <;> simp_all

/-! ### The `ref_next` obligation -/

/-- **The `ref_next` obligation of the correction warps**: at a counted state satisfying `Ref`,
an expected event of the state's shape that is no undefined behaviour neither stops the counted
machine nor leads to a state that breaks `Ref`. -/
theorem ref_next {dn : D × (Cnt → Nat)} {e : Event} (hJ : Ref p L g dn) (hE : Expect dn e)
    (hev : Ev p L g dn.1 e) (hub : ∀ f, e.kind ≠ .ub f) :
    (MC p L g).next dn e ≠ some none ∧
      ∀ dn', (MC p L g).next dn e = some (some dn') → Ref p L g dn' := by
  obtain ⟨d, n⟩ := dn
  refine ⟨fun h => not_stop hJ hE (Code.counted_next_none_iff.mp h), fun dn' h => ?_⟩
  obtain ⟨hn, h2⟩ := Code.counted_next_some h
  obtain ⟨⟨r, ℓ, hQ⟩, hpos⟩ := hJ
  obtain ⟨r', ℓ', hQ'⟩ := counts_step hQ hev hub hn
  obtain ⟨d', n'⟩ := dn'
  simp only at h2 hQ' ⊢
  subst h2
  exact ⟨⟨r', ℓ', hQ'⟩, pos_step hpos hE hn⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
