-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Export.Butterfly
public import Kernels.InklingRelDecode.Proof.Lib.RoundWords
public import Kernels.InklingRelDecode.Proof.Lib.EvWord
public import Kernels.InklingRelDecode.Proof.Lib.RescaleSkip
public import Lemmas.Flow.TypedG
public import Lemmas.Flow.OutKinds
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Softmax.Export.AlphaOperand
import Kernels.InklingRelDecode.Proof.Softmax.Export.ShufflePartner
import Kernels.InklingRelDecode.Proof.Softmax.Data.RoundNum
import Kernels.InklingRelDecode.Proof.Softmax.Data.AlphaExact
import Kernels.InklingRelDecode.Proof.Softmax.Steps.Rescale
import Kernels.InklingRelDecode.Proof.Softmax.RescaleChoice
import Kernels.InklingRelDecode.Proof.Softmax.Export.PollKeep
import Lemmas.Flow.SetpReads

/-! # The minimum butterfly is below the factor of every lane it covers

The words of the stages of the minimum butterfly are numbers (the first stage sends the lane's
rescale factor); a stage `k` word of a lane is at most the first-stage word of every lane of its
warp that the stage covers: the lane itself, and the lanes whose index differs from it by a
subset of the offsets below `k`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow Lib

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The lane `h` of stage `k` covers the lane `y`: same warp, same half, and the lane indices differ
by none of the offsets from stage `k` on. -/
@[expose] public def Cover (k h y : Nat) : Prop :=
  h - h % 32 = y - y % 32 ∧ (h % 32 ^^^ y % 32) < 16 ∧ (h % 32 ^^^ y % 32) &&& (15 >>> k) = 0

private theorem cover_flip (k : Nat) (hk : k < 4) : ∀ a < 32, ∀ b < 32,
    ((a ^^^ b) < 16 ∧ (a ^^^ b) &&& (15 >>> (k + 1)) = 0) →
    (((a ^^^ b) < 16 ∧ (a ^^^ b) &&& (15 >>> k) = 0) ∨
      (((a ^^^ 8 >>> k) ^^^ b) < 16 ∧ ((a ^^^ 8 >>> k) ^^^ b) &&& (15 >>> k) = 0)) := by
  interval_cases k <;> decide +kernel

private theorem cover_step {k h y : Nat} (hk : k < 4) (c : Cover (k + 1) h y) :
    Cover k h y ∨ Cover k (h - h % 32 + (h % 32 ^^^ 8 >>> k)) y := by
  obtain ⟨w, x, z⟩ := c
  have a : h % 32 < 32 := Nat.mod_lt _ (by decide)
  have b : y % 32 < 32 := Nat.mod_lt _ (by decide)
  have f : h % 32 ^^^ 8 >>> k < 32 := Nat.xor_lt_two_pow (n := 5) a (by
    interval_cases k <;> decide)
  have e : (h - h % 32 + (h % 32 ^^^ 8 >>> k)) % 32 = h % 32 ^^^ 8 >>> k := by omega
  have e2 : h - h % 32 + (h % 32 ^^^ 8 >>> k) - (h - h % 32 + (h % 32 ^^^ 8 >>> k)) % 32 =
      h - h % 32 := by omega
  rcases cover_flip k hk _ a _ b ⟨x, z⟩ with ⟨x1, z1⟩ | ⟨x1, z1⟩
  · exact .inl ⟨w, x1, z1⟩
  · exact .inr ⟨by rw [e2, w], by rw [e]; exact x1, by rw [e]; exact z1⟩

private theorem cover_zero {h y : Nat} (c : Cover 0 h y) : h = y := by
  obtain ⟨w, x, z⟩ := c
  have a : h % 32 < 32 := Nat.mod_lt _ (by decide)
  have b : y % 32 < 32 := Nat.mod_lt _ (by decide)
  have : ∀ a < 32, ∀ b < 32, (a ^^^ b) < 16 → (a ^^^ b) &&& (15 >>> 0) = 0 → a = b := by
    decide +kernel
  have := this _ a _ b x z
  omega

private theorem coe_min' (x y : ℝ) : ((min x y : ℝ) : EReal) = min (x : EReal) (y : EReal) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (EReal.coe_le_coe_iff.2 h)]
  · rw [min_eq_right h, min_eq_right (EReal.coe_le_coe_iff.2 h)]

private theorem minE_rd {a b : Value} {x y : ℝ} (ha : Rd a x) (hb : Rd b y) :
    MinCore.minE [a, b] = .ok (Assumption.erealValue .f32 ((min x y : ℝ) : EReal)) := by
  have ha' : Assumption.readEReal .f32 a = some (.ok (x : EReal)) := ha
  have hb' : Assumption.readEReal .f32 b = some (.ok (y : EReal)) := hb
  unfold MinCore.minE
  simp only [MinCore.idealMin, ha', hb', Assumption.bindRead, pure, Except.pure, coe_min']

/-- The minimum of two words that read as numbers reads as the minimum. -/
public theorem rd_min {a b : Value} {x y : ℝ} (ha : Rd a x) (hb : Rd b y) :
    Rd (minWord a b) ((min x y : ℝ) : EReal) := by
  unfold minWord
  rw [minE_rd ha hb]
  exact PTX.Flow.readEReal_erealValue_f32 _

/-- **A decision on two minima below one does not skip.** -/
public theorem skip_false {L : Launch} {a b : Value} {x y : ℝ} (ha : Rd a x) (hb : Rd b y)
    (h : min x y < 1) : Lib.rescaleSkip L a b = false := by
  rw [← Control.skip_free L 0 a b, Control.skipRescale_eq, minE_rd ha hb]
  simp only [Except.bind]
  have one : Rd (PTX.Proof.b32 1065353216) ((1 : ℝ) : EReal) := Data.rd_one
  rw [setpE_reads (c := .unord .ge) (Or.inr rfl) (readEReal_erealValue_f32 _) one]
  have : ¬ (((min x y : ℝ) : EReal) ≥ ((1 : ℝ) : EReal)) := by
    rw [ge_iff_le, EReal.coe_le_coe_iff, not_le]
    exact h
  show decide (((min x y : ℝ) : EReal) ≥ ((1 : ℝ) : EReal)) = false
  exact decide_eq_false this

private theorem min_step {a b : Value} {x y : ℝ} {v0 : EReal} {P R : Prop} (ha : Rd a x)
    (hb : Rd b y) (f1 : P → (x : EReal) ≤ v0) (f2 : R → (y : EReal) ≤ v0) {z : ℝ}
    (hz : Rd (minWord a b) z) (c : P ∨ R) : (z : EReal) ≤ v0 := by
  have e : z = min x y := by
    have := (rd_min ha hb).symm.trans hz
    exact (Option.some.inj this |> Except.ok.inj |> EReal.coe_eq_coe_iff.1).symm
  subst e
  rw [coe_min']
  rcases c with c | c
  · exact (min_le_left _ _).trans (f1 c)
  · exact (min_le_right _ _).trans (f2 c)

/-- **Every stage word is a number, and at most the first-stage word of each lane covered.** The
first-stage word of the lane `y` at the shuffle count `C` is at most `v0`; the stage `k` events at
the count `C + k` read as numbers, below `v0` where they cover `y`. -/
public theorem stage_cover (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (hR : ∀ g j, g % L.block < 128 → ∀ p ∈ Data.roundWords X g j, SK.ni.Has p.1 ∧ SK.ni.Has p.2)
    {y C : Nat} {v0 : EReal}
    (H0 : ∀ j a r, Stage X 0 y j a r → ((X.tr y).take j).countP Execution.isShfl = C →
      ∀ x : ℝ, Rd a x → (x : EReal) ≤ v0) :
    ∀ k, k ≤ 3 → ∀ h j a r, h % L.block < 128 → Stage X k h j a r →
      ((X.tr h).take j).countP Execution.isShfl = C + k →
      (∃ x : ℝ, Rd a x) ∧ (Cover k h y → ∀ x : ℝ, Rd a x → (x : EReal) ≤ v0) := by
  intro k
  induction k with
  | zero =>
    intro _ h j a r lane st cnt
    have ea := alpha_operand hp hX st
    obtain ⟨-, x, hx⟩ := (show SK.fl.Has _ from Data.alphaWord_has hp (hR h j lane))
    rw [← ea] at hx
    refine ⟨⟨x, hx⟩, fun c z hz => ?_⟩
    obtain rfl := cover_zero c
    exact H0 j a r st cnt z hz
  | succ k ih =>
    intro hk h j a r lane st cnt
    obtain ⟨j', a', r', rfl, st', rfl⟩ := stage_back hp hX (by omega) st
    obtain ⟨j2, r2, st2, c2, low⟩ := stage_partner hp hX hf (by omega) lane st'
    obtain ⟨ok, get⟩ := st'
    have c1 : ((X.tr h).take j').countP Execution.isShfl = C + k := by
      have := count_succ get
      simp [Execution.isShfl] at this
      omega
    obtain ⟨⟨x1, d1⟩, f1⟩ := ih (by omega) h j' a' r' lane ⟨ok, get⟩ c1
    obtain ⟨⟨x2, d2⟩, f2⟩ := ih (by omega) _ j2 r' r2 low st2 (c2.trans c1)
    refine ⟨⟨min x1 x2, rd_min d1 d2⟩, fun c z hz => ?_⟩
    rcases cover_step (by omega) c with c' | c'
    · exact min_step d1 d2 (f1 · x1 d1) (f2 · x2 d2) hz (.inl c')
    · exact min_step d1 d2 (f1 · x1 d1) (f2 · x2 d2) hz (.inr c')

/-- **A stage word is the last of a chain of first-stage shuffles one position apart.** -/
public theorem stage_origin (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    ∀ k, k ≤ 3 → ∀ h j a r, Stage X k h j a r → ∃ j0 a0 r0, Stage X 0 h j0 a0 r0 ∧ j = j0 + k ∧
      ((X.tr h).take j).countP Execution.isShfl =
        ((X.tr h).take j0).countP Execution.isShfl + k ∧
      pollRound 1257 ((X.tr h).take (j + 1)) = pollRound 1257 ((X.tr h).take j0) := by
  intro k
  induction k with
  | zero =>
    intro _ h j a r st
    obtain ⟨ok, get⟩ := st
    exact ⟨j, a, r, ⟨ok, get⟩, rfl, rfl, poll_keep get (by show 2242 + 2 * 0 ≠ 1257; omega)⟩
  | succ k ih =>
    intro hk h j a r st
    obtain ⟨j', a', r', rfl, st', -⟩ := stage_back hp hX (by omega) st
    obtain ⟨j0, a0, r0, s0, e1, c1, p1⟩ := ih (by omega) h j' a' r' st'
    obtain ⟨ok, get⟩ := st'
    obtain ⟨ok2, get2⟩ := st
    refine ⟨j0, a0, r0, s0, by omega, ?_, ?_⟩
    · have := count_succ get
      simp [Execution.isShfl] at this
      omega
    · rw [poll_keep get2 (by show 2242 + 2 * (k + 1) ≠ 1257; omega), p1]

/-- **The word a scratch store writes is a number, and at most the first-stage word of every lane
the last two stages cover.** -/
public theorem store_cover (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (hR : ∀ g j, g % L.block < 128 → ∀ p ∈ Data.roundWords X g j, SK.ni.Has p.1 ∧ SK.ni.Has p.2)
    {y C : Nat} {v0 : EReal}
    (H0 : ∀ j a r, Stage X 0 y j a r → ((X.tr y).take j).countP Execution.isShfl = C →
      ∀ x : ℝ, Rd a x → (x : EReal) ≤ v0)
    {h j : Nat} {a r : Value} (lane : h % L.block < 128) (st : Stage X 3 h j a r)
    (cnt : ((X.tr h).take j).countP Execution.isShfl = C + 3) :
    (∃ x : ℝ, Rd (minWord a r) x) ∧
      (Cover 4 h y → ∀ x : ℝ, Rd (minWord a r) x → (x : EReal) ≤ v0) := by
  obtain ⟨j2, r2, st2, c2, low⟩ := stage_partner hp hX hf le_rfl lane st
  obtain ⟨⟨x1, d1⟩, f1⟩ := stage_cover hp hX hf hR H0 3 le_rfl h j a r lane st cnt
  obtain ⟨⟨x2, d2⟩, f2⟩ := stage_cover hp hX hf hR H0 3 le_rfl _ j2 r r2 low st2 (c2.trans cnt)
  refine ⟨⟨min x1 x2, rd_min d1 d2⟩, fun c z hz => ?_⟩
  rcases cover_step (by omega) c with c' | c'
  · exact min_step d1 d2 (f1 · x1 d1) (f2 · x2 d2) hz (.inl c')
  · exact min_step d1 d2 (f1 · x1 d1) (f2 · x2 d2) hz (.inr c')

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
