-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.WidenFinite
import Kernels.FlashKdaFwd.Audit.NormChoices

/-! For finite keys, every specified reduction result feeds a positive normal argument
or positive infinity to the reciprocal square root. Both give a finite normalization factor. -/
namespace FlashKda.FiniteMask
open PTX FlashKda.NormRange FlashKda.Normalize FlashKda.RootContract
noncomputable section

theorem square_closed {x : FVal} (h : NormRange.Finite x) : NormRange.Nonneg (x.mul x) := by
  cases x <;> simp_all [NormRange.Finite,NormRange.Nonneg,FVal.mul,FVal.toRat,FVal.isNeg]
  split_ifs <;> simp [mul_self_nonneg]

theorem add_closed {x y : FVal} (hx : NormRange.Nonneg x) (hy : NormRange.Nonneg y) :
    NormRange.Nonneg (x.add .rn y) := by
  cases x <;> cases y <;> simp_all [NormRange.Nonneg,FVal.add,FVal.toRat]
  all_goals split_ifs <;> simp_all [_root_.add_nonneg]

theorem rounded_nonneg {v out : FVal} (h : NormRange.Nonneg v)
    (r : format.roundVal .rn true v = some out) : NormRange.Nonneg out := by
  cases v with
  | fin x =>
    change 0 ≤ x at h
    exact round_nonneg (by exact_mod_cast h) r
  | zero _ | inf _ | nan _ => cases r; exact h

private theorem square_result (acc x : FVal) :
    squareStep acc x = format.roundVal .rn true
      (((format.flush x).mul (format.flush x)).add .rn (format.flush acc)) := by
  have op : square.lane [x,x,acc] =
      FOut.val <$> (format.roundVal .rn true
        (((format.flush x).mul (format.flush x)).add .rn (format.flush acc))) := by
    change (FOut.val <$> square.arith [x,x,acc]) = _
    have flush : square.flushIn [x,x,acc] =
        [format.flush x,format.flush x,format.flush acc] := rfl
    simp [FloatInstr.arith, square, FloatRound.mode]
    unfold square at flush
    rw [flush]
  unfold squareStep
  rw [op]
  cases format.roundVal .rn true
      (((format.flush x).mul (format.flush x)).add .rn (format.flush acc)) <;> rfl

private theorem sum_result (x y : FVal) :
    sumStep x y = format.roundVal .rn true ((format.flush x).add .rn (format.flush y)) := by
  have op : (add32 (some .rn)).lane [x,y] = FOut.val <$>
      format.roundVal .rn true ((format.flush x).add .rn (format.flush y)) := by
    change (FOut.val <$> (add32 (some .rn)).arith [x,y]) = _
    have flush : (add32 (some .rn)).flushIn [x,y] = [format.flush x,format.flush y] := rfl
    simp [FloatInstr.arith, add32, FloatRound.mode]
    unfold add32 at flush
    rw [flush]
  unfold sumStep
  rw [op]
  cases format.roundVal .rn true ((format.flush x).add .rn (format.flush y)) <;> rfl

theorem square_step {x acc v : FVal} (key : NormRange.Finite x) (prev : NormRange.Nonneg acc)
    (h : squareStep acc x = some v) : NormRange.Nonneg v := by
  rw [square_result] at h
  exact rounded_nonneg (add_closed (square_closed (flush_finite key)) (flush_nonneg prev)) h

theorem sum_step {a b v : FVal} (left : NormRange.Nonneg a) (right : NormRange.Nonneg b)
    (h : sumStep a b = some v) : NormRange.Nonneg v := by
  rw [sum_result] at h
  exact rounded_nonneg (add_closed (flush_nonneg left) (flush_nonneg right)) h

abbrev epsilon : ℚ := magnitude 0x358637bd

private theorem epsilon_format : format.minNormal ≤ epsilon ∧ 0 < epsilon ∧
    format.flush (.fin epsilon) = .fin epsilon := by decide +kernel

theorem plus_epsilon {s v : FVal} (hs : NormRange.Nonneg s)
    (step : sumStep s (.fin epsilon) = some v) :
    RootArg v := by
  rw [sum_result,epsilon_format.2.2] at step
  have hf := flush_nonneg hs
  generalize hw : format.flush s = w at step hf
  cases w with
  | nan _ => exact False.elim hf
  | inf sign =>
    change sign = false at hf
    subst sign
    exact Option.some.inj step ▸ (rfl : RootArg (.inf false))
  | zero sign =>
    have pos := epsilon_format.2.1
    have eq : (FVal.zero sign).add .rn (.fin epsilon) = .fin epsilon := by
      simp [FVal.add,FVal.toRat,ne_of_gt pos]
    rw [eq] at step
    exact root_argument (by exact_mod_cast epsilon_format.1) step
  | fin q =>
    change 0 ≤ q at hf
    have pos : 0 < q + epsilon := by linarith [epsilon_format.2.1]
    have eq : (FVal.fin q).add .rn (.fin epsilon) = .fin (q + epsilon) := by
      simp [FVal.add,FVal.toRat,ne_of_gt pos]
    rw [eq] at step
    apply root_argument _ step
    exact_mod_cast (show format.minNormal ≤ q + epsilon by linarith [epsilon_format.1])

private theorem finite_widen {w : Nat} (finite : finiteWord w) {x : FVal}
    (hw : widened w = some x) : NormRange.Finite x := by
  obtain ⟨_,_,same,ok⟩ := widened_bits w finite
  exact (Option.some.inj (same.symm.trans hw)) ▸ ok

/-- Each lane widens eight input words and accumulates their squares. -/
private theorem lane_nonneg (raw : List Nat) {acc v : FVal} (ha : NormRange.Nonneg acc)
    (finite : ∀ w ∈ raw, ∀ x, widened w = some x → NormRange.Finite x)
    (step : laneSum acc raw = some v) : NormRange.Nonneg v := by
  induction raw generalizing acc with
  | nil =>
    cases step
    exact ha
  | cons w ws ih =>
    cases hx : widened w with
    | none => simp [laneSum,hx] at step
    | some x =>
      cases hs : squareStep acc x with
      | none => simp [laneSum,hx,hs] at step
      | some s =>
        exact ih (square_step (finite w (by simp) x hx) ha hs)
          (fun z hz => finite z (by simp [hz])) (by simpa [laneSum,hx,hs] using step)

/-- Arbitrary raw packets follow the same four exchange distances as the compiled warp.
The list runs from the last exchange back toward the initial per-lane sums. -/
def rowSum (packet : Nat → List Nat) : List Nat → Nat → Option FVal
  | [], lane => laneSum (.zero false) (packet lane)
  | d::ds, lane => do
    let (peer,valid) := shflSource .bfly lane d 31
    guard valid
    sumStep (← rowSum packet ds lane) (← rowSum packet ds peer)

/-- The existing production arithmetic probe is an instance of the generic reduction. -/
theorem same_sum (key : Bool) (ds : List Nat) (lane : Nat) :
    rowSum (rawPacket key) ds lane = warpSum key ds lane := by
  induction ds generalizing lane with
  | nil => rfl
  | cons d ds ih =>
    simp only [rowSum,warpSum,ih]

private theorem row_nonneg (packet : Nat → List Nat)
    (finite : ∀ lane w, w ∈ packet lane → ∀ x, widened w = some x → NormRange.Finite x)
    (ds : List Nat) (lane : Nat) {v : FVal}
    (step : rowSum packet ds lane = some v) : NormRange.Nonneg v := by
  induction ds generalizing lane v with
  | nil => exact lane_nonneg _ (by trivial) (finite lane) step
  | cons d ds ih =>
    cases hp : shflSource .bfly lane d 31 with
    | mk peer valid =>
      cases valid <;> simp [rowSum,hp] at step
      cases ha : rowSum packet ds lane with
      | none => simp [ha] at step
      | some a =>
        cases hb : rowSum packet ds peer with
        | none => simp [ha,hb] at step
        | some b => exact sum_step (ih _ ha) (ih _ hb) (by simpa [ha,hb] using step)

/-- On any finite row, any specified execution of the four exchanges and epsilon addition
gives a normal positive root argument or positive infinity from overflow. -/
theorem finite_argument (packet : Nat → List Nat)
    (finite : ∀ lane w, w ∈ packet lane → ∀ x, widened w = some x → NormRange.Finite x)
    (lane : Nat) {s v : FVal} (sum : rowSum packet [1,2,4,8] lane = some s)
    (epsilonAdded : sumStep s (.fin epsilon) = some v) : RootArg v :=
  plus_epsilon (row_nonneg packet finite _ lane sum) epsilonAdded

/-- Version stated directly in terms of the bits in the public bfloat16 input buffer. -/
theorem finite_words_argument (packet : Nat → List Nat)
    (finite : ∀ lane w, w ∈ packet lane → finiteWord w) (lane : Nat) {s v : FVal}
    (sum : rowSum packet [1,2,4,8] lane = some s)
    (epsilonAdded : sumStep s (.fin epsilon) = some v) : RootArg v :=
  finite_argument packet (fun l w mem _ => finite_widen (finite l w mem)) lane sum epsilonAdded

/-- Zeroing a padded raw key gives a zero normalized key for every allowed positive-normal
reciprocal square root. An overflowing square sum gives reciprocal positive zero. -/
theorem masked {x : ℚ} {w : Nat} (allowedRoot : allowed x w) :
    format.decode w = some (.fin (magnitude w)) ∧
    (FVal.zero false).mul (.fin (magnitude w)) = .zero false := by
  refine ⟨decode allowedRoot, ?_⟩
  have pos := Layout.magnitude_nonneg 8 23 w
  simp [FVal.mul,FVal.toRat,FVal.isNeg,not_lt.mpr pos]

theorem masked_overflow : invRoot.lane [.inf false] = some (.val (.zero false)) ∧
    (FVal.zero false).mul (.zero false) = .zero false :=
  ⟨inverse_lane,by decide +kernel⟩

/-- Select any allowed inverse length on a normal input, and the specified inverse on
positive infinity. Every such choice leaves a cleared key coordinate at positive zero. -/
theorem finite_mask (packet : Nat → List Nat)
    (finite : ∀ lane w, w ∈ packet lane → finiteWord w) (lane : Nat) {s v : FVal}
    (sum : rowSum packet [1,2,4,8] lane = some s)
    (epsilonAdded : sumStep s (.fin epsilon) = some v) (proposal : Nat) :
    match v with
    | .fin x => ∃ w, allowed x w ∧ (allowed x proposal → w = proposal) ∧
        format.decode w = some (.fin (magnitude w)) ∧
        (FVal.zero false).mul (.fin (magnitude w)) = .zero false
    | .inf false => invRoot.lane [v] = some (.val (.zero false)) ∧
        (FVal.zero false).mul (.zero false) = .zero false
    | _ => False := by
  have arg := finite_words_argument packet finite lane sum epsilonAdded
  cases v with
  | nan _ | zero _ => exact arg
  | inf sign => cases sign <;> first | exact masked_overflow | exact Bool.noConfusion arg
  | fin x =>
    let w := RootExecution.select x arg proposal
    exact ⟨w.val,w.property,fun ok => RootExecution.select_valid arg ok,masked w.property⟩

end
end FlashKda.FiniteMask
