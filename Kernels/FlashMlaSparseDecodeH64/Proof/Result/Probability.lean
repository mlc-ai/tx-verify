-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0
import Lemmas.Flow.SplitJoin
import Lemmas.Flow.Recip

public section

/-! # The probability of valid and masked slots -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
open PTX PTX.Proof PTX.Flow PTX.Assumption Wg0

noncomputable section

/-- A padded slot carries a negative-infinity score and contributes zero. -/
def shiftedWeight (scale ref : ℝ) (score : WithBot ℝ) : ℝ :=
  match score with
  | ⊥ => 0
  | some s => 2 ^ (scale * s - ref)

private def exponentArg (scale ref : ℝ) (score : WithBot ℝ) : WithBot ℝ :=
  score.map fun s => s * scale - ref

private def scoreReal : WithBot ℝ → EReal
  | ⊥ => ⊥
  | some x => (x : EReal)

private theorem read_peakVal (s : WithBot ℝ) :
    readEReal .f32 (peakVal s) = some (.ok (scoreReal s)) := by
  cases s
  · rfl
  · exact readEReal_of_valFloat valFloat_float

private theorem erealValue_scoreReal (s : WithBot ℝ) :
    erealValue .f32 (scoreReal s) = peakVal s := by
  cases s
  · simp [scoreReal, peakVal, erealValue, negInf, FVal.toValue, FloatFmt.bytes]
    rfl
  · exact erealValue_coe _ _

private theorem exponentArith (scale ref : ℝ) (hscale : 0 < scale) (s : WithBot ℝ) :
    (mulEReal (scoreReal s) (scale : EReal)).bind (addEReal · (-ref : ℝ)) =
      some (scoreReal (exponentArg scale ref s)) := by
  cases s with
  | bot =>
    have hn : (scale : EReal) ≠ 0 := (EReal.coe_pos.mpr hscale).ne'
    simp [scoreReal, exponentArg, mulEReal, addEReal, hn, EReal.bot_mul_coe_of_pos hscale]
  | coe x =>
    simp only [scoreReal, exponentArg, WithBot.map_coe, mulEReal_coe, Option.bind_some,
      addEReal_coe, sub_eq_add_neg]

private theorem unpack_peakVal (a b : WithBot ℝ) :
    unpackE 64 (.pair (peakVal a) (peakVal b)) = .ok (peakVal a, peakVal b) := by
  cases a <;> cases b <;> rfl

private theorem exponentResult (scale ref : ℝ) (s : WithBot ℝ) :
    ((ex2E true (peakVal (exponentArg scale ref s))).bind (valFloat .f32)) =
      .ok (shiftedWeight scale ref s) := by
  cases s with
  | bot =>
    have hx : ex2E true negInf = .ok (.float .f32 0) := by
      unfold ex2E
      change (match (none : Option (Exec Value)) with
        | some result => result
        | none => coreFloat (ex2I true) [negInf]) = .ok (.float .f32 0)
      rfl
    simp [exponentArg, peakVal, hx, shiftedWeight, valFloat_float, Except.bind]
  | coe x =>
    change ((ex2E true (fl (x * scale - ref))).bind (valFloat .f32)) =
      .ok ((2 : ℝ) ^ (scale * x - ref))
    rw [ex2E_fin (valFloat_fl _)]
    simp [Except.bind, valFloat_float, mul_comm x scale]

/-- The exact value in the two packed scale operands comes from the launch's little-endian word. -/
theorem probScale_features {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    pairRead (probScale L) = some (.ok ((P.scale : EReal), (P.scale : EReal))) := by
  let n := Wg0.paramWord L 28 4
  have hn : n < 2 ^ 32 := by
    obtain ⟨w, _, hbytes, _⟩ := hpre.paramScale
    have hr := Thread.paramWord_four (L := L) (off := 28) (x := w) fun j hj => by
      simpa using hbytes j hj
    change Thread.paramWord L 28 4 = w % 2 ^ 32 at hr
    change Thread.paramWord L 28 4 < 2 ^ 32
    rw [hr]
    exact Nat.mod_lt _ (by decide)
  have h64 : n < 2 ^ 64 := hn.trans (by decide)
  have hbits : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
  have hr : valFloat .f32 (b32 n) = .ok P.scale := by
    change bitsAsFloat .f32 (b32 n) = .ok P.scale
    rw [bitsAsFloat_eq (by intro f hf; cases hf)]
    simp only [b32, Value.bitPattern, Value.bytes, FloatFmt.bytes,
      Nat.reduceDiv, hbits, ↓reduceIte]
    have h := scaleWord hpre
    change (f32Value n).map (fun q : ℚ => (q : ℝ)) = some P.scale at h
    obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
    change FloatFmt.f32.decode n = some r at hr
    simp [hr, he, pure, Except.pure]
  have hsp : splitValue 64 (joinValue (b32 n) (b32 n)) = (b32 n, b32 n) :=
    split_join_bits (hbits.symm ▸ hn)
  exact pairRead_of (by rw [show splitValue 64 (probScale L) = _ from hsp]; exact hr)
    (by rw [show splitValue 64 (probScale L) = _ from hsp]; exact hr)

/-- The probability calculation succeeds on scores and masks supplied by the GEMM and index
handoffs, and preserves each slot's shifted weight. -/
theorem probPair_eq {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {d : D} {i : Nat} (a b : WithBot ℝ)
    (hs : d.scoreSums i = .pair (peakVal a) (peakVal b)) :
    probPair L d i =
      some (shiftedWeight P.scale (reference d) a, shiftedWeight P.scale (reference d) b) := by
  let z := reference d
  let v := joinValue (fl (-z)) (fl (-z))
  have hb : pairRead v = some (.ok (((-z : ℝ) : EReal), ((-z : ℝ) : EReal))) :=
    pairRead_of (valFloat_fl _) (valFloat_fl _)
  have hw : pairRead (.pair (peakVal a) (peakVal b)) =
      some (.ok (scoreReal a, scoreReal b)) := by
    simp only [pairRead, splitValue, read_peakVal, pure, Except.pure]
  have hf : fma2E (.pair (peakVal a) (peakVal b)) (probScale L) v =
      .ok (.pair (peakVal (exponentArg P.scale z a)) (peakVal (exponentArg P.scale z b))) := by
    simp only [fma2E, idealFma2, hw, probScale_features hpre, hb, bindRead,
      exponentArith _ _ hpre.scalePos, erealValue_scoreReal, pure, Except.pure]
  unfold probPair
  rw [hs]
  change _ = some (shiftedWeight P.scale z a, shiftedWeight P.scale z b)
  simp only [show joinValue (fl (-reference d)) (fl (-reference d)) = v from rfl, hf,
    unpack_peakVal, Except.toOption, bind, Option.bind_some]
  cases h₁ : ex2E true (peakVal (exponentArg P.scale z a)) with
  | error e => have h := exponentResult P.scale z a; rw [h₁] at h; cases h
  | ok p =>
    cases h₂ : ex2E true (peakVal (exponentArg P.scale z b)) with
    | error e => have h := exponentResult P.scale z b; rw [h₂] at h; cases h
    | ok q =>
      have hp := exponentResult P.scale z a
      have hq := exponentResult P.scale z b
      rw [h₁] at hp
      rw [h₂] at hq
      change valFloat .f32 p = .ok (shiftedWeight P.scale z a) at hp
      change valFloat .f32 q = .ok (shiftedWeight P.scale z b) at hq
      simp [hp, hq, pure]

/-- A finite score's shifted weight is its original attention weight times the inverse reference. -/
theorem shiftedWeight_fin (scale ref score : ℝ) :
    shiftedWeight scale ref (some score) = 2 ^ (scale * score) * 2 ^ (-ref) := by
  change (2 : ℝ) ^ (scale * score - ref) = _
  rw [sub_eq_add_neg, Real.rpow_add (by norm_num : 0 < (2 : ℝ))]

/-- The shifted weight vanishes exactly for a masked slot. -/
theorem shiftedWeight_zero (scale ref : ℝ) (score : WithBot ℝ) :
    shiftedWeight scale ref score = 0 ↔ score = ⊥ := by
  cases score with
  | bot => simp [shiftedWeight]
  | coe x =>
    have hp : 0 < (2 : ℝ) ^ (scale * x - ref) := Real.rpow_pos_of_pos (by norm_num) _
    change (2 : ℝ) ^ (scale * x - ref) = 0 ↔ (x : WithBot ℝ) = ⊥
    simp [hp.ne']

/-- The next reference uses the local row maximum only when the warp votes to update it. -/
def voteReference (before : ℝ) (rowMax : WithBot ℝ) (update : Bool) : ℝ :=
  if update then
    match rowMax with
    | ⊥ => before
    | some x => max x before
  else before

private theorem max_reference (d : D) (m : WithBot ℝ) :
    peerMaxE (peakVal m) (miVal d) = .ok (fl (voteReference (reference d) m true)) := by
  have hd := readEReal_of_valFloat (valFloat_miVal d)
  cases m with
  | bot =>
    have hb : readEReal .f32 negInf = some (.ok (⊥ : EReal)) := rfl
    simp only [peerMaxE, idealMax, peakVal, hb, hd, bindRead, bot_sup_eq, erealValue_coe, pure,
      Except.pure, voteReference, ↓reduceIte, fl]
  | coe x =>
    change peerMaxE (fl x) (miVal d) = .ok (fl (max x (reference d)))
    have hx : readEReal .f32 (fl x) = some (.ok (x : EReal)) := readEReal_of_valFloat valFloat_float
    simp only [peerMaxE, idealMax, hx, hd, bindRead, coe_max, erealValue_coe, pure, Except.pure]
    rfl

/-- The vote transition keeps a finite reference and produces the exact ratio of consecutive
reference scales. -/
theorem afterReferenceVote_ratio {d : D} (m : WithBot ℝ) (hr : d.blockMax = peakVal m) (r : Bool) :
    ∃ d', afterReferenceVote d r = some d' ∧
      reference d' = voteReference (reference d) m r ∧
      valFloat .f32 d'.gainWord = .ok ((2 : ℝ) ^ (reference d - reference d')) := by
  cases r
  · let d' : D := { d with gainWord := b32 1065353216 }
    have hd : reference d' = reference d := rfl
    refine ⟨d', rfl, hd, ?_⟩
    rw [hd, sub_self, Real.rpow_zero]
    exact valFloat_one
  · let c := voteReference (reference d) m true
    let gain := (2 : ℝ) ^ (reference d - c)
    let d' : D := { d with mi := c, miUpd := true, gainWord := fl gain }
    have hd : reference d' = c := by simp [reference, d']
    have ha : valFloat .f32 (fl c) = .ok c := valFloat_fl c
    have hsub : subE true (miVal d) (fl c) = .ok (fl (reference d - c)) :=
      subE_fin (valFloat_miVal d) ha
    have hpow : ex2E true (fl (reference d - c)) = .ok (fl gain) := ex2E_fin (valFloat_fl _)
    have hmax : peerMaxE d.blockMax (miVal d) = .ok (fl c) := hr ▸ max_reference d m
    refine ⟨d', ?_, hd, ?_⟩
    · simp [afterReferenceVote, hmax, ha, hsub, hpow, d', Except.toOption, pure]
    · rw [hd]
      exact valFloat_fl gain

/-- The exact half-row sum after adding the 16 probability pairs and their two lane sums. -/
theorem probabilityUpdate_terms {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}
    (hpre : Pre P L mem0) (d : D) (lo hi : Fin 16 → WithBot ℝ) (gain : ℝ)
    (hs : ∀ i : Fin 16, d.scoreSums i.val = .pair (peakVal (lo i)) (peakVal (hi i)))
    (hg : valFloat .f32 d.gainWord = .ok gain) :
    let pair := fun i : Fin 16 =>
      (shiftedWeight P.scale (reference d) (lo i), shiftedWeight P.scale (reference d) (hi i))
    let ps := (List.finRange 16).map pair
    ∃ d', probabilityUpdate L g d = some d' ∧ d'.sumUpd = true ∧
      d'.lh = (if d.sumUpd then d.lh else 0) * gain +
        ((ps.map Prod.fst).sum + (ps.map Prod.snd).sum) ∧
      (∀ slot, 32 * half L g ≤ slot → slot < 32 * half L g + 32 →
        let i := slot - 32 * half L g
        let v := ps.getD (i/2) (0, 0)
        d'.pw (head L g) slot = if i % 2 = 0 then v.1 else v.2) := by
  let pair := fun i : Fin 16 =>
    (shiftedWeight P.scale (reference d) (lo i), shiftedWeight P.scale (reference d) (hi i))
  have hmap (xs : List (Fin 16)) :
      (xs.mapM fun i => probPair L d i.val) = some (xs.map pair) := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      simp [List.mapM_cons, probPair_eq hpre (lo i) (hi i) (hs i), pair, ih]
  let ps := (List.finRange 16).map pair
  let d' : D := { d with
    sumUpd := true
    lh := (if d.sumUpd then d.lh else 0) * gain +
      ((ps.map Prod.fst).sum + (ps.map Prod.snd).sum)
    pw := fun h slot => if h = head L g ∧ 32 * half L g ≤ slot ∧ slot < 32 * half L g + 32 then
      let i := slot - 32 * half L g
      let p := ps.getD (i/2) (0, 0)
      if i % 2 = 0 then p.1 else p.2
    else d.pw h slot }
  refine ⟨d', ?_, rfl, rfl, ?_⟩
  · simp [probabilityUpdate, hmap, hg, Except.toOption, d', ps, pure]
  · intro slot hlo hhi
    simp [d', hlo, hhi, ps, pair]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
