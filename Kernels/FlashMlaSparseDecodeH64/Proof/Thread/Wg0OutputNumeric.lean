-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0
import Lemmas.Flow.Widen
public import Lemmas.Flow.FmaRun
import Lemmas.Flow.Join
import Lemmas.Flow.Scalars

@[expose] public section

/-! # The softmax warpgroup's per-tile output conversion -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

open PTX PTX.Proof PTX.Flow
open Assumptions

noncomputable section
set_option maxRecDepth 100000

/-- The interleaved four-instruction conversion of a consecutive pair of O columns starts
two instructions after the tile load. -/
def outputPairPC (j : Fin 4) (i : Nat) : Nat := (Site.oWait j).pc + 1 + 4 * i

private def packReg (j : Fin 4) (i : Nat) : Nat :=
  if j.val = 0 ∧ i = 0 then 3576
  else [3577, 3641, 3705, 3769].getD j.val 0 + 2 * i

private def packOp (j : Fin 4) (i : Nat) : Op :=
  .move ⟨.pack, .int .b 64, [some (packReg j i)],
    [.reg (outputFirst j + 2 * i), .reg (outputFirst j + 2 * i + 1)]⟩

private def mulOp (j : Fin 4) (i : Nat) : Op :=
  .float {
    op := .mul
    ty := ⟨.f32, 2⟩
    dsts := [some (packReg j i - 1)]
    srcs := [.reg (packReg j i), .reg 3577] }

private def unpackOp (j : Fin 4) (i : Nat) : Op :=
  let d := stageFirst j + 3 * i
  .move ⟨.unpack, .int .b 64, [some (d + 1), some (d + 2)], [.reg (packReg j i - 1)]⟩

private def cvtOutputOp (d lo hi : Nat) : Op :=
  .cvt {
    dst := .packed (.float .bf16) 2
    src := .float .f32
    rnd := some .rn
    d := d
    srcs := [.reg hi, .reg lo] }

open Lean Elab Tactic Meta in
elab "output_code" : tactic => do
  let target ← whnf (← getMainTarget)
  let some (_, lhs, _) := target.eq? | throwError "expected an instruction lookup"
  unless lhs.isAppOfArity ``GetElem?.getElem? 7 do
    throwError "expected a lookup in the frozen instruction table"
  let pc ← PTX.Flow.natValue (lhs.getArg! 6)
  let proof := mkIdent ((`PTX.Kernels.FlashMlaSparseDecodeH64.Flow) ++ Name.mkSimple s!"code_{pc}")
  evalTactic (← `(tactic| exact $proof))

private theorem outputPack_code (j : Fin 4) (i : Fin 32) :
    kernel.code[outputPairPC j i.val]? = some ⟨none, packOp j i.val⟩ := by
  fin_cases j <;> fin_cases i <;> output_code

private theorem outputMul_code (j : Fin 4) (i : Fin 32) :
    kernel.code[outputPairPC j i.val + 1]? = some ⟨none, mulOp j i.val⟩ := by
  fin_cases j <;> fin_cases i <;> output_code

private theorem outputUnpack_code (j : Fin 4) (i : Fin 32) :
    kernel.code[outputPairPC j i.val + 2]? = some ⟨none, unpackOp j i.val⟩ := by
  fin_cases j <;> fin_cases i <;> output_code

private theorem outputCvt_code (j : Fin 4) (i : Fin 32) :
    let d := stageFirst j + 3 * i.val
    kernel.code[outputPairPC j i.val + 3]? = some ⟨none, cvtOutputOp d (d + 1) (d + 2)⟩ := by
  dsimp only
  fin_cases j <;> fin_cases i <;> output_code

private theorem outputNoSegments : Assumption.NoSegments asms := by
  intro a ha L g t
  simp only [asms, all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem exec_outputPack {L : Launch} {g : Nat} {t : TState} {d a b : Nat} {va vb : Value}
    (hpc : 713 ≤ t.pc) (ha : t.regs a = some va) (hb : t.regs b = some vb)
    (hla : va.bytes = 4) (hlb : vb.bytes = 4) :
    execLocalA asms L g t (.move ⟨.pack, .int .b 64, [some d], [.reg a, .reg b]⟩) =
      .ok (PTX.next (setReg t d (joinValue va vb))) := by
  have hd : deadPackWords t.pc = none :=
    deadPackWords.eq_3 _ (by omega) (by omega)
  have hnone : ∀ h ∈ asms, h.localRule L g t
      (.move ⟨.pack, .int .b 64, [some d], [.reg a, .reg b]⟩) = none := by
    intro h hmem
    simp only [asms, all, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | simp [paramPointers, sharedBits, deadPackRule, peerPackRule, hd]
  rw [execLocalA_noSegment outputNoSegments.segFreeAt, execLocalRule_of_none hnone]
  simp [execLocal, Op.rule, MoveInstr.rule, execMove, readValue, readReg, DType.width,
    ha, hb, hla, hlb, bind, Except.bind, pure, Except.pure]

theorem outputNoUnpack : NoUnpack64 asms := by
  intro lo hi src L g t h hmem
  simp only [asms, all, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | (simp [paramPointers, sharedBits, deadPackRule, peerPackRule])

theorem outputMul_ideal : Assumption.IdealFor asms .mulF32x2 :=
  Assumption.idealFor_head (by simp) outputNoSegments.tail

private theorem scoreHalf_cases {v : Value} (h : scoreHalf v) :
    (∃ x, v = fl x) ∨ ∃ b : BitVec 64, v = .bits 32 b ∧ b.toNat < 2 ^ 32 := by
  unfold scoreHalf at h
  split at h
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, rfl, h⟩
  · exact h.elim

theorem split_join_words {lo hi : Value} (hl : scoreHalf lo) (hh : scoreHalf hi) :
    splitValue 64 (joinValue lo hi) = (lo, hi) := by
  rcases scoreHalf_cases hl with ⟨x, rfl⟩ | ⟨x, rfl, hx⟩
  · rcases scoreHalf_cases hh with ⟨y, rfl⟩ | ⟨y, rfl, hy⟩ <;> rfl
  rcases scoreHalf_cases hh with ⟨y, rfl⟩ | ⟨y, rfl, hy⟩
  · rfl
  have ex : BitVec.ofNat 64 x.toNat = x := by simp
  have ey : BitVec.ofNat 64 y.toNat = y := by simp
  rw [join_bits32 ex.symm ey.symm hx hy]
  have hmax : x.toNat + y.toNat * 2 ^ 32 < 2 ^ 64 := by omega
  have hd : (x.toNat + y.toNat * 2 ^ 32) / 2 ^ 32 = y.toNat := by
    rw [Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hx, Nat.zero_add]
  have hm : (x.toNat + y.toNat * 2 ^ 32) % 2 ^ 32 = x.toNat := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  simp only [splitValue, truncBits, Nat.reduceDiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax,
    hd, hm, Nat.mod_eq_of_lt hy, ex, ey]

private theorem outputScale_lo (P : Params) (L : Launch) (g : Nat) (d : D) :
    valFloat .f32 (splitValue 64 (oScaleWord P L g d)).1 = .ok (oScale P L g d) := by
  by_cases h : d.li = 0
  · have hz : splitValue 64 (joinValue (b32 0) (b32 0)) = (b32 0, b32 0) := rfl
    simpa only [oScaleWord, oScale, h, ↓reduceIte, hz] using valFloat_z0
  · simpa only [oScaleWord, h, ↓reduceIte, fl, joinValue, splitValue] using
      (valFloat_float (fmt := .f32) (x := oScale P L g d))

private theorem outputScale_hi (P : Params) (L : Launch) (g : Nat) (d : D) :
    valFloat .f32 (splitValue 64 (oScaleWord P L g d)).2 = .ok (oScale P L g d) := by
  by_cases h : d.li = 0
  · have hz : splitValue 64 (joinValue (b32 0) (b32 0)) = (b32 0, b32 0) := rfl
    simpa only [oScaleWord, oScale, h, ↓reduceIte, hz] using valFloat_z0
  · simpa only [oScaleWord, h, ↓reduceIte, fl, joinValue, splitValue] using
      (valFloat_float (fmt := .f32) (x := oScale P L g d))

private theorem exec_outputCvt {L : Launch} {g : Nat} {t : TState} {d lo hi : Nat}
    {x y : ℝ} (hl : t.regs lo = some (fl x)) (hh : t.regs hi = some (fl y)) :
    execLocalA asms L g t (cvtOutputOp d lo hi) =
      .ok (PTX.next (setReg t d (bf16Pair x y))) := by
  rw [execLocalA_noSegment outputNoSegments.segFreeAt]
  have hc : cvtBf16x2.localRule L g t (cvtOutputOp d lo hi) =
      some (.ok (PTX.next (setReg t d (bf16Pair x y)))) := by
    simp [cvtBf16x2, cvtOutputOp, f32ValueOf, readValue, readReg, hl, hh, fl, pure, Except.pure,
      valFloat_float, Except.toOption]
  change
    (match [idealArith, approx, mulBf16x2, cvtBf16x2, cvtUe8m0, lg2Exact, ncReadOnly,
      paramPointers, storeDrain, sharedBits].findSome?
      (fun h => h.localRule L g t (cvtOutputOp d lo hi)) with
    | some r => r
    | none => execLocal L g t (cvtOutputOp d lo hi)) = _
  simp only [List.findSome?_cons,
    show idealArith.localRule L g t (cvtOutputOp d lo hi) = none from rfl,
    show approx.localRule L g t (cvtOutputOp d lo hi) = none from rfl,
    show mulBf16x2.localRule L g t (cvtOutputOp d lo hi) = none from rfl, hc]


theorem outputWords_at {words : List Value} (hw : goodOutputWords words = true)
    {i : Nat} (hi : i < 64) :
    scoreHalf (words.getD i (b32 0)) ∧
      valFloat .f32 (words.getD i (b32 0)) = .ok (outputReal words i) := by
  simp only [goodOutputWords, Bool.and_eq_true, beq_iff_eq] at hw
  have hlen : words.length = 64 := hw.1
  have hi' : i < words.length := by omega
  have hmem : words.getD i (b32 0) ∈ words := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    exact List.getElem_mem _
  have hh := List.all_eq_true.mp hw.2 _ hmem
  simp only [outputWord, Bool.and_eq_true, decide_eq_true_eq] at hh
  refine ⟨hh.1, ?_⟩
  unfold outputReal
  cases hq : valFloat .f32 (words.getD i (b32 0)) with
  | error f =>
    simp only [List.getD_eq_getElem?_getD] at hq
    simp [hq, Except.toOption] at hh
  | ok x => rfl

theorem at_set_keep {t : TState} {p r : Nat} {v : Value} {F : List (Nat × Value)}
    (ht : At t p F) (hr : ∀ q ∈ F, q.1 ≠ r) : At (PTX.next (setReg t r v)) (p + 1) F :=
  ⟨congrArg (· + 1) ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, holds_update ht.2.2.2.2 hr⟩

private theorem pack_ne_scale (j : Fin 4) (i : Fin 32) : 3577 ≠ packReg j i.val := by
  fin_cases j <;> fin_cases i <;> decide +kernel

private theorem run_outputPair {P : Params} {L : Launch} {g : Nat} {d : D} (j : Fin 4)
    (i : Fin 32) {F : List (Nat × Value)} {t : TState}
    (hat : At t (outputPairPC j i.val) F) (hd : goodOutputWords d.oWords = true)
    (hL : t.regs (outputFirst j + 2 * i.val) = some (d.oWords.getD (2 * i.val) (b32 0)))
    (hH : t.regs (outputFirst j + 2 * i.val + 1) = some (d.oWords.getD (2 * i.val + 1) (b32 0)))
    (hS : t.regs 3577 = some (oScaleWord P L g d))
    (hpack : ∀ q ∈ F, q.1 ≠ packReg j i.val)
    (hmul : ∀ q ∈ F, q.1 ≠ packReg j i.val - 1)
    (hdst : ∀ q ∈ F, q.1 ≠ stageFirst j + 3 * i.val)
    (hlo : ∀ q ∈ F, q.1 ≠ stageFirst j + 3 * i.val + 1)
    (hhi : ∀ q ∈ F, q.1 ≠ stageFirst j + 3 * i.val + 2) :
    ∃ u, run kernel asms L g 4 t = some u ∧
      At u (outputPairPC j (i.val + 1))
        ((stageFirst j + 3 * i.val, stagePair P L g d i.val) :: F) := by
  let a := d.oWords.getD (2 * i.val) (b32 0)
  let b := d.oWords.getD (2 * i.val + 1) (b32 0)
  let s := oScale P L g d
  let x := outputReal d.oWords (2 * i.val)
  let y := outputReal d.oWords (2 * i.val + 1)
  let dp := packReg j i.val
  let dm := dp - 1
  let dv := stageFirst j + 3 * i.val
  have hs := outputNoSegments
  have hi := i.isLt
  have ⟨ha, hax⟩ : scoreHalf a ∧ valFloat .f32 a = .ok x := outputWords_at hd (by omega)
  have ⟨hb, hby⟩ : scoreHalf b ∧ valFloat .f32 b = .ok y := outputWords_at hd (by omega)
  let t₁ := PTX.next (setReg t dp (joinValue a b))
  have hr₁ : run kernel asms L g 1 t = some t₁ := by
    apply run_local (outputPack_code j i) rfl hat
    have hp : 713 ≤ t.pc := by
      rw [hat.1]
      fin_cases j <;> simp [outputPairPC, Site.pc] <;> omega
    exact exec_outputPack hp hL hH (scoreHalf_bytes ha) (scoreHalf_bytes hb)
  have ht₁ : At t₁ (outputPairPC j i.val + 1) F := at_set_keep hat hpack
  have hp (q : Nat) : t₁.regs q = Function.update t.regs dp (some (joinValue a b)) q := rfl
  have hrp : t₁.regs dp = some (joinValue a b) := Function.update_self ..
  have hrs : t₁.regs 3577 = some (oScaleWord P L g d) := by
    rw [hp, Function.update_of_ne (pack_ne_scale j i), hS]
  let m := Value.pair (fl (x * s)) (fl (y * s))
  let t₂ := PTX.next (setReg t₁ dm m)
  have hr₂ : run kernel asms L g 1 t₁ = some t₂ := by
    apply run_local (outputMul_code j i) rfl ht₁
    have hsplit := split_join_words ha hb
    exact exec_fmul2 outputMul_ideal.at hrp hrs
      (hsplit ▸ hax) (hsplit ▸ hby) (outputScale_lo P L g d) (outputScale_hi P L g d)
  have ht₂ : At t₂ (outputPairPC j i.val + 2) F := at_set_keep ht₁ hmul
  let t₃ := PTX.next (setReg (setReg t₂ (dv + 1) (fl (x * s))) (dv + 2) (fl (y * s)))
  have hr₃ : run kernel asms L g 1 t₂ = some t₃ := by
    apply run_local (outputUnpack_code j i) rfl ht₂
    exact exec_unpack64 (Function.update_self ..) rfl rfl hs.segFreePc outputNoUnpack
  have ht₃ : At t₃ (outputPairPC j i.val + 3) F :=
    ⟨congrArg (· + 1) ht₂.1, ht₂.2.1, ht₂.2.2.1, ht₂.2.2.2.1,
      holds_update (holds_update ht₂.2.2.2.2 hlo) hhi⟩
  have hlo' : t₃.regs (dv + 1) = some (fl (x * s)) := by
    change Function.update (Function.update t₂.regs (dv + 1) (some (fl (x * s)))) (dv + 2)
      (some (fl (y * s))) (dv + 1) = _
    rw [Function.update_of_ne (show dv + 1 ≠ dv + 2 by omega), Function.update_self]
  have hhi' : t₃.regs (dv + 2) = some (fl (y * s)) := Function.update_self ..
  let t₄ := PTX.next (setReg t₃ dv (stagePair P L g d i.val))
  have hr₄ : run kernel asms L g 1 t₃ = some t₄ := by
    apply run_local (outputCvt_code j i) rfl ht₃
    change execLocalA asms L g t₃ (cvtOutputOp dv (dv + 1) (dv + 2)) = _
    rw [exec_outputCvt hlo' hhi']
    simp only [t₄, stagePair, bf16Pair, x, y, s, mul_comm]
  have ht₄ : At t₄ (outputPairPC j i.val + 3 + 1) ((dv, stagePair P L g d i.val) :: F) :=
    ht₃.set hdst
  exact ⟨t₄, run_comp (run_comp (run_comp hr₁ hr₂) hr₃) hr₄,
    by simpa only [outputPairPC, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using ht₄⟩

private def waitLive (j : Fin 4) : List Nat :=
  (Flow.live (Site.oWait j).pc).filter tracked.contains

private def convertedFacts (P : Params) (L : Launch) (g : Nat) (d : D) (j : Fin 4)
    (n : Nat) : List (Nat × Value) :=
  (List.range n).reverse.map (fun i => (stageFirst j + 3 * i, stagePair P L g d i))

private theorem convertedFacts_succ (P : Params) (L : Launch) (g : Nat) (d : D) (j : Fin 4)
    (i : Nat) :
    convertedFacts P L g d j (i + 1) =
      (stageFirst j + 3 * i, stagePair P L g d i) :: convertedFacts P L g d j i := by
  simp [convertedFacts, List.range_succ]

private theorem outputDsts_liveWait (j : Fin 4) :
    ∀ r ∈ outputDsts j, r ∈ waitLive j := by
  have h : (outputDsts j).all (fun r => (waitLive j).contains r) = true := by
    fin_cases j <;> decide +kernel
  simpa using List.all_eq_true.mp h

private theorem scale_liveWait (j : Fin 4) : 3577 ∈ waitLive j := by
  fin_cases j <;> decide +kernel

theorem outputWord_value (P : Params) (L : Launch) (g : Nat) (d : D) (j : Fin 4) (i : Fin 64) :
    valueOf P L g d (outputFirst j + i.val) = d.oWords.getD i.val (b32 0) := by
  fin_cases j <;> fin_cases i <;> rfl

theorem outputStage_value (P : Params) (L : Launch) (g : Nat) (d : D) (j : Fin 4) (i : Fin 32) :
    valueOf P L g d (stageFirst j + 3 * i.val) = stagePair P L g d i.val := by
  fin_cases j <;> fin_cases i <;> rfl

private theorem waitLive_cover (j : Fin 4) :
    ∀ r ∈ waitLive j, r ≤ outputFirst j + 64 ∨ (2992 ≤ r ∧ r ≤ 2999) ∨ r = 3577 ∨
      r = 3832 := by
  have h : (waitLive j).all (fun r => decide (r ≤ outputFirst j + 64 ∨
      (2992 ≤ r ∧ r ≤ 2999) ∨ r = 3577 ∨ r = 3832)) = true := by
    fin_cases j <;> decide +kernel
  simpa using List.all_eq_true.mp h

private theorem notMem_pairWrites (j : Fin 4) (i : Fin 32) :
    packReg j i.val ∉ waitLive j ∧ packReg j i.val - 1 ∉ waitLive j ∧
      stageFirst j + 3 * i.val ∉ waitLive j ∧ stageFirst j + 3 * i.val + 1 ∉ waitLive j ∧
      stageFirst j + 3 * i.val + 2 ∉ waitLive j := by
  have hi := i.isLt
  have hpack : 3500 ≤ packReg j i.val ∧ packReg j i.val < 3832 ∧
      packReg j i.val ≠ 3577 ∧ packReg j i.val - 1 ≠ 3577 := by
    fin_cases j <;> simp [packReg] <;> (try split_ifs) <;> omega
  have hled : outputFirst j + 64 < stageFirst j := by fin_cases j <;> decide
  have hmax : stageFirst j ≤ 2320 := by fin_cases j <;> decide
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  all_goals rcases waitLive_cover j _ h with ht | ht | ht | ht <;> omega

private theorem pairRegs_at {P : Params} {L : Launch} {g : Nat} {d : D}
    (j : Fin 4) (i : Fin 32) {t : TState}
    (h : Holds t.regs (factsFrom (waitLive j) (valueOf P L g d))) :
    t.regs (outputFirst j + 2 * i.val) = some (d.oWords.getD (2 * i.val) (b32 0)) ∧
      t.regs (outputFirst j + 2 * i.val + 1) =
        some (d.oWords.getD (2 * i.val + 1) (b32 0)) ∧
      t.regs 3577 = some (oScaleWord P L g d) := by
  have hi := i.isLt
  have hget (n : Nat) (hn : n < 64) := holds_mem h (List.mem_map.mpr
    ⟨outputFirst j + n, outputDsts_liveWait j _
      (by rw [outputDsts, List.mem_range'_1]; omega), rfl⟩)
  have h0 := hget (2 * i.val) (by omega)
  have h1 := hget (2 * i.val + 1) (by omega)
  refine ⟨?_, ?_, holds_mem h (List.mem_map.mpr ⟨3577, scale_liveWait j, rfl⟩)⟩
  · rw [outputWord_value P L g d j ⟨2 * i.val, by omega⟩] at h0
    exact h0
  · rw [outputWord_value P L g d j ⟨2 * i.val + 1, by omega⟩] at h1
    exact h1

private theorem liveStage_cover (j : Fin 4) :
    ∀ r ∈ (Flow.live (Site.oStage j 0).pc).filter tracked.contains,
      (waitLive j).contains r || (List.range' (stageFirst j) 32 3).contains r := by
  apply List.all_eq_true.mp
  fin_cases j <;> decide +kernel

/-- The local conversion of one output tile reads all 64 words, applies the duplicated
normalization scale, and leaves the 32 packed BF16 values for the eight vector stores. -/
theorem run_outputTile {P : Params} {L : Launch} {g : Nat} {d : D} (j : Fin 4) {t : TState}
    (h : At t ((Site.oWait j).pc + 1)
      (factsFrom ((Flow.live (Site.oWait j).pc).filter tracked.contains) (valueOf P L g d)))
    (hv : goodOutputWords d.oWords = true) :
    ∃ u, run kernel asms L g 128 t = some u ∧
      At u (Site.oStage j 0).pc
        (factsFrom ((Flow.live (Site.oStage j 0).pc).filter tracked.contains)
          (valueOf P L g d)) := by
  let F := factsFrom (waitLive j) (valueOf P L g d)
  have hiter (n : Nat) (hn : n ≤ 32) :
      ∃ u, run kernel asms L g (4 * n) t = some u ∧
        At u (outputPairPC j n) (convertedFacts P L g d j n ++ F) := by
    induction n with
    | zero => exact ⟨t, rfl, by simpa [outputPairPC, convertedFacts, F, waitLive] using h⟩
    | succ n ih =>
      have hn' : n < 32 := by omega
      let i : Fin 32 := ⟨n, hn'⟩
      obtain ⟨u, hr, hu⟩ := ih (by omega)
      have hcarry : Holds u.regs F := ((holds_append _ _ _).mp hu.2.2.2.2).2
      obtain ⟨hlo, hhi, hs⟩ := pairRegs_at j i hcarry
      obtain ⟨hp, hm, hd, h1, h2⟩ := notMem_pairWrites j i
      have hbase : 3575 ≤ packReg j n := by
        fin_cases j <;> simp [packReg] <;> (try split_ifs) <;> omega
      have hfirst : stageFirst j ≤ 2320 := by fin_cases j <;> decide
      have hf (r : Nat) (hr : r ∉ waitLive j)
          (hne : ∀ k < n, stageFirst j + 3 * k ≠ r) :
          ∀ q ∈ convertedFacts P L g d j n ++ F, q.1 ≠ r := by
        intro q hq
        rcases List.mem_append.mp hq with hq' | hq'
        · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq'
          exact hne k (List.mem_range.mp (List.mem_reverse.mp hk))
        · exact not_mem_factsFrom hr q hq'
      obtain ⟨v, hrv, hv'⟩ := run_outputPair j i hu hv hlo hhi hs
        (hf _ hp (fun k hk => by dsimp [i]; omega)) (hf _ hm (fun k hk => by dsimp [i]; omega))
        (hf _ hd (fun k hk => by dsimp [i]; omega)) (hf _ h1 (fun k hk => by dsimp [i]; omega))
        (hf _ h2 (fun k hk => by dsimp [i]; omega))
      refine ⟨v, ?_, ?_⟩
      · rw [Nat.mul_succ]
        exact run_comp hr hrv
      · simpa only [convertedFacts_succ, List.cons_append] using hv'
  obtain ⟨u, hr, hu⟩ := hiter 32 (by decide)
  have hpc : outputPairPC j 32 = (Site.oStage j 0).pc := by fin_cases j <;> rfl
  rw [hpc] at hu
  refine ⟨u, hr, hu.mono (holds_of_pointwise ?_)⟩
  intro r hm
  have hcov := liveStage_cover j r hm
  simp only [Bool.or_eq_true] at hcov
  rcases hcov with hwait | hstage
  · exact holds_mem ((holds_append _ _ _).mp hu.2.2.2.2).2
      (List.mem_map.mpr ⟨r, by simpa using hwait, rfl⟩)
  · have hstage' : r ∈ List.range' (stageFirst j) 32 3 := by simpa using hstage
    rw [List.mem_range'] at hstage'
    obtain ⟨i, hi, rfl⟩ := hstage'
    rw [outputStage_value P L g d j ⟨i, hi⟩]
    exact holds_mem ((holds_append _ _ _).mp hu.2.2.2.2).1
      (List.mem_map.mpr ⟨i, List.mem_reverse.mpr (List.mem_range.mpr hi), rfl⟩)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
