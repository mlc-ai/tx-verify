-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeNumerics
import Lemmas.Flow.FmaRun
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part133
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Flow.Code.Part138

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

/-- Flipping the low swizzle bit changes the odd neighbor's address by one signed vector. -/
def finalizeVectorDelta (l : Launch) (g : Nat) : Nat :=
  if rowOf l g % 2 = 0 then 16 else 2 ^ 32 - 16

def finalizeVectorAddress (l : Launch) (g : Nat) (stage : Fin 2) (chunk : Fin 16)
    (half : Fin 2) : Nat :=
  (outputChunkLoc l g stage 0 (rowOf l g) (finalizeVector chunk half).val).addr

private theorem vectorAddressBound {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) (chunk : Fin 16) (half : Fin 2) :
    finalizeVectorAddress l g stage chunk half < 2 ^ 32 := by
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  have hPhase : rowOf l g % 8 < 8 := Nat.mod_lt _ (by decide)
  have hVec := (finalizeVector chunk half).isLt
  have hXor := Nat.xor_lt_two_pow (n := 3) hVec hPhase
  have hStage := stage.isLt
  have hLimit := hp.shared.2.1
  simp only [finalizeVectorAddress, outputChunkLoc, sharedSlot, Loc.at]
  omega

private theorem finalizeVectorDelta_ok {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) (chunk : Fin 16) :
    (finalizeVectorAddress l g stage chunk 0 + finalizeVectorDelta l g) % (2 ^ 32) =
      finalizeVectorAddress l g stage chunk 1 := by
  let k := chunk.val % 4
  let r := rowOf l g % 8
  have hk : k < 4 := Nat.mod_lt _ (by decide)
  have hr : r < 8 := Nat.mod_lt _ (by decide)
  have hParity : rowOf l g % 2 = r % 2 := by dsimp [r]; omega
  have hXor : if r % 2 = 0 then 16 * ((2 * k + 1) ^^^ r) = 16 * ((2 * k) ^^^ r) + 16
      else 16 * ((2 * k) ^^^ r) = 16 * ((2 * k + 1) ^^^ r) + 16 := by
    clear hParity
    generalize k = x at hk ⊢
    generalize r = y at hr ⊢
    interval_cases x <;> interval_cases y <;> decide
  have h0 := vectorAddressBound hp g stage chunk 0
  have h1 := vectorAddressBound hp g stage chunk 1
  have hAdd (h : r % 2 = 0) :
      finalizeVectorAddress l g stage chunk 1 = finalizeVectorAddress l g stage chunk 0 + 16 := by
    simp only [h, ↓reduceIte] at hXor
    simp only [finalizeVectorAddress, outputChunkLoc, Loc.at, finalizeVector]
    change _ + (_ + 16 * ((2 * k + 1) ^^^ r)) = _ + (_ + 16 * ((2 * k) ^^^ r)) + 16
    rw [hXor]
    omega
  have hSub (h : r % 2 ≠ 0) :
      finalizeVectorAddress l g stage chunk 0 = finalizeVectorAddress l g stage chunk 1 + 16 := by
    simp only [h, ↓reduceIte] at hXor
    simp only [finalizeVectorAddress, outputChunkLoc, Loc.at, finalizeVector]
    change _ + (_ + 16 * ((2 * k) ^^^ r)) = _ + (_ + 16 * ((2 * k + 1) ^^^ r)) + 16
    rw [hXor]
    omega
  unfold finalizeVectorDelta
  rw [hParity]
  by_cases h : r % 2 = 0
  · rw [ite_eq_left h, ← hAdd h, Nat.mod_eq_of_lt h1]
  · rw [ite_eq_right h, hSub h]
    omega

private def betweenVectorOp (stage : Fin 2) (chunk : Fin 16) : Op :=
  .int {
    op := .add
    ty := .int .s 32
    dsts := [some (outputStoreAddrReg stage (finalizeVector chunk 1))]
    srcs := [.reg (outputStoreAddrReg stage (finalizeVector chunk 0)), .reg 6500]}

private theorem betweenVectorCode (stage : Fin 2) (chunk : Fin 16) (hc : chunk.val < 4) :
    kernel.code[outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 0) + 1]? =
      some ⟨none, betweenVectorOp stage chunk⟩ := by
  fin_cases stage <;> fin_cases chunk <;> try (simp at hc)
  · exact Flow.code_8493
  · exact Flow.code_8512
  · exact Flow.code_8531
  · exact Flow.code_8550
  · exact Flow.code_8789
  · exact Flow.code_8808
  · exact Flow.code_8827
  · exact Flow.code_8846

private theorem nextVectorPc (stage : Fin 2) (chunk : Fin 16) :
    outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 0) + 1 +
        (if chunk.val < 4 then 1 else 0) =
      outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 1) - 2 := by
  fin_cases stage <;> fin_cases chunk <;> decide

/-- The first subbox adds its signed vector stride between the stores. The other subboxes
already hold the second base address and proceed directly to unpacking. -/
theorem advanceFinalizeVectorLocal {p : Params} {l : Launch} {m : Mem0}
    {g : Nat} {t : TState} {F : List (Nat × Value)} (hp : Pre p l m)
    (stage : Fin 2) (chunk : Fin 16)
    (ht : At t (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 0) + 1) F)
    (hFirst : t.regs (outputStoreAddrReg stage (finalizeVector chunk 0)) =
      some (b32 (finalizeVectorAddress l g stage chunk 0)))
    (hOther : if chunk.val < 4 then t.regs 6500 = some (b32 (finalizeVectorDelta l g))
      else t.regs (outputStoreAddrReg stage (finalizeVector chunk 1)) =
        some (b32 (finalizeVectorAddress l g stage chunk 1)))
    (hFresh : chunk.val < 4 → outputStoreAddrReg stage (finalizeVector chunk 1) ∉ F.map Prod.fst)
    : ∃ u,
      u.regs (outputStoreAddrReg stage (finalizeVector chunk 1)) =
        some (b32 (finalizeVectorAddress l g stage chunk 1)) ∧
      At u (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 1) - 2) F ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  have hPc := nextVectorPc stage chunk
  by_cases hc : chunk.val < 4
  · rw [ite_eq_left hc] at hPc hOther
    let d := outputStoreAddrReg stage (finalizeVector chunk 1)
    let a := finalizeVectorAddress l g stage chunk 0
    let b := finalizeVectorDelta l g
    let c := finalizeVectorAddress l g stage chunk 1
    let u := next (setReg t d (b32 c))
    have ha : a < 2 ^ 32 := vectorAddressBound hp g stage chunk 0
    have hb : b < 2 ^ 32 := by dsimp [b, finalizeVectorDelta]; split <;> decide
    have hab : a + b < 2 ^ 64 := by omega
    have hSum : truncBits 32 (BitVec.ofNat 64 a + BitVec.ofNat 64 b) = BitVec.ofNat 64 c := by
      rw [← BitVec.ofNat_add, truncBits, toNat_ofNat_lt hab, finalizeVectorDelta_ok hp]
    have hExec : execLocalA Assumptions.all l g t (betweenVectorOp stage chunk) = .ok u := by
      rw [Assumptions.execLocalA_all_eq_numeric]
      rw [Assumptions.execLocalA_eq_nil _ rfl]
      · change execInt l g t ⟨.add, .int .s 32, false, [some d],
          [.reg (outputStoreAddrReg stage (finalizeVector chunk 0)), .reg 6500]⟩ = .ok u
        have hA : t.regs (outputStoreAddrReg stage (finalizeVector chunk 0)) =
            some (b32 a) := hFirst
        have hB : t.regs 6500 = some (b32 b) := hOther
        simp only [execInt, DType.width, readValue, readReg, hA, hB, b32,
          readBits, pure, Except.pure, bind, Except.bind,
          truncBits_ofNat ha (by decide), truncBits_ofNat hb (by decide), hSum, u]
      · have hLo : 8493 ≤ t.pc := by
          rw [ht.1]
          unfold outputStorePc
          omega
        simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
        omega
    have hRun : run kernel Assumptions.all l g 1 t = some u := by
      rw [run_step (ht.1.symm ▸ betweenVectorCode stage chunk hc) rfl ht.2.2.2.1 hExec]
      rfl
    have hAt : At u
        (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 1) - 2) F := by
      refine ⟨(congrArg (· + 1) ht.1).trans hPc, ht.2.1, ht.2.2.1, ht.2.2.2.1, ?_⟩
      apply holds_update ht.2.2.2.2
      intro q hq h
      apply hFresh hc
      change d ∈ F.map Prod.fst
      rw [← h]
      exact List.mem_map_of_mem hq
    have hValue : u.regs d = some (b32 c) := Function.update_self ..
    exact ⟨u, hValue, hAt, run_rtg hRun⟩
  · rw [ite_eq_right hc, Nat.add_zero] at hPc
    rw [ite_eq_right hc] at hOther
    exact ⟨t, hOther, hPc ▸ ht, .refl⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} {g pos : Nat} {t : TState}

theorem advanceFinalizeVector {F : List (Nat × Value)} (hp : Pre p l m) (stage : Fin 2)
    (chunk : Fin 16)
    (ht : At t (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 0) + 1) F)
    (hFirst : t.regs (outputStoreAddrReg stage (finalizeVector chunk 0)) =
      some (b32 (finalizeVectorAddress l g stage chunk 0)))
    (hOther : if chunk.val < 4 then t.regs 6500 = some (b32 (finalizeVectorDelta l g))
      else t.regs (outputStoreAddrReg stage (finalizeVector chunk 1)) =
        some (b32 (finalizeVectorAddress l g stage chunk 1)))
    (hFresh : chunk.val < 4 → outputStoreAddrReg stage (finalizeVector chunk 1) ∉ F.map Prod.fst)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u,
      (u.regs (outputStoreAddrReg stage (finalizeVector chunk 1)) =
        some (b32 (finalizeVectorAddress l g stage chunk 1))) ∧
      At u (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 1) - 2) F ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) none := by
  obtain ⟨u,hAddr,hU,hLocal⟩ := advanceFinalizeVectorLocal hp stage chunk ht hFirst hOther hFresh
  exact ⟨u,hAddr,hU,hr.after_local hLocal⟩

/-- Scalar address operands that survive the load and both packed calculations. -/
def normalizeStoreFacts (l : Launch) (g : Nat) (stage : Fin 2) (chunk : Fin 16) :
    List (Nat × Value) :=
  [(outputStoreAddrReg stage (finalizeVector chunk 0),
      b32 (finalizeVectorAddress l g stage chunk 0)),
    if chunk.val < 4 then (6500, b32 (finalizeVectorDelta l g))
    else (outputStoreAddrReg stage (finalizeVector chunk 1),
      b32 (finalizeVectorAddress l g stage chunk 1))]

private theorem normalizeFacts_keys (l : Launch) (g : Nat) (stage : Fin 2) (chunk : Fin 16) :
    (normalizeStoreFacts l g stage chunk).map Prod.fst =
      [outputStoreAddrReg stage (finalizeVector chunk 0),
        if chunk.val < 4 then 6500 else outputStoreAddrReg stage (finalizeVector chunk 1)] := by
  by_cases hc : chunk.val < 4 <;> simp [normalizeStoreFacts, hc]

private theorem finalizeProductFacts_keys (stage : Fin 2) (chunk : Fin 16)
    (old : Nat → ℝ) (reciprocal : ℝ) :
    (finalizeProductFacts stage chunk old reciprocal).map Prod.fst =
      (List.range 4).map (fun i => finalizePackBase stage chunk + 4 + i) := by
  simp [finalizeProductFacts, List.map_map, Function.comp_def]

private theorem normalizeFacts_preserved (l : Launch) (g : Nat) (stage : Fin 2) (chunk : Fin 16) :
    (∀ r ∈ (normalizeStoreFacts l g stage chunk).map Prod.fst,
      r ∉ finalizeDataRegs stage chunk ∧
      (∀ q ∈ finalizePacks stage chunk, q.1 ≠ r) ∧
      (∀ q ∈ finalizeMuls stage chunk, q.1 ≠ r)) := by
  rw [normalizeFacts_keys]
  fin_cases stage <;> fin_cases chunk <;> decide

private theorem normalizeFirstFacts_preserved (l : Launch) (g : Nat) (stage : Fin 2)
    (chunk : Fin 16) (old : Nat → ℝ) (reciprocal : ℝ) :
    (∀ r ∈ (finalizeProductFacts stage chunk old reciprocal ++
          normalizeStoreFacts l g stage chunk).map Prod.fst,
      ∀ q ∈ finalizeUnpacks stage chunk 0, q.2.1 ≠ r ∧ q.2.2 ≠ r) ∧
    (chunk.val < 4 → outputStoreAddrReg stage (finalizeVector chunk 1) ∉
      (finalizeProductFacts stage chunk old reciprocal ++
        normalizeStoreFacts l g stage chunk).map Prod.fst) := by
  simp only [List.map_append, finalizeProductFacts_keys, normalizeFacts_keys]
  fin_cases stage <;> fin_cases chunk <;> decide

private theorem firstVectorPc (stage : Fin 2) (chunk : Fin 16) :
    finalizeLoadPc stage chunk + 10 =
      outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 0) - 2 := by
  fin_cases stage <;> fin_cases chunk <;> decide

/-- One actual x8 load, its matching wait and all eight following shared writes belong to
the same normalization chunk. Its input values are those supplied by the TMEM handoff. -/
theorem observeNormalizedChunkWithFrame {F : List (Nat × Value)} (hp : Pre p l m) (stage : Fin 2)
    (chunk : Fin 16) (old : Nat → ℝ) (reciprocal : ℝ)
    (ht : At t (finalizeLoadPc stage chunk) (normalizeStoreFacts l g stage chunk ++ F))
    (hAddr : t.regs (finalizeAddressReg stage chunk) =
      some (b32 (outputAddress l g stage (8 * chunk.val))))
    (hRecip : t.regs (finalizeReciprocalPair stage) = some (.pair (fl reciprocal) (fl reciprocal)))
    (hFrame : ∀ r ∈ F.map Prod.fst,
      r ∉ finalizeDataRegs stage chunk ∧
      (∀ q ∈ finalizePacks stage chunk, q.1 ≠ r) ∧
      (∀ q ∈ finalizeMuls stage chunk, q.1 ≠ r) ∧
      (∀ half, ∀ q ∈ finalizeUnpacks stage chunk half, q.2.1 ≠ r ∧ q.2.2 ≠ r) ∧
      (chunk.val < 4 → r ≠ outputStoreAddrReg stage (finalizeVector chunk 1)))
    (hRead : ∀ vals, X.get (g, pos) = some ⟨finalizeLoadPc stage chunk,
      .tc (.ld (outputAddress l g stage (8 * chunk.val)) vals .s32x32b)⟩ →
      vals = List.ofFn (fun i : Fin 8 => fl (old i.val)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u,
      X.get (g, pos) = some ⟨finalizeLoadPc stage chunk,
        .tc (.ld (outputAddress l g stage (8 * chunk.val))
          (List.ofFn fun i : Fin 8 => fl (old i.val)) .s32x32b)⟩ ∧
      X.get (g, pos + 1) = some ⟨finalizeLoadPc stage chunk + 5, .tc .waitLd⟩ ∧
      (∀ half : Fin 2, ∀ j : Fin 4, X.get (g, pos + 2 + 4 * half.val + j.val) = some
        ⟨outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk half),
          .wr {
            loc := (outputChunkLoc l g stage (finalizeSubset chunk) (rowOf l g)
              (finalizeVector chunk half).val).at (4 * j.val)
            size := 4, elem := j.val } (fl (old (4 * half.val + j.val) * reciprocal)).toBytes⟩) ∧
      At u (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 1) + 1)
        ((outputStoreAddrReg stage (finalizeVector chunk 1),
          b32 (finalizeVectorAddress l g stage chunk 1)) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 10)) none := by
  let facts := normalizeStoreFacts l g stage chunk
  let pairs := finalizeProductFacts stage chunk old reciprocal
  have hLoadFrame (r : Nat) (hm : r ∈ (facts ++ F).map Prod.fst) :
      r ∉ finalizeDataRegs stage chunk ∧
      (∀ q ∈ finalizePacks stage chunk, q.1 ≠ r) ∧
      (∀ q ∈ finalizeMuls stage chunk, q.1 ≠ r) := by
    rw [List.map_append, List.mem_append] at hm
    exact hm.elim (normalizeFacts_preserved l g stage chunk r) (fun h =>
      ⟨(hFrame r h).1, (hFrame r h).2.1, (hFrame r h).2.2.1⟩)
  obtain ⟨s, hLoad, hWait, hS, hRun⟩ := observeFinalizeProducts hp stage chunk old reciprocal
    ht hAddr hRecip hLoadFrame hRead hr
  have hSPairs := (holds_append _ _ _).1 hS.2.2.2.2
  have hS' : At s (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 0) - 2)
      (pairs ++ ((pairs ++ facts) ++ F)) := by
    rw [← firstVectorPc]
    have hP : Holds s.regs (pairs ++ facts) :=
      (holds_append _ _ _).2 ⟨hSPairs.1, ((holds_append _ _ _).1 hSPairs.2).1⟩
    exact hS.mono ((holds_append _ _ _).2
      ⟨hSPairs.1, (holds_append _ _ _).2 ⟨hP, ((holds_append _ _ _).1 hSPairs.2).2⟩⟩)
  have hA0 : s.regs (outputStoreAddrReg stage (finalizeVector chunk 0)) =
      some (b32 (finalizeVectorAddress l g stage chunk 0)) := ((holds_append _ _ _).1 hSPairs.2).1.1
  have hFresh := normalizeFirstFacts_preserved l g stage chunk old reciprocal
  obtain ⟨v, hFirst, hV, hRunV⟩ := observeNormalizedVector hp stage chunk 0 old reciprocal
    hS' hA0 (by
      intro r hm
      rw [List.map_append, List.mem_append] at hm
      exact hm.elim (hFresh.1 r) (fun h => (hFrame r h).2.2.2.1 0)) hRun
  have hVFacts : Holds v.regs facts :=
    ((holds_append _ _ _).1 ((holds_append _ _ _).1 hV.2.2.2.2).1).2
  have hOther : if chunk.val < 4 then v.regs 6500 = some (b32 (finalizeVectorDelta l g))
      else v.regs (outputStoreAddrReg stage (finalizeVector chunk 1)) =
        some (b32 (finalizeVectorAddress l g stage chunk 1)) := by
    have h := hVFacts
    unfold facts normalizeStoreFacts at h
    by_cases hc : chunk.val < 4
    · rw [ite_eq_left hc] at h ⊢
      exact h.2.1
    · rw [ite_eq_right hc] at h ⊢
      exact h.2.1
  obtain ⟨w, hA1, hW, hRunW⟩ := advanceFinalizeVector hp stage chunk hV hVFacts.1 hOther
    (by
      intro hc hm
      rw [List.map_append, List.mem_append] at hm
      exact hm.elim (hFresh.2 hc) (fun h => (hFrame _ h).2.2.2.2 hc rfl)) hRunV
  let addr := (outputStoreAddrReg stage (finalizeVector chunk 1),
    b32 (finalizeVectorAddress l g stage chunk 1))
  have hSaved := (holds_append _ _ _).1 hW.2.2.2.2
  have hW' : At w (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 1) - 2)
      (pairs ++ addr :: F) := hW.mono
        ((holds_append _ _ _).2 ⟨((holds_append _ _ _).1 hSaved.1).1, hA1, hSaved.2⟩)
  have hAddrKeep : ∀ q ∈ finalizeUnpacks stage chunk 1,
      q.2.1 ≠ addr.1 ∧ q.2.2 ≠ addr.1 := by
    dsimp only [addr]
    fin_cases stage <;> fin_cases chunk <;> decide
  obtain ⟨u, hSecond, hU, hRunU⟩ := observeNormalizedVector hp stage chunk 1 old reciprocal
    hW' hA1 (by
      intro r hm
      rw [List.map_cons, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact hAddrKeep
      · exact (hFrame r hm).2.2.2.1 1) hRunW
  refine ⟨u, hLoad, hWait, ?_, hU, ?_⟩
  · intro half j
    fin_cases half
    · exact hFirst j
    · exact hSecond j
  · simpa only [Nat.add_assoc] using hRunU

end
end PTX.Kernels.TmlFa4Fwd.Correction
