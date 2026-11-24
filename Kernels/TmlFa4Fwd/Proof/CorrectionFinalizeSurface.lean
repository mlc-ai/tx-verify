-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeBridge
public import Kernels.TmlFa4Fwd.Proof.CorrectionOutputSignal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

def finalizeVectorFact (l : Launch) (g : Nat) (stage : Fin 2) (v : Fin 8) : Nat × Value :=
  (outputStoreAddrReg stage v, b32 ((outputChunkLoc l g stage 0 (rowOf l g) v.val).addr))

/-- The register table grows through the first subbox and is reused by the later subboxes. -/
def finalizeVectorFrame (l : Launch) (g : Nat) (stage : Fin 2) (covered : Nat) :
    List (Nat × Value) :=
  (List.finRange 8).filterMap fun v => if v.val < covered then
    some (finalizeVectorFact l g stage v) else none

private theorem finalizeVectorFrame_mem {l : Launch} {g covered : Nat} {stage : Fin 2}
    {rv : Nat × Value} :
    rv ∈ finalizeVectorFrame l g stage covered ↔
      ∃ v : Fin 8, v.val < covered ∧ finalizeVectorFact l g stage v = rv := by
  simp only [finalizeVectorFrame, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨v, hv⟩
    by_cases h : v.val < covered
    · exact ⟨v, h, Option.some.inj (by simpa only [h, ↓reduceIte] using hv)⟩
    · simp [h] at hv
  · rintro ⟨v, h, rfl⟩
    exact ⟨v, by simp [h]⟩

private theorem holds_of_forall {regs : Nat → Option Value} :
    ∀ {F : List (Nat × Value)}, (∀ rv ∈ F, regs rv.1 = some rv.2) → Holds regs F
  | [], _ => trivial
  | r :: _rest, h => ⟨h r (List.mem_cons_self), holds_of_forall
    (fun r hr => h r (List.mem_cons_of_mem _ hr))⟩

private theorem vectorFrameExtend {l : Launch} {g covered : Nat} {stage : Fin 2}
    {v : Fin 8} {regs : Nat → Option Value}
    (hFrame : Holds regs (finalizeVectorFrame l g stage covered))
    (hCovered : covered = v.val)
    (hNew : regs (finalizeVectorFact l g stage v).1 = some (finalizeVectorFact l g stage v).2) :
    Holds regs (finalizeVectorFrame l g stage (covered + 1)) := by
  apply holds_of_forall
  intro rv hm
  obtain ⟨a, ha, rfl⟩ := finalizeVectorFrame_mem.mp hm
  by_cases h : a.val < covered
  · exact holds_mem hFrame (finalizeVectorFrame_mem.mpr ⟨a, h, rfl⟩)
  · have hEq : a = v := Fin.ext (by omega)
    rw [hEq]
    exact hNew

def finalizeSurfacePc (stage : Fin 2) (done : Nat) : Nat :=
  if h : done < 16 then
    if done = 0 then finalizeLoadPc stage 0 else finalizeBridgePc stage ⟨done, h⟩
  else outputFencePc stage

def finalizeSurfaceFrame (l : Launch) (g : Nat) (stage : Fin 2) (done : Nat)
    (F : List (Nat × Value)) : List (Nat × Value) :=
  finalizeVectorFrame l g stage (max 1 (2 * done)) ++ F

structure FinalizeSurfaceRegisters (l : Launch) (g : Nat) (stage : Fin 2) (reciprocal : ℝ)
    (F : List (Nat × Value)) : Prop where
  tmemZero : (1629, b32 (outputAddress l g 0 0)) ∈ F
  tmemStage : (finalizeAddressReg stage 0, b32 (outputAddress l g stage 0)) ∈ F
  deltaOdd : (6500, b32 (finalizeVectorDelta l g)) ∈ F
  deltaEven : ∀ chunk : Fin 16, 0 < chunk.val → chunk.val < 4 →
    (finalizeEvenDeltaReg chunk, b32 (finalizeEvenDelta l g chunk)) ∈ F
  recip : (finalizeReciprocalPair stage, .pair (fl reciprocal) (fl reciprocal)) ∈ F
  tmemFresh : ∀ chunk : Fin 16, 0 < chunk.val → ∀ rv ∈ F,
    rv.1 ≠ finalizeAddressReg stage chunk
  evenFresh : ∀ chunk : Fin 16, 0 < chunk.val → chunk.val < 4 → ∀ rv ∈ F,
    rv.1 ≠ outputStoreAddrReg stage (finalizeVector chunk 0)
  chunkFresh : ∀ chunk : Fin 16, ∀ r ∈ F.map Prod.fst,
    r ∉ finalizeDataRegs stage chunk ∧
    (∀ q ∈ finalizePacks stage chunk, q.1 ≠ r) ∧
    (∀ q ∈ finalizeMuls stage chunk, q.1 ≠ r) ∧
    (∀ half, ∀ q ∈ finalizeUnpacks stage chunk half, q.2.1 ≠ r ∧ q.2.2 ≠ r) ∧
    (chunk.val < 4 → r ≠ outputStoreAddrReg stage (finalizeVector chunk 1))

private theorem finalizeTmem_vectorDistinct (stage : Fin 2) (c : Fin 16) (v : Fin 8)
    (hc : 0 < c.val) : outputStoreAddrReg stage v ≠ finalizeAddressReg stage c := by
  fin_cases stage <;> fin_cases c <;> try (simp at hc)
  all_goals fin_cases v <;> decide

private theorem finalizeVectorReg_injective (stage : Fin 2) :
    Function.Injective (outputStoreAddrReg stage) := by
  intro a b h
  fin_cases stage <;> fin_cases a <;> fin_cases b <;> first | rfl | contradiction

private theorem finalizeChunkKeepsVector (stage : Fin 2) (c : Fin 16) (v : Fin 8) :
    let r := outputStoreAddrReg stage v
    r ∉ finalizeDataRegs stage c ∧
    (∀ q ∈ finalizePacks stage c, q.1 ≠ r) ∧
    (∀ q ∈ finalizeMuls stage c, q.1 ≠ r) ∧
    (∀ half : Fin 2, ∀ q ∈ finalizeUnpacks stage c half, q.2.1 ≠ r ∧ q.2.2 ≠ r) := by
  fin_cases stage <;> fin_cases c <;> fin_cases v <;> decide

private theorem finalizeSurfaceAddr {p : Params} {l : Launch} {m : Mem0} {g : Nat}
    {t : TState} {F : List (Nat × Value)} (hp : Pre p l m) (stage : Fin 2) (chunk : Fin 16)
    (reciprocal : ℝ) (hF : FinalizeSurfaceRegisters l g stage reciprocal F)
    (ht : At t (finalizeSurfacePc stage chunk.val)
      (finalizeSurfaceFrame l g stage chunk.val F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (finalizeLoadPc stage chunk) (finalizeVectorFrame l g stage (2 * chunk.val + 1) ++ F) ∧
      u.regs (finalizeAddressReg stage chunk) =
        some (b32 (outputAddress l g stage (8 * chunk.val))) := by
  by_cases hz : chunk.val = 0
  · have hzero : chunk = 0 := Fin.ext hz
    subst chunk
    exact ⟨t, .refl, ht, holds_mem ((holds_append _ _ _).1 ht.2.2.2.2).2 hF.tmemStage⟩
  have hn : 0 < chunk.val := by omega
  have hAt : At t (finalizeBridgePc stage chunk)
      (finalizeVectorFrame l g stage (2 * chunk.val) ++ F) := by
    have hCover : max 1 (2 * chunk.val) = 2 * chunk.val := max_eq_right (by omega)
    simpa only [finalizeSurfacePc, dite_eq_left chunk.isLt, ite_eq_right hz,
      finalizeSurfaceFrame, hCover] using ht
  let addr := (finalizeAddressReg stage chunk, b32 (outputAddress l g stage (8 * chunk.val)))
  let G := finalizeVectorFrame l g stage (2 * chunk.val)
  obtain ⟨u, hu, hU⟩ := finalizeBridgeTmem stage chunk hn hAt
    (holds_mem ((holds_append _ _ _).1 hAt.2.2.2.2).2 hF.tmemZero) (by
      intro rv hm
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨v, _, rfl⟩ := finalizeVectorFrame_mem.mp hm
        exact finalizeTmem_vectorDistinct stage chunk v hn
      · exact hF.tmemFresh chunk hn rv hm)
  by_cases hc : chunk.val < 4
  · let even := finalizeVector chunk 0
    have hNew : even.val = 2 * chunk.val := by
      simp only [even, finalizeVector, Nat.mod_eq_of_lt hc]
      rfl
    have hPrev : (finalizeVector (finalizeEvenBase chunk) 0).val < 2 * chunk.val := by
      unfold finalizeEvenBase
      split
      · change 4 < 2 * chunk.val
        omega
      · change 0 < 2 * chunk.val
        omega
    have hFields := (holds_append _ _ _).1 hU.2.2.2.2.2
    obtain ⟨v, hv, hV⟩ := finalizeBridgeEven hp stage chunk hn hc hU
      (holds_mem hFields.1 (finalizeVectorFrame_mem.mpr ⟨_, hPrev, rfl⟩))
      (holds_mem hFields.2 (hF.deltaEven chunk hn hc)) (by
        intro rv hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact (finalizeTmem_vectorDistinct stage chunk even hn).symm
        rcases List.mem_append.mp hm with hm | hm
        · obtain ⟨a, ha, rfl⟩ := finalizeVectorFrame_mem.mp hm
          intro h
          have := congrArg Fin.val (finalizeVectorReg_injective stage h)
          omega
        · exact hF.evenFresh chunk hn hc rv hm)
    have hDone := (holds_append _ _ _).1 hV.2.2.2.2.2.2
    exact ⟨v, hu.trans hv, hV.mono ((holds_append _ _ _).2
      ⟨vectorFrameExtend hDone.1 hNew.symm hV.2.2.2.2.1, hDone.2⟩), hV.2.2.2.2.2.1⟩
  · have hPc : finalizeBridgePc stage chunk + 1 = finalizeLoadPc stage chunk := by
      unfold finalizeBridgePc
      rw [ite_eq_right hc]
      have : 0 < finalizeLoadPc stage chunk := by unfold finalizeLoadPc; omega
      omega
    have hWide : finalizeVectorFrame l g stage (2 * chunk.val) =
        finalizeVectorFrame l g stage (2 * chunk.val + 1) := by
      unfold finalizeVectorFrame
      apply List.filterMap_congr
      intro v _
      have ha : v.val < 2 * chunk.val := by have := v.isLt; omega
      simp only [ite_eq_left ha, ite_eq_left (show v.val < 2 * chunk.val + 1 by omega)]
    exact ⟨u, hu, (hPc ▸ hU).mono (hWide ▸ hU.2.2.2.2.2), hU.2.2.2.2.1⟩

private theorem vectorFrameWide (l : Launch) (g : Nat) (stage : Fin 2) {a b : Nat}
    (ha : 8 ≤ a) (hb : 8 ≤ b) :
    finalizeVectorFrame l g stage a = finalizeVectorFrame l g stage b := by
  unfold finalizeVectorFrame
  apply List.filterMap_congr
  intro v _
  have hv := v.isLt
  simp only [ite_eq_left (show v.val < a by omega), ite_eq_left (show v.val < b by omega)]

/-- The ten events for a normalized chunk are contiguous on the actual correction trace. -/
structure NormalizedChunkEffects (l : Launch) (X : Execution) (g pos : Nat)
    (stage : Fin 2) (chunk : Fin 16) (old : Nat → ℝ) (reciprocal : ℝ) : Prop where
  load : X.get (g, pos) = some ⟨finalizeLoadPc stage chunk,
    .tc (.ld (outputAddress l g stage (8 * chunk.val))
      (List.ofFn fun i : Fin 8 => fl (old i.val)) .s32x32b)⟩
  wait : X.get (g, pos + 1) = some ⟨finalizeLoadPc stage chunk + 5, .tc .waitLd⟩
  writes : ∀ half : Fin 2, ∀ j : Fin 4, X.get (g, pos + 2 + 4 * half.val + j.val) = some
    ⟨outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk half), .wr
      { loc := (outputChunkLoc l g stage (finalizeSubset chunk) (rowOf l g)
          (finalizeVector chunk half).val).at (4 * j.val), size := 4, elem := j.val }
      (fl (old (4 * half.val + j.val) * reciprocal)).toBytes⟩

/-- Compute the local address and normalization frame before a finalization load. -/
theorem prepareFinalizeSurface {p : Params} {l : Launch} {m : Mem0} {g : Nat}
    {t : TState} {F : List (Nat × Value)} (hp : Pre p l m)
    (stage : Fin 2) (chunk : Fin 16) (reciprocal : ℝ)
    (hFrame : FinalizeSurfaceRegisters l g stage reciprocal F)
    (ht : At t (finalizeSurfacePc stage chunk.val) (finalizeSurfaceFrame l g stage chunk.val F)) :
    let G := finalizeVectorFrame l g stage (2*chunk.val+1) ++ F
    ∃ s, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t s ∧
      At s (finalizeLoadPc stage chunk) (normalizeStoreFacts l g stage chunk ++ G) ∧
      s.regs (finalizeAddressReg stage chunk) =
        some (b32 (outputAddress l g stage (8*chunk.val))) ∧
      (∀ r ∈ G.map Prod.fst,
        r ∉ finalizeDataRegs stage chunk ∧
        (∀ q ∈ finalizePacks stage chunk, q.1 ≠ r) ∧
        (∀ q ∈ finalizeMuls stage chunk, q.1 ≠ r) ∧
        (∀ half, ∀ q ∈ finalizeUnpacks stage chunk half, q.2.1 ≠ r ∧ q.2.2 ≠ r) ∧
        (chunk.val < 4 → r ≠ outputStoreAddrReg stage (finalizeVector chunk 1))) := by
  obtain ⟨s, hLocal, hs, hAddr⟩ := finalizeSurfaceAddr hp stage chunk reciprocal hFrame ht
  let G := finalizeVectorFrame l g stage (2 * chunk.val + 1) ++ F
  have hG : Holds s.regs G := hs.2.2.2.2
  have hVec (v : Fin 8) (hv : v.val < 2 * chunk.val + 1) :
      s.regs (outputStoreAddrReg stage v) = some
          (b32 (outputChunkLoc l g stage 0 (rowOf l g) v.val).addr) :=
    holds_mem ((holds_append _ _ _).1 hG).1 (finalizeVectorFrame_mem.mpr ⟨v, hv, rfl⟩)
  have hN : Holds s.regs (normalizeStoreFacts l g stage chunk) := by
    have hFirst : (finalizeVector chunk 0).val < 2 * chunk.val + 1 := by
      unfold finalizeVector
      have := Nat.mod_le chunk.val 4
      dsimp only
      omega
    unfold normalizeStoreFacts
    by_cases hc : chunk.val < 4
    · rw [ite_eq_left hc]
      exact ⟨hVec _ hFirst, holds_mem ((holds_append _ _ _).1 hG).2 hFrame.deltaOdd, trivial⟩
    · rw [ite_eq_right hc]
      have hSecond : (finalizeVector chunk 1).val < 2 * chunk.val + 1 := by
        have := (finalizeVector chunk 1).isLt
        omega
      exact ⟨hVec _ hFirst, hVec _ hSecond, trivial⟩
  have hF (r : Nat) (hm : r ∈ G.map Prod.fst) :
      r ∉ finalizeDataRegs stage chunk ∧
      (∀ q ∈ finalizePacks stage chunk, q.1 ≠ r) ∧
      (∀ q ∈ finalizeMuls stage chunk, q.1 ≠ r) ∧
      (∀ half, ∀ q ∈ finalizeUnpacks stage chunk half, q.2.1 ≠ r ∧ q.2.2 ≠ r) ∧
      (chunk.val < 4 → r ≠ outputStoreAddrReg stage (finalizeVector chunk 1)) := by
    rw [List.mem_map] at hm
    obtain ⟨rv, hm, rfl⟩ := hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨v, hv, rfl⟩ := finalizeVectorFrame_mem.mp hm
      have hKeep := finalizeChunkKeepsVector stage chunk v
      refine ⟨hKeep.1, hKeep.2.1, hKeep.2.2.1, hKeep.2.2.2, ?_⟩
      intro hc he
      have hSame := congrArg Fin.val (finalizeVectorReg_injective stage he)
      have hOdd : (finalizeVector chunk 1).val = 2 * chunk.val + 1 := by
        simp only [finalizeVector, Nat.mod_eq_of_lt hc]
        rfl
      omega
    · exact hFrame.chunkFresh chunk _ (List.mem_map_of_mem hm)
  exact ⟨s,hLocal,hs.mono ((holds_append _ _ _).2 ⟨hN,hG⟩),hAddr,hF⟩

/-- Retain the second vector's address in the table and move to the successor surface state. -/
theorem advanceFinalizeSurface {l : Launch} {g : Nat} {u : TState} {F : List (Nat × Value)}
    (stage : Fin 2) (chunk : Fin 16)
    (hu : At u (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 1)+1)
      ((outputStoreAddrReg stage (finalizeVector chunk 1),
        b32 (finalizeVectorAddress l g stage chunk 1)) ::
        (finalizeVectorFrame l g stage (2*chunk.val+1) ++ F))) :
    At u (finalizeSurfacePc stage (chunk.val+1))
      (finalizeSurfaceFrame l g stage (chunk.val+1) F) := by
  have hAt : u.pc = finalizeSurfacePc stage (chunk.val + 1) := by
    rw [hu.1]
    by_cases hc : chunk.val + 1 < 16
    · let nextChunk : Fin 16 := ⟨chunk.val + 1, hc⟩
      have hn : 0 < nextChunk.val := by dsimp [nextChunk]; omega
      have hPrev : (⟨nextChunk.val - 1, by omega⟩ : Fin 16) = chunk := Fin.ext (by simp [nextChunk])
      have hPc := finalizeBridge_pc stage nextChunk hn
      rw [hPrev] at hPc
      simpa only [finalizeSurfacePc, dite_eq_left hc,
        ite_eq_right (show chunk.val + 1 ≠ 0 by omega)] using hPc
    · have hLast : chunk = 15 := Fin.ext (by have := chunk.isLt; change _ = 15; omega)
      rw [finalizeSurfacePc, dite_eq_right hc, hLast]
      fin_cases stage <;> decide
  have hFields := (holds_append _ _ _).1 hu.2.2.2.2.2
  have hCover : max 1 (2 * (chunk.val + 1)) = 2 * chunk.val + 2 := by omega
  have hKnown : Holds u.regs (finalizeVectorFrame l g stage (2 * chunk.val + 2)) := by
    by_cases hc : chunk.val < 4
    · apply vectorFrameExtend (v := finalizeVector chunk 1) hFields.1 _ hu.2.2.2.2.1
      simp only [finalizeVector, Nat.mod_eq_of_lt hc]
      rfl
    · rw [← vectorFrameWide l g stage
        (show 8 ≤ 2 * chunk.val + 1 by omega) (show 8 ≤ 2 * chunk.val + 2 by omega)]
      exact hFields.1
  exact ⟨hAt,hu.2.1,hu.2.2.1,hu.2.2.2.1,
    by simpa only [finalizeSurfaceFrame,hCover] using
      (holds_append _ _ _).2 ⟨hKnown,hFields.2⟩⟩

private theorem observeSurfaceStep {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g pos : Nat} {t : TState} {F : List (Nat × Value)} (hp : Pre p l m)
    (stage : Fin 2) (chunk : Fin 16) (old : Nat → ℝ) (reciprocal : ℝ)
    (hFrame : FinalizeSurfaceRegisters l g stage reciprocal F)
    (ht : At t (finalizeSurfacePc stage chunk.val) (finalizeSurfaceFrame l g stage chunk.val F))
    (hRead : ∀ vals, X.get (g, pos) = some ⟨finalizeLoadPc stage chunk,
      .tc (.ld (outputAddress l g stage (8 * chunk.val)) vals .s32x32b)⟩ →
      vals = List.ofFn (fun i : Fin 8 => fl (old i.val)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u, NormalizedChunkEffects l X g pos stage chunk old reciprocal ∧
      At u (finalizeSurfacePc stage (chunk.val + 1))
        (finalizeSurfaceFrame l g stage (chunk.val + 1) F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 10)) none := by
  obtain ⟨s,hLocal,hs,hAddr,hKeep⟩ := prepareFinalizeSurface hp stage chunk reciprocal hFrame ht
  have hG := ((holds_append _ _ _).1 hs.2.2.2.2).2
  obtain ⟨u, hLoad, hWait, hStore, hu, hU⟩ := observeNormalizedChunkWithFrame hp
    stage chunk old reciprocal hs hAddr
    (holds_mem ((holds_append _ _ _).1 hG).2 hFrame.recip) hKeep hRead (hr.after_local hLocal)
  exact ⟨u,⟨hLoad,hWait,hStore⟩,advanceFinalizeSurface stage chunk hu,hU⟩

/-- The actual trace normalizes every column of a stage before the proxy fence and ready arrival.
The TMEM input witness supplies the accumulated row at each of the sixteen actual reads. -/
theorem observeNormalizedSurface {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g pos : Nat} {t : TState} {F : List (Nat × Value)} (hp : Pre p l m)
    (stage : Fin 2) (old : Fin 16 → Nat → ℝ) (reciprocal : ℝ)
    (hFrame : FinalizeSurfaceRegisters l g stage reciprocal (outputSignalFacts l g stage ++ F))
    (ht : At t (finalizeLoadPc stage 0)
      (finalizeSurfaceFrame l g stage 0 (outputSignalFacts l g stage ++ F)))
    (hFresh : ∀ rv ∈ F, rv.1 ≠ outputCreditDst stage ∧ rv.1 ≠ outputCreditDst stage + 1)
    (hRead : ∀ (chunk : Fin 16) vals, X.get (g, pos + 10 * chunk.val) =
      some ⟨finalizeLoadPc stage chunk,
        .tc (.ld (outputAddress l g stage (8 * chunk.val)) vals .s32x32b)⟩ →
      vals = List.ofFn (fun i : Fin 8 => fl (old chunk i.val)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u, (∀ chunk : Fin 16, NormalizedChunkEffects l X g (pos + 10 * chunk.val)
        stage chunk (old chunk) reciprocal) ∧
      X.get (g, pos + 160) = some
        ⟨outputFencePc stage, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      X.get (g, pos + 161) = some
        ⟨outputFencePc stage + 1, .arrive (creditLoc l g stage) 0 1 true .cta⟩ ∧
      X.get (g, pos + 162) = some
        ⟨outputFencePc stage + 2, .arrive (readyLoc l g stage) 0 1 true .cta⟩ ∧
      At u (outputFencePc stage + 3) F ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 163)) none := by
  let H := outputSignalFacts l g stage ++ F
  have hSteps (n : Nat) (hn : n ≤ 16) : ∃ v,
      (∀ chunk : Fin 16, chunk.val < n →
        NormalizedChunkEffects l X g (pos + 10 * chunk.val) stage chunk (old chunk) reciprocal) ∧
      At v (finalizeSurfacePc stage n) (finalizeSurfaceFrame l g stage n H) ∧
      Run kernel Assumptions.all l g v ((X.tr g).drop (pos + 10 * n)) none := by
    induction n with
    | zero => exact ⟨t, (fun _ hc => (Nat.not_lt_zero _ hc).elim), ht, hr⟩
    | succ n ih =>
      obtain ⟨v, hDone, hv, hV⟩ := ih (by omega)
      let chunk : Fin 16 := ⟨n, by omega⟩
      obtain ⟨w, hNext, hw, hW⟩ := observeSurfaceStep hp stage chunk (old chunk) reciprocal
        hFrame hv (hRead chunk) hV
      refine ⟨w, ?_, hw, ?_⟩
      · intro u hu
        by_cases h : u.val < n
        · exact hDone u h
        · have hEq : u = chunk := Fin.ext (by dsimp [chunk]; omega)
          rw [hEq]
          exact hNext
      · simpa only [Nat.mul_succ, Nat.add_assoc] using hW
  obtain ⟨v, hChunks, hv, hV⟩ := hSteps 16 (by decide)
  have hSignal : At v (outputFencePc stage) H :=
    hv.mono ((holds_append _ _ _).1 hv.2.2.2.2).2
  obtain ⟨u, hu, hFence, hCredit, hReady, hU⟩ :=
    observeOutputSignal (pos := pos + 160) hp stage hSignal hFresh hV
  exact ⟨u, (fun chunk => hChunks chunk chunk.isLt), hFence, hCredit, hReady, hu, hU⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
