-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeCode

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

private theorem holds_of_mem {R : Nat → Option Value} {F : List (Nat × Value)}
    (h : ∀ rv ∈ F, R rv.1 = some rv.2) : Holds R F := by
  induction F with
  | nil => trivial
  | cons rv rest ih =>
    cases rv with
    | mk r v => exact ⟨h (r, v) (by simp), ih (fun x hx => h x (by simp [hx]))⟩

def finalizeProductFacts (stage : Fin 2) (chunk : Fin 16) (old : Nat → ℝ) (reciprocal : ℝ) :
    List (Nat × Value) :=
  (List.range 4).map fun i => (finalizePackBase stage chunk + 4 + i,
    .pair (fl (old (2 * i) * reciprocal)) (fl (old (2 * i + 1) * reciprocal)))

private theorem finalPackFields (stage : Fin 2) (chunk : Fin 16) :
    (∀ p ∈ finalizePacks stage chunk, ∀ q ∈ finalizePacks stage chunk,
      q.1 ≠ p.2.1 ∧ q.1 ≠ p.2.2) ∧
    ((finalizePacks stage chunk).map Prod.fst).Nodup ∧
    (∀ q ∈ finalizePacks stage chunk, q.1 ≠ finalizeReciprocalPair stage) := by
  fin_cases stage <;> fin_cases chunk <;> decide

private theorem finalMulFields (stage : Fin 2) (chunk : Fin 16) :
    (∀ q ∈ finalizeMuls stage chunk, q.1 ≠ finalizeReciprocalPair stage ∧
      ∀ q' ∈ finalizeMuls stage chunk, q.1 ≠ q'.2) ∧
    ((finalizeMuls stage chunk).map Prod.fst).Nodup := by
  fin_cases stage <;> fin_cases chunk <;> decide

private theorem finalPackMem (stage : Fin 2) (chunk : Fin 16) (i : Nat) (hi : i < 4) :
    (finalizePackBase stage chunk + (3 - i), finalizeDataBase stage chunk + 2 * i,
      finalizeDataBase stage chunk + (2 * i + 1)) ∈ finalizePacks stage chunk := by
  apply List.mem_map.mpr
  refine ⟨3 - i, List.mem_range.mpr (by omega), ?_⟩
  rw [show 6 - 2 * (3 - i) = 2 * i by omega,
    show 7 - 2 * (3 - i) = 2 * i + 1 by omega]

/-- The four local packs keep the reciprocal and the carried frame while forming
pairs from the words returned by the live Tensor Memory load. -/
theorem finalizeChunkPacksLocal {l : Launch} {g : Nat} {t : TState} {F : List (Nat × Value)}
    (stage : Fin 2) (chunk : Fin 16) (old : Nat → ℝ) (reciprocal : ℝ)
    (ht : At t (finalizeLoadPc stage chunk + 1) F)
    (hData : ∀ i < 8, t.regs (finalizeDataBase stage chunk + i) = some (fl (old i)))
    (hRecip : t.regs (finalizeReciprocalPair stage) =
      some (.pair (fl reciprocal) (fl reciprocal)))
    (hFresh : ∀ r ∈ F.map Prod.fst, ∀ q ∈ finalizePacks stage chunk, q.1 ≠ r) :
    ∃ packed, At packed (finalizeLoadPc stage chunk + 5) F ∧
      packed.regs (finalizeReciprocalPair stage) = some (.pair (fl reciprocal) (fl reciprocal)) ∧
      (∀ i < 4, packed.regs (finalizePackBase stage chunk + (3 - i)) =
        some (.pair (fl (old (2 * i))) (fl (old (2 * i + 1))))) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t packed := by
  let ps := finalizePacks stage chunk
  let vc := Value.pair (fl reciprocal) (fl reciprocal)
  let v : Nat → Value := fun r => (t.regs r).getD (b32 0)
  have hpc : 8012 ≤ t.pc := by rw [ht.1]; unfold finalizeLoadPc; omega
  have hPLen : ps.length = 4 := by simp [ps, finalizePacks]
  have hV (i : Nat) (hi : i < 8) : v (finalizeDataBase stage chunk + i) = fl (old i) := by
    simp [v, hData i hi]
  have hSources : ∀ q ∈ ps, t.regs q.2.1 = some (v q.2.1) ∧
      t.regs q.2.2 = some (v q.2.2) ∧ (v q.2.1).bytes = 4 ∧ (v q.2.2).bytes = 4 := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    have hlo : 6 - 2 * j < 8 := by omega
    have hhi : 7 - 2 * j < 8 := by omega
    simp only [hV _ hlo, hV _ hhi, hData _ hlo, hData _ hhi, true_and]
    exact ⟨rfl, rfl⟩
  have hPackOk : packsOk v ps = true := by
    apply List.all_eq_true.mpr
    intro q hq
    simp [(hSources q hq).2.2.1, (hSources q hq).2.2.2]
  let packed := packRun v t ps
  have hPSkel := packRun_skel v ps t
  have hPacked : run kernel Assumptions.all l g ps.length t = some packed := by
    rw [Assumptions.run_all_eq_numeric]
    exact (packs_run numericPack v ps t (ht.1.symm ▸ finalizePackCode stage chunk)
      ht.2.2.2.1 (fun q hq => ⟨(hSources q hq).1, (hSources q hq).2.1⟩)
      (finalPackFields stage chunk).1 (fun i _ => correctionSegFree (by omega))).1 hPackOk
  have hPAt : At packed (finalizeLoadPc stage chunk + 5) F := by
    refine ⟨by rw [hPSkel.1, hPLen, ht.1], hPSkel.2.1.trans ht.2.1,
      hPSkel.2.2.1.trans ht.2.2.1, hPSkel.2.2.2.trans ht.2.2.2.1, ?_⟩
    apply holds_of_mem
    intro pair hm
    rw [packRun_other v ps t (hFresh _ (List.mem_map_of_mem hm))]
    exact holds_mem ht.2.2.2.2 hm
  have hCoeff : packed.regs (finalizeReciprocalPair stage) = some vc := by
    rw [packRun_other v ps t (finalPackFields stage chunk).2.2]
    exact hRecip
  let w : Nat → Value := fun r => (packed.regs r).getD (b32 0)
  have hPair (i : Nat) (hi : i < 4) : packed.regs (finalizePackBase stage chunk + (3 - i)) =
      some (.pair (fl (old (2 * i))) (fl (old (2 * i + 1)))) := by
    rw [packRun_val v ps t (finalPackFields stage chunk).2.1 (finalPackMem stage chunk i hi)]
    rw [hV (2 * i) (by omega), hV (2 * i + 1) (by omega)]
    rfl
  exact ⟨packed,hPAt,hCoeff,hPair,run_rtg hPacked⟩

/-- Once the explicit wait returns, four local multiplications normalize the packed words. -/
theorem finalizeChunkMulsLocal {l : Launch} {g : Nat} {waited : TState}
    {F : List (Nat × Value)} (stage : Fin 2) (chunk : Fin 16) (old : Nat → ℝ)
    (reciprocal : ℝ) (hWAt : At waited (finalizeLoadPc stage chunk + 6) F)
    (hPair : ∀ i < 4, waited.regs (finalizePackBase stage chunk + (3 - i)) =
      some (.pair (fl (old (2 * i))) (fl (old (2 * i + 1)))))
    (hCoeff : waited.regs (finalizeReciprocalPair stage) =
      some (.pair (fl reciprocal) (fl reciprocal)))
    (hFresh : ∀ r ∈ F.map Prod.fst, ∀ q ∈ finalizeMuls stage chunk, q.1 ≠ r) :
    ∃ u, At u (finalizeLoadPc stage chunk + 10)
      (finalizeProductFacts stage chunk old reciprocal ++ F) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) waited u := by
  let ms := finalizeMuls stage chunk
  let vc := Value.pair (fl reciprocal) (fl reciprocal)
  let w : Nat → Value := fun r => (waited.regs r).getD (b32 0)
  have hMLen : ms.length = 4 := by simp [ms, finalizeMuls]
  have hPairW (i : Nat) (hi : i < 4) : w (finalizePackBase stage chunk + (3 - i)) =
      .pair (fl (old (2 * i))) (fl (old (2 * i + 1))) := by simp [w, hPair i hi]
  have hFloat (i : Nat) (hi : i < 4) :
      floatE (mul2I .rn false) [w (finalizePackBase stage chunk + (3 - i)), vc] =
        .ok (.pair (fl (old (2 * i) * reciprocal)) (fl (old (2 * i + 1) * reciprocal))) := by
    rw [hPairW i hi]
    exact floatE_mul2_fin rfl rfl rfl rfl
  have hMulOk : mulsEOk .rn false w vc ms = true := by
    apply List.all_eq_true.mpr
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    simp only [hFloat i (List.mem_range.mp hi), Except.toBool]
  let u := mulRunE .rn false w vc waited ms
  have hMSkel := mulRunE_skel .rn false w vc ms waited
  have hMultiplied : run kernel Assumptions.all l g ms.length waited = some u := by
    rw [Assumptions.run_all_eq_numeric]
    apply (mulsE_run w ms waited (hWAt.1.symm ▸ finalizeMulCode stage chunk)
      hWAt.2.2.2.1 hCoeff ?_ (finalMulFields stage chunk).1 ?_).1 hMulOk
    · intro q hq
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
      simp only [hPairW i (List.mem_range.mp hi)]
      exact hPair i (List.mem_range.mp hi)
    · intro i hi s hs
      apply mulModel
      rw [hs, hWAt.1]
      unfold finalizeLoadPc
      omega
  refine ⟨u, ⟨by rw [hMSkel.1, hMLen, hWAt.1],
    hMSkel.2.1.trans hWAt.2.1, hMSkel.2.2.1.trans hWAt.2.2.1,
    hMSkel.2.2.2.trans hWAt.2.2.2.1, ?_⟩, run_rtg hMultiplied⟩
  apply holds_of_mem
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    have hm : (finalizePackBase stage chunk + 4 + i, finalizePackBase stage chunk + (3 - i))
        ∈ ms := List.mem_map.mpr ⟨i, hi, rfl⟩
    rw [mulRunE_val .rn false w vc ms waited (finalMulFields stage chunk).2 hm]
    simp only [mulOutV, hFloat i (List.mem_range.mp hi), okVal]
  · rw [mulRunE_other .rn false w vc ms waited (hFresh _ (List.mem_map_of_mem h))]
    exact holds_mem hWAt.2.2.2.2 h


variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} {g pos : Nat} {t : TState}

/-- Between the x8 load and first vector store, the actual lane packs the data, waits for the
load, and multiplies each pair by the reciprocal of the row's guarded sum. -/
theorem finalizeChunkProducts {F : List (Nat × Value)} (hp : Pre p l m) (stage : Fin 2)
    (chunk : Fin 16) (old : Nat → ℝ) (reciprocal : ℝ) (ht : At t (finalizeLoadPc stage chunk + 1) F)
    (hData : ∀ i < 8, t.regs (finalizeDataBase stage chunk + i) = some (fl (old i)))
    (hRecip : t.regs (finalizeReciprocalPair stage) = some (.pair (fl reciprocal) (fl reciprocal)))
    (hFresh : ∀ r ∈ F.map Prod.fst,
      (∀ q ∈ finalizePacks stage chunk, q.1 ≠ r) ∧
      (∀ q ∈ finalizeMuls stage chunk, q.1 ≠ r))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u, X.get (g, pos) = some ⟨finalizeLoadPc stage chunk + 5, .tc .waitLd⟩ ∧
      At u (finalizeLoadPc stage chunk + 10)
        (finalizeProductFacts stage chunk old reciprocal ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) none := by
  obtain ⟨packed,hPAt,hCoeff,hPair,hLocal⟩ := finalizeChunkPacksLocal (l := l) (g := g)
    stage chunk old reciprocal ht hData hRecip (fun r hr => (hFresh r hr).1)
  obtain ⟨hWait,hWAt,hTail⟩ := observeFinalizeWait hp stage chunk hPAt (hr.after_local hLocal)
  obtain ⟨u,hU,hStep⟩ := finalizeChunkMulsLocal (l := l) (g := g)
    stage chunk old reciprocal hWAt hPair hCoeff (fun r hr => (hFresh r hr).2)
  exact ⟨u,hWait,hU,hTail.after_local hStep⟩

/-- The x8 tensor-memory load and its explicit wait are successive trace events. The lane
then holds each pair of normalized words, ready to unpack for the shared stores. -/
theorem observeFinalizeProducts {F : List (Nat × Value)} (hp : Pre p l m) (stage : Fin 2)
    (chunk : Fin 16) (old : Nat → ℝ) (reciprocal : ℝ) (ht : At t (finalizeLoadPc stage chunk) F)
    (hAddr : t.regs (finalizeAddressReg stage chunk) =
      some (b32 (outputAddress l g stage (8 * chunk.val))))
    (hRecip : t.regs (finalizeReciprocalPair stage) = some (.pair (fl reciprocal) (fl reciprocal)))
    (hFresh : ∀ r ∈ F.map Prod.fst, r ∉ finalizeDataRegs stage chunk ∧
      (∀ q ∈ finalizePacks stage chunk, q.1 ≠ r) ∧
      (∀ q ∈ finalizeMuls stage chunk, q.1 ≠ r))
    (hRead : ∀ vals, X.get (g, pos) = some ⟨finalizeLoadPc stage chunk,
      .tc (.ld (outputAddress l g stage (8 * chunk.val)) vals .s32x32b)⟩ →
      vals = List.ofFn (fun i : Fin 8 => fl (old i.val)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u,
      X.get (g, pos) = some ⟨finalizeLoadPc stage chunk,
        .tc (.ld (outputAddress l g stage (8 * chunk.val))
          (List.ofFn fun i : Fin 8 => fl (old i.val)) .s32x32b)⟩ ∧
      X.get (g, pos + 1) = some ⟨finalizeLoadPc stage chunk + 5, .tc .waitLd⟩ ∧
      At u (finalizeLoadPc stage chunk + 10)
        (finalizeProductFacts stage chunk old reciprocal ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 2)) none := by
  obtain ⟨ds, vals, _, _, hDecode, he, hTail⟩ :=
    observeFinalizeLoad hp stage chunk (ht.mono ⟨hAddr, trivial⟩) hr
  have hInst := Option.some.inj (hDecode.symm.trans (finalizeRegisterCode stage chunk))
  have hd : ds = finalizeDataRegs stage chunk := (Op.tcLd.inj (Instr.mk.inj hInst).2).1
  have hv := hRead vals he
  rw [hd, hv] at hTail
  rw [hv] at he
  let values := List.ofFn fun i : Fin 8 => fl (old i.val)
  let s := setRegs (next t) (finalizeDataRegs stage chunk) values
  have hSkel := setRegs_skel (next t) (finalizeDataRegs stage chunk) values
  have hState : At s (finalizeLoadPc stage chunk + 1) F := by
    refine ⟨hSkel.1.trans (congrArg (· + 1) ht.1), hSkel.2.1.trans ht.2.1,
      hSkel.2.2.1.trans ht.2.2.1, hSkel.2.2.2.trans ht.2.2.2.1, ?_⟩
    apply holds_of_mem
    intro q hq
    rw [setRegs_other _ _ _ _ (hFresh _ (List.mem_map_of_mem hq)).1]
    exact holds_mem ht.2.2.2.2 hq
  have hDistinct : (finalizeDataRegs stage chunk).Nodup ∧
      finalizeReciprocalPair stage ∉ finalizeDataRegs stage chunk := by
    fin_cases stage <;> fin_cases chunk <;> decide
  have hData (i : Nat) (hi : i < 8) :
      s.regs (finalizeDataBase stage chunk + i) = some (fl (old i)) := by
    apply setRegs_get _ _ _ i _ _ hDistinct.1
    · simp only [finalizeDataRegs, List.getElem?_ofFn, dite_eq_left hi]
    · simp only [values, List.getElem?_ofFn, dite_eq_left hi]
  have hCoefficient : s.regs (finalizeReciprocalPair stage) =
      some (.pair (fl reciprocal) (fl reciprocal)) := by
    rw [setRegs_other _ _ _ _ hDistinct.2]
    exact hRecip
  obtain ⟨u, hWait, hu, hRun⟩ := finalizeChunkProducts hp stage chunk old reciprocal
    hState hData hCoefficient (fun r hm => (hFresh r hm).2) hTail
  exact ⟨u, he, hWait, hu, by simpa only [Nat.add_assoc] using hRun⟩

private theorem finalUnpackFields (stage : Fin 2) (chunk : Fin 16) (half : Fin 2) :
    (∀ q ∈ finalizeUnpacks stage chunk half, ∀ q' ∈ finalizeUnpacks stage chunk half,
      q'.2.1 ≠ q.1 ∧ q'.2.2 ≠ q.1) ∧
    ((finalizeUnpacks stage chunk half).flatMap fun q => [q.2.1, q.2.2]).Nodup ∧
    (∀ q ∈ finalizeUnpacks stage chunk half,
      q.2.1 ≠ outputStoreAddrReg stage (finalizeVector chunk half) ∧
      q.2.2 ≠ outputStoreAddrReg stage (finalizeVector chunk half)) := by
  fin_cases stage <;> fin_cases chunk <;> fin_cases half <;> decide

/-- The local unpack instructions produce the four normalized words for one vector store. -/
theorem finalizeUnpackLocal {l : Launch}
    {g : Nat} {t : TState} {F : List (Nat × Value)}
    (stage : Fin 2) (chunk : Fin 16) (half : Fin 2) (old : Nat → ℝ) (reciprocal : ℝ)
    (ht : At t (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk half) - 2)
      (finalizeProductFacts stage chunk old reciprocal ++ F))
    (hAddress : t.regs (outputStoreAddrReg stage (finalizeVector chunk half)) =
      some (b32 (outputChunkLoc l g stage 0 (rowOf l g) (finalizeVector chunk half).val).addr))
    (hFresh : ∀ r ∈ F.map Prod.fst, ∀ q ∈ finalizeUnpacks stage chunk half,
      q.2.1 ≠ r ∧ q.2.2 ≠ r)
    : ∃ s, At s (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk half)) F ∧
      s.regs (outputStoreAddrReg stage (finalizeVector chunk half)) =
        some (b32 (outputChunkLoc l g stage 0 (rowOf l g) (finalizeVector chunk half).val).addr) ∧
      (∀ j : Fin 4, s.regs (outputStoreValueReg stage (finalizeSubset chunk)
        (finalizeVector chunk half) j) = some (fl (old (4*half.val+j.val)*reciprocal))) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t s := by
  let pc := outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk half)
  let words := outputStoreValueReg stage (finalizeSubset chunk) (finalizeVector chunk half)
  let mul := finalizePackBase stage chunk + 4
  let left := 2 * half.val
  let value (i : Nat) := fl (old (4 * half.val + i) * reciprocal)
  let us := finalizeUnpacks stage chunk half
  let v (r : Nat) := (t.regs r).getD (b32 0)
  have hProducts (k : Nat) (hk : k < 4) : t.regs (mul + k) =
      some (.pair (fl (old (2 * k) * reciprocal)) (fl (old (2 * k + 1) * reciprocal))) := by
    apply holds_mem ht.2.2.2.2
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  have hHalf := half.isLt
  have hL : t.regs (mul + left) = some (.pair (value 0) (value 1)) := by
    simpa only [value, Nat.add_zero, show 2 * left = 4 * half.val by dsimp [left]; omega]
      using hProducts left (by dsimp [left]; omega)
  have hR : t.regs (mul + left + 1) = some (.pair (value 2) (value 3)) := by
    rw [Nat.add_assoc]
    have he : 2 * (left + 1) = 4 * half.val + 2 := by dsimp [left]; omega
    have he' : 2 * (left + 1) + 1 = 4 * half.val + 3 := by omega
    simpa only [value, he', he] using hProducts (left + 1) (by dsimp [left]; omega)
  have hvL : v (mul + left) = .pair (value 0) (value 1) := by simp [v, hL]
  have hvR : v (mul + left + 1) = .pair (value 2) (value 3) := by simp [v, hR]
  have hForm : us = [(mul + left + 1, words 2, words 3), (mul + left, words 0, words 1)] := rfl
  have hSrc (q : Nat × Nat × Nat) (hq : q ∈ us) :
      t.regs q.1 = some (v q.1) ∧ ∃ x y, v q.1 = .pair x y ∧ x.bytes = 4 ∧ y.bytes = 4 := by
    rw [hForm, List.mem_cons, List.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact ⟨hR.trans (congrArg some hvR.symm), _, _, hvR, rfl, rfl⟩
    · exact ⟨hL.trans (congrArg some hvL.symm), _, _, hvL, rfl, rfl⟩
  obtain ⟨hDisjoint, hDistinct, hAddrFresh⟩ := finalUnpackFields stage chunk half
  let s := unpackRun v t us
  have hRun : run kernel Assumptions.all l g us.length t = some s := by
    rw [Assumptions.run_all_eq_numeric]
    apply unpacks_run numericMoves v us t
      (ht.1.symm ▸ finalizeUnpackCode stage chunk half) ht.2.2.2.1
      (fun q hq => (hSrc q hq).1) (fun q hq => (hSrc q hq).2) hDisjoint
    intro i hi
    apply correctionSegFree
    rw [ht.1]
    have hpc : 8492 ≤ pc := by unfold pc outputStorePc; omega
    change 8012 ≤ pc - 2 + i
    omega
  have hWords : ∀ j : Fin 4, s.regs (words j) = some (value j.val) := by
    have hwL := unpackRun_val v us t hDistinct (mul + left, words 0, words 1)
      (by rw [hForm]; simp)
    have hwR := unpackRun_val v us t hDistinct (mul + left + 1, words 2, words 3)
      (by rw [hForm]; simp)
    simp only [hvL, splitValue] at hwL
    simp only [hvR, splitValue] at hwR
    intro j
    fin_cases j
    · exact hwL.1
    · exact hwL.2
    · exact hwR.1
    · exact hwR.2
  have hAddr : s.regs (outputStoreAddrReg stage (finalizeVector chunk half)) =
      some (b32 (outputChunkLoc l g stage 0 (rowOf l g) (finalizeVector chunk half).val).addr) :=
    (unpackRun_other v us t hAddrFresh).trans hAddress
  have hSkel := unpackRun_skel v us t
  have hAt : At s pc F := by
    refine ⟨?_, hSkel.2.1.trans ht.2.1, hSkel.2.2.1.trans ht.2.2.1,
      hSkel.2.2.2.trans ht.2.2.2.1, ?_⟩
    · have hpc : 2 ≤ pc := by unfold pc outputStorePc; omega
      rw [hSkel.1, ht.1, hForm]
      change pc - 2 + 2 = pc
      omega
    · apply holds_of_mem
      intro q hq
      rw [unpackRun_other v us t (hFresh _ (List.mem_map_of_mem hq))]
      exact holds_mem ht.2.2.2.2 (List.mem_append_right _ hq)
  exact ⟨s,hAt,hAddr,hWords,run_rtg hRun⟩

/-- Each half unpacks its two normalized pairs and writes the four words in ascending column
order at the actual shared addresses used by writeback. -/
theorem observeNormalizedVector {F : List (Nat × Value)} (hp : Pre p l m) (stage : Fin 2)
    (chunk : Fin 16) (half : Fin 2) (old : Nat → ℝ) (reciprocal : ℝ)
    (ht : At t (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk half) - 2)
      (finalizeProductFacts stage chunk old reciprocal ++ F))
    (hAddress : t.regs (outputStoreAddrReg stage (finalizeVector chunk half)) =
      some (b32 (outputChunkLoc l g stage 0 (rowOf l g) (finalizeVector chunk half).val).addr))
    (hFresh : ∀ r ∈ F.map Prod.fst, ∀ q ∈ finalizeUnpacks stage chunk half, q.2.1 ≠ r ∧ q.2.2 ≠ r)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u, (∀ j : Fin 4, X.get (g, pos + j.val) = some
      ⟨outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk half),
        .wr {
          loc := (outputChunkLoc l g stage (finalizeSubset chunk) (rowOf l g)
            (finalizeVector chunk half).val).at (4 * j.val)
          size := 4, elem := j.val } (fl (old (4 * half.val + j.val) * reciprocal)).toBytes⟩) ∧
      At u (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk half) + 1) F ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 4)) none := by
  obtain ⟨_,hAt,hAddr,hWords,hLocal⟩ := finalizeUnpackLocal (l := l) (g := g)
    stage chunk half old reciprocal ht hAddress hFresh
  obtain ⟨he,hNext,hTail⟩ := observeOutputStoreChunk hp stage (finalizeSubset chunk)
    (finalizeVector chunk half) (fun j => fl (old (4 * half.val + j.val) * reciprocal))
    hAt hAddr hWords (fun _ => rfl) (hr.after_local hLocal)
  exact ⟨_,he,hNext,hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
