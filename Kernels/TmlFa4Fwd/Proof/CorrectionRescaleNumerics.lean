-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleCode
import Lemmas.Flow.ContinuingEvent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

theorem correctionSegFree {pc : Nat} (hpc : 8012 ≤ pc) :
    SegFreePc Assumptions.numeric pc :=
  Assumptions.numeric_segSites.pc (by
    simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
    omega)

theorem numericMoves : CoreMoves Assumptions.numeric := by
  intro inst l g t a ha
  simp only [Assumptions.numeric, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem numericPack : NoPack Assumptions.numeric :=
  fun _ _ _ => numericMoves _

theorem mulModel {l : Launch} {g : Nat} {t : TState} (hpc : 8012 ≤ t.pc) :
    IdealAt Assumptions.numeric .mulF32x2 l g t ∧
      DeclineAt Assumptions.numeric .mulF32x2 l g t := by
  have hSeg := correctionSegFree hpc
  refine ⟨idealAt_head (by decide) hSeg.tail, ?_⟩
  intro op hForm hDecline
  rw [(hSeg.at rfl).exec, execLocalRule_of_none]
  intro a ha
  simp only [Assumptions.numeric, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · simp [Assumptions.idealArith, idealReal, hForm, Assumptions.arithScope, hDecline]
  · apply approxExact_localRule_none
    intro f hf
    rw [approxForm_none_of_float hForm] at hf
    cases hf
  · have hLog : Assumptions.lg2Operands op = none := by
      cases op <;> try rfl
      rename_i f
      cases h : f.op <;> simp [Assumptions.lg2Operands, h]
      simp [FloatForm.ofOp, h] at hForm
    simp [Assumptions.lg2, hLog]
  · cases op <;> try rfl
    rename_i c
    simp only [FloatForm.ofOp] at hForm
    split_ifs at hForm <;> cases hForm
  · rfl

private theorem packLength (stage : Fin 2) (chunk : Fin 8) :
    (rescalePacks stage chunk).length = 8 + if chunk.val = 0 then 1 else 0 := by
  by_cases h : chunk.val = 0 <;> simp [rescalePacks, h]

private theorem packFields (stage : Fin 2) (chunk : Fin 8) :
    (∀ p ∈ rescalePacks stage chunk, ∀ q ∈ rescalePacks stage chunk,
      q.1 ≠ p.2.1 ∧ q.1 ≠ p.2.2) ∧
    ((rescalePacks stage chunk).map Prod.fst).Nodup ∧
    (chunk.val ≠ 0 → ∀ q ∈ rescalePacks stage chunk, q.1 ≠ rescaleAlphaPair stage) ∧
    (∀ q ∈ rescalePacks stage chunk, q.1 ≠ rescaleAddressReg stage chunk) := by
  fin_cases stage <;> fin_cases chunk <;> decide

private theorem mulFields (stage : Fin 2) (chunk : Fin 8) :
    (∀ q ∈ rescaleMuls stage chunk, q.1 ≠ rescaleAlphaPair stage ∧
      ∀ q' ∈ rescaleMuls stage chunk, q.1 ≠ q'.2) ∧
    ((rescaleMuls stage chunk).map Prod.fst).Nodup ∧
    (∀ q ∈ rescaleMuls stage chunk, q.1 ≠ rescaleAddressReg stage chunk) := by
  fin_cases stage <;> fin_cases chunk <;> decide

private theorem unpackFields (stage : Fin 2) (chunk : Fin 8) :
    (∀ p ∈ rescaleUnpacks stage chunk, ∀ q ∈ rescaleUnpacks stage chunk,
      q.2.1 ≠ p.1 ∧ q.2.2 ≠ p.1) ∧
    ((rescaleUnpacks stage chunk).flatMap fun p => [p.2.1, p.2.2]).Nodup ∧
    (∀ p ∈ rescaleUnpacks stage chunk,
      p.2.1 ≠ rescaleAddressReg stage chunk ∧ p.2.2 ≠ rescaleAddressReg stage chunk) := by
  fin_cases stage <;> fin_cases chunk <;> decide

private theorem firstPackMem (stage : Fin 2) (chunk : Fin 8) (i : Nat) (hi : i < 8) :
    (rescalePackBase stage chunk + (7 - i), rescaleDataBase stage chunk + 2 * i,
      rescaleDataBase stage chunk + (2 * i + 1)) ∈ rescalePacks stage chunk := by
  unfold rescalePacks
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨7 - i, List.mem_range.mpr (by omega), ?_⟩
  rw [show 14 - 2 * (7 - i) = 2 * i by omega,
    show 15 - 2 * (7 - i) = 2 * i + 1 by omega]

private theorem mulMem (stage : Fin 2) (chunk : Fin 8) (i : Nat) (hi : i < 8) :
    (rescaleMulBase stage chunk + i, rescalePackBase stage chunk + (7 - i)) ∈
      rescaleMuls stage chunk :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

private theorem unpackMem (stage : Fin 2) (chunk : Fin 8) (i : Nat) (hi : i < 8) :
    (rescaleMulBase stage chunk + i,
        rescaleDataBase stage chunk + 16 + 2 * (7 - i),
        rescaleDataBase stage chunk + 17 + 2 * (7 - i)) ∈ rescaleUnpacks stage chunk := by
  apply List.mem_map.mpr
  refine ⟨7 - i, List.mem_range.mpr (by omega), ?_⟩
  rw [show 7 - (7 - i) = i by omega]

private theorem holds_rescale_frame {R : Nat → Option Value} {F : List (Nat × Value)}
    (h : ∀ rv ∈ F, R rv.1 = some rv.2) : Holds R F := by
  induction F with
  | nil => trivial
  | cons rv rest ih =>
    cases rv with
    | mk r v => exact ⟨h (r, v) (by simp), ih (fun x hx => h x (by simp [hx]))⟩

/-- Registers carried between rescale chunks lie outside the pack, multiply and unpack targets. -/
def rescaleLocalKeeps (stage : Fin 2) (chunk : Fin 8) (r : Nat) : Prop :=
  (∀ q ∈ rescalePacks stage chunk, q.1 ≠ r) ∧
  (∀ q ∈ rescaleMuls stage chunk, q.1 ≠ r) ∧
  (∀ q ∈ rescaleUnpacks stage chunk, q.2.1 ≠ r ∧ q.2.2 ≠ r)

/-- The local pack, multiply and unpack steps reach the rescale store with all sixteen products. -/
theorem rescaleChunkProductSteps {l : Launch}
    {g : Nat} {t : TState} {F : List (Nat × Value)}
    (stage : Fin 2) (chunk : Fin 8)
    (old : Nat → ℝ) (alphaWord : Value) (alpha : ℝ)
    (ht : At t (rescaleLoadPc stage chunk + 1) F)
    (hFrame : ∀ r ∈ F.map Prod.fst, rescaleLocalKeeps stage chunk r)
    (hData : ∀ i < 16, t.regs (rescaleDataBase stage chunk + i) = some (fl (old i)))
    (hAlphaBytes : alphaWord.bytes = 4)
    (hAlphaLo : valFloat .f32 (splitValue 64 (joinValue alphaWord alphaWord)).1 = .ok alpha)
    (hAlphaHi : valFloat .f32 (splitValue 64 (joinValue alphaWord alphaWord)).2 = .ok alpha)
    (hAlpha : if chunk.val = 0 then t.regs (statsReg stage .alpha) = some alphaWord
      else t.regs (rescaleAlphaPair stage) = some (joinValue alphaWord alphaWord))
    (hAddr : t.regs (rescaleAddressReg stage chunk) =
      some (b32 (outputAddress l g stage (16 * chunk.val))))
    : ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (rescaleStorePc stage chunk)
        ((rescaleAlphaPair stage,joinValue alphaWord alphaWord)::F) ∧
      u.regs (rescaleAddressReg stage chunk) = some (b32 (outputAddress l g stage (16*chunk.val))) ∧
      ∀ j, u.regs (rescaleValueReg stage chunk j) = some (fl (old j.val*alpha)) := by
  let ps := rescalePacks stage chunk
  let ms := rescaleMuls stage chunk
  let us := rescaleUnpacks stage chunk
  let vc := joinValue alphaWord alphaWord
  let v : Nat → Value := fun r => (t.regs r).getD (b32 0)
  have hpc : 8012 ≤ t.pc := by rw [ht.1]; unfold rescaleLoadPc; omega
  have hV (i : Nat) (hi : i < 16) : v (rescaleDataBase stage chunk + i) = fl (old i) := by
    simp [v, hData i hi]
  have hSources : ∀ q ∈ ps, t.regs q.2.1 = some (v q.2.1) ∧
      t.regs q.2.2 = some (v q.2.2) ∧ (v q.2.1).bytes = 4 ∧ (v q.2.2).bytes = 4 := by
    intro q hq
    unfold ps rescalePacks at hq
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
      have hj' := List.mem_range.mp hj
      have hlo : 14 - 2 * j < 16 := by omega
      have hhi : 15 - 2 * j < 16 := by omega
      simp only [hV _ hlo, hV _ hhi, hData _ hlo, hData _ hhi, true_and]
      exact ⟨rfl, rfl⟩
    · by_cases hc : chunk.val = 0
      · rw [ite_eq_left hc, List.mem_singleton] at h
        rw [ite_eq_left hc] at hAlpha
        subst q
        simp [v, hAlpha, hAlphaBytes]
      · simp [hc] at h
  have hPackOk : packsOk v ps = true := by
    apply List.all_eq_true.mpr
    intro q hq
    simp [(hSources q hq).2.2.1, (hSources q hq).2.2.2]
  let u := packRun v t ps
  have hPSkel := packRun_skel v ps t
  have hPacked : run kernel Assumptions.numeric l g ps.length t = some u :=
    (packs_run numericPack v ps t (ht.1.symm ▸ rescalePackCode stage chunk)
      ht.2.2.2.1 (fun q hq => ⟨(hSources q hq).1, (hSources q hq).2.1⟩)
      (packFields stage chunk).1 (fun i _ => correctionSegFree (by omega))).1 hPackOk
  have hCoeff : u.regs (rescaleAlphaPair stage) = some vc := by
    by_cases hc : chunk.val = 0
    · have hMem : (rescaleAlphaPair stage, statsReg stage .alpha, statsReg stage .alpha) ∈ ps :=
        List.mem_append_right _ (by simp [hc])
      rw [packRun_val v ps t (packFields stage chunk).2.1 hMem]
      rw [ite_eq_left hc] at hAlpha
      simp [v, vc, hAlpha]
    · rw [packRun_other v ps t ((packFields stage chunk).2.2.1 hc)]
      rw [ite_eq_right hc] at hAlpha
      exact hAlpha
  let w : Nat → Value := fun r => (u.regs r).getD (b32 0)
  have hPair (i : Nat) (hi : i < 8) : u.regs (rescalePackBase stage chunk + (7 - i)) =
      some (.pair (fl (old (2 * i))) (fl (old (2 * i + 1)))) := by
    rw [packRun_val v ps t (packFields stage chunk).2.1 (firstPackMem stage chunk i hi)]
    rw [hV (2 * i) (by omega), hV (2 * i + 1) (by omega)]
    rfl
  have hPairW (i : Nat) (hi : i < 8) : w (rescalePackBase stage chunk + (7 - i)) =
      .pair (fl (old (2 * i))) (fl (old (2 * i + 1))) := by simp [w, hPair i hi]
  have hFloat (i : Nat) (hi : i < 8) :
      floatE (mul2I .rn false) [w (rescalePackBase stage chunk + (7 - i)), vc] =
        .ok (.pair (fl (old (2 * i) * alpha)) (fl (old (2 * i + 1) * alpha))) := by
    rw [hPairW i hi]
    exact floatE_mul2_fin (by rfl) (by rfl) hAlphaLo hAlphaHi
  have hMulOk : mulsEOk .rn false w vc ms = true := by
    apply List.all_eq_true.mpr
    intro pair hm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    have hi' := List.mem_range.mp hi
    simp only [hFloat i hi', Except.toBool]
  let z := mulRunE .rn false w vc u ms
  have hMSkel := mulRunE_skel .rn false w vc ms u
  have hMultiplied : run kernel Assumptions.numeric l g ms.length u = some z := by
    apply (mulsE_run w ms u ?_ (hPSkel.2.2.2.trans ht.2.2.2.1) hCoeff ?_
      (mulFields stage chunk).1 ?_).1 hMulOk
    · rw [hPSkel.1, ht.1]
      exact rescaleMulCode stage chunk
    · intro pair hm
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
      simp only [hPairW i (List.mem_range.mp hi)]
      exact hPair i (List.mem_range.mp hi)
    · intro i hi s hs
      apply mulModel
      rw [hs, hPSkel.1]
      omega
  let product : Nat → Value := fun r => (z.regs r).getD (b32 0)
  have hProduct (i : Nat) (hi : i < 8) : z.regs (rescaleMulBase stage chunk + i) =
      some (.pair (fl (old (2 * i) * alpha)) (fl (old (2 * i + 1) * alpha))) := by
    rw [mulRunE_val .rn false w vc ms u (mulFields stage chunk).2.1 (mulMem stage chunk i hi)]
    simp only [mulOutV, hFloat i hi, okVal]
  have hProductW (i : Nat) (hi : i < 8) : product (rescaleMulBase stage chunk + i) =
      .pair (fl (old (2 * i) * alpha)) (fl (old (2 * i + 1) * alpha)) := by
    simp [product, hProduct i hi]
  let endState := unpackRun product z us
  have hUSkel := unpackRun_skel product us z
  have hMLen : ms.length = 8 := by simp [ms, rescaleMuls]
  have hULen : us.length = 8 := by simp [us, rescaleUnpacks]
  have hUnpacked : run kernel Assumptions.numeric l g us.length z = some endState := by
    apply unpacks_run numericMoves product us z
    · rw [hMSkel.1, hPSkel.1, ht.1, hMLen]
      exact rescaleUnpackCode stage chunk
    · exact hMSkel.2.2.2.trans (hPSkel.2.2.2.trans ht.2.2.2.1)
    · intro triple htr
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp htr
      have hb : 7 - i < 8 := by omega
      rw [hProductW (7 - i) hb]
      exact hProduct (7 - i) hb
    · intro triple htr
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp htr
      have hb : 7 - i < 8 := by omega
      exact ⟨_, _, hProductW (7 - i) hb, rfl, rfl⟩
    · exact (unpackFields stage chunk).1
    · intro i hi
      apply correctionSegFree
      rw [hMSkel.1, hPSkel.1]
      omega
  have hReg (j : Fin 16) :
      endState.regs (rescaleValueReg stage chunk j) = some (fl (old j.val * alpha)) := by
    let i := j.val / 2
    have hi : i < 8 := by have := j.isLt; dsimp [i]; omega
    have hw := unpackRun_val product us z (unpackFields stage chunk).2.1
      _ (unpackMem stage chunk i hi)
    rw [hProductW i hi] at hw
    simp only [splitValue] at hw
    have hj : j.val % 2 < 2 := Nat.mod_lt _ (by decide)
    by_cases h : j.val % 2 = 0
    · have hR : rescaleValueReg stage chunk j = rescaleDataBase stage chunk + 16 + 2 * (7 - i) := by
        unfold rescaleValueReg rescaleDataBase
        dsimp [i]
        omega
      rw [hR, hw.1, show 2 * i = j.val by dsimp [i]; omega]
    · have hR : rescaleValueReg stage chunk j = rescaleDataBase stage chunk + 17 + 2 * (7 - i) := by
        unfold rescaleValueReg rescaleDataBase
        dsimp [i]
        omega
      rw [hR, hw.2, show 2 * i + 1 = j.val by dsimp [i]; omega]
  have hAddress : endState.regs (rescaleAddressReg stage chunk) =
      some (b32 (outputAddress l g stage (16 * chunk.val))) := by
    rw [unpackRun_other product us z (unpackFields stage chunk).2.2,
      mulRunE_other .rn false w vc ms u (mulFields stage chunk).2.2,
      packRun_other v ps t (packFields stage chunk).2.2.2]
    exact hAddr
  have hVC : endState.regs (rescaleAlphaPair stage) = some vc := by
    have hUnpack : ∀ q ∈ us, q.2.1 ≠ rescaleAlphaPair stage ∧
        q.2.2 ≠ rescaleAlphaPair stage := by
      fin_cases stage <;> fin_cases chunk <;>
        change ∀ q ∈ rescaleUnpacks _ _, _ <;> decide
    rw [unpackRun_other product us z hUnpack,
      mulRunE_other .rn false w vc ms u (fun q hq => ((mulFields stage chunk).1 q hq).1)]
    exact hCoeff
  have hF : Holds endState.regs F := by
    apply holds_rescale_frame
    intro rv hm
    obtain ⟨hP, hM, hU⟩ := hFrame rv.1 (List.mem_map_of_mem hm)
    rw [unpackRun_other product us z hU, mulRunE_other .rn false w vc ms u hM,
      packRun_other v ps t hP]
    exact holds_mem ht.2.2.2.2 hm
  have hEnd : At endState (rescaleStorePc stage chunk)
      ((rescaleAlphaPair stage, vc) :: F) := by
    refine ⟨?_, hUSkel.2.1.trans (hMSkel.2.1.trans (hPSkel.2.1.trans ht.2.1)),
      hUSkel.2.2.1.trans (hMSkel.2.2.1.trans (hPSkel.2.2.1.trans ht.2.2.1)),
      hUSkel.2.2.2.trans (hMSkel.2.2.2.trans (hPSkel.2.2.2.trans ht.2.2.2.1)), hVC, hF⟩
    rw [hUSkel.1, hMSkel.1, hPSkel.1, ht.1, hULen, hMLen]
    change rescaleLoadPc stage chunk + 1 + (rescalePacks stage chunk).length + 8 + 8 = _
    rw [packLength]
    unfold rescaleLoadPc rescaleStorePc
    split_ifs <;> omega
  have hRun : run kernel Assumptions.all l g (ps.length + ms.length + us.length) t =
      some endState := by
    rw [Assumptions.run_all_eq_numeric]
    exact run_comp (run_comp hPacked hMultiplied) hUnpacked
  exact ⟨endState,run_rtg hRun,hEnd,hAddress,hReg⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem loadRegisterShape (stage : Fin 2) (chunk : Fin 8) :
    (rescaleDataRegs stage chunk).Nodup ∧
      rescaleAddressReg stage chunk ∉ rescaleDataRegs stage chunk ∧
      statsReg stage .alpha ∉ rescaleDataRegs stage chunk ∧
      rescaleAlphaPair stage ∉ rescaleDataRegs stage chunk := by
  fin_cases stage <;> fin_cases chunk <;> decide

/-- Restoring the sixteen returned words prepares the entire product computation
through the local instructions up to the rescale store. -/
theorem loadedRescaleProductSteps {l : Launch} {g : Nat} {t : TState}
    {F : List (Nat × Value)} (stage : Fin 2) (chunk : Fin 8)
    (old : Nat → ℝ) (alphaWord : Value) (alpha : ℝ)
    (ht : At t (rescaleLoadPc stage chunk) F)
    (hAddr : t.regs (rescaleAddressReg stage chunk) =
      some (b32 (outputAddress l g stage (16*chunk.val))))
    (hFrame : ∀ r ∈ F.map Prod.fst,
      r ∉ rescaleDataRegs stage chunk ∧ rescaleLocalKeeps stage chunk r)
    (hAlphaBytes : alphaWord.bytes = 4)
    (hAlphaLo : valFloat .f32 (splitValue 64 (joinValue alphaWord alphaWord)).1 = .ok alpha)
    (hAlphaHi : valFloat .f32 (splitValue 64 (joinValue alphaWord alphaWord)).2 = .ok alpha)
    (hAlpha : if chunk.val = 0 then t.regs (statsReg stage .alpha) = some alphaWord
      else t.regs (rescaleAlphaPair stage) = some (joinValue alphaWord alphaWord)) :
    let values := List.ofFn fun i : Fin 16 => fl (old i.val)
    let s := setRegs (next t) (rescaleDataRegs stage chunk) values
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (rescaleStorePc stage chunk)
        ((rescaleAlphaPair stage,joinValue alphaWord alphaWord)::F) ∧
      u.regs (rescaleAddressReg stage chunk) = some (b32 (outputAddress l g stage (16*chunk.val))) ∧
      ∀ j, u.regs (rescaleValueReg stage chunk j) = some (fl (old j.val*alpha)) := by
  let values := List.ofFn fun i : Fin 16 => fl (old i.val)
  let s := setRegs (next t) (rescaleDataRegs stage chunk) values
  have hSkel := setRegs_skel (next t) (rescaleDataRegs stage chunk) values
  have hState : At s (rescaleLoadPc stage chunk + 1) F := by
    refine ⟨hSkel.1.trans (congrArg (· + 1) ht.1), hSkel.2.1.trans ht.2.1,
      hSkel.2.2.1.trans ht.2.2.1, hSkel.2.2.2.trans ht.2.2.2.1, ?_⟩
    apply holds_rescale_frame
    intro rv hm
    rw [setRegs_other _ _ _ _ (hFrame _ (List.mem_map_of_mem hm)).1]
    exact holds_mem ht.2.2.2.2 hm
  obtain ⟨hDistinct, hAddress, hReg, hPair⟩ := loadRegisterShape stage chunk
  have hData (i : Nat) (hi : i < 16) :
      s.regs (rescaleDataBase stage chunk + i) = some (fl (old i)) := by
    apply setRegs_get _ _ _ i _ _ hDistinct
    · simp only [rescaleDataRegs, List.getElem?_ofFn, dite_eq_left hi]
    · simp only [values, List.getElem?_ofFn, dite_eq_left hi]
  have hStoreAddr : s.regs (rescaleAddressReg stage chunk) =
      some (b32 (outputAddress l g stage (16 * chunk.val))) := by
    rw [setRegs_other _ _ _ _ hAddress]
    exact hAddr
  have hCoefficient : if chunk.val = 0 then s.regs (statsReg stage .alpha) = some alphaWord
      else s.regs (rescaleAlphaPair stage) = some (joinValue alphaWord alphaWord) := by
    by_cases hc : chunk.val = 0
    · rw [ite_eq_left hc, setRegs_other _ _ _ _ hReg]
      rw [ite_eq_left hc] at hAlpha
      exact hAlpha
    · rw [ite_eq_right hc, setRegs_other _ _ _ _ hPair]
      rw [ite_eq_right hc] at hAlpha
      exact hAlpha
  exact rescaleChunkProductSteps stage chunk old alphaWord alpha hState
    (fun r hm => (hFrame r hm).2)
    hData hAlphaBytes hAlphaLo hAlphaHi hCoefficient hStoreAddr

/-- A prefix containing the whole chunk records its actual load, wait and FP32 product. -/
theorem observeRescaledChunkInPrefix {g pos : Nat} {t : TState} {ending : Option TState}
    {F : List (Nat × Value)} (hp : Pre p l m) (stage : Fin 2) (chunk : Fin 8) (old : Nat → ℝ)
    (alphaWord : Value) (alpha : ℝ) (ht : At t (rescaleLoadPc stage chunk) F)
    (hAddr : t.regs (rescaleAddressReg stage chunk) =
      some (b32 (outputAddress l g stage (16 * chunk.val))))
    (hFrame : ∀ r ∈ F.map Prod.fst,
      r ∉ rescaleDataRegs stage chunk ∧ rescaleLocalKeeps stage chunk r)
    (hRead : ∀ vals, X.get (g, pos) = some ⟨rescaleLoadPc stage chunk,
      .tc (.ld (outputAddress l g stage (16 * chunk.val)) vals .s32x32b)⟩ →
      vals = List.ofFn fun i : Fin 16 => fl (old i.val)) (hAlphaBytes : alphaWord.bytes = 4)
    (hAlphaLo : valFloat .f32 (splitValue 64 (joinValue alphaWord alphaWord)).1 = .ok alpha)
    (hAlphaHi : valFloat .f32 (splitValue 64 (joinValue alphaWord alphaWord)).2 = .ok alpha)
    (hAlpha : if chunk.val = 0 then t.regs (statsReg stage .alpha) = some alphaWord
      else t.regs (rescaleAlphaPair stage) = some (joinValue alphaWord alphaWord))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hPresent : ending = none ∨ pos + 2 < (X.tr g).length) :
    ∃ u, X.get (g, pos) = some ⟨rescaleLoadPc stage chunk,
        .tc (.ld (outputAddress l g stage (16 * chunk.val))
          (List.ofFn fun i : Fin 16 => fl (old i.val)) .s32x32b)⟩ ∧
      X.get (g, pos + 1) = some ⟨rescaleLoadPc stage chunk, .tc .waitLd⟩ ∧
      X.get (g, pos + 2) = some ⟨rescaleStorePc stage chunk,
        .tc (.st (outputAddress l g stage (16 * chunk.val))
          (List.ofFn fun i : Fin 16 => fl (old i.val * alpha)) .s32x32b)⟩ ∧
      At u (rescaleStorePc stage chunk + 1)
        ((rescaleAlphaPair stage, joinValue alphaWord alphaWord) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 3)) ending := by
  obtain ⟨ds, vals, _, _, hCode, hLoad, hWait, hTail⟩ :=
    observeRescaleLoadInPrefix hp stage chunk (ht.mono ⟨hAddr, trivial⟩) hr
      (hPresent.imp id (fun h => by omega))
  have hv := hRead vals hLoad
  rw [hv] at hLoad hTail
  let values := List.ofFn fun i : Fin 16 => fl (old i.val)
  have hInst := Option.some.inj (hCode.symm.trans (rescaleRegisterCode stage chunk))
  have hd : ds = rescaleDataRegs stage chunk := (Op.tcLd.inj (Instr.mk.inj hInst).2).1
  rw [hd] at hTail
  have hSeen : (X.tr g).drop (pos + 2) ≠ [] := by
    intro hNil
    rcases hPresent with rfl | hIndex
    · rw [hNil] at hTail
      cases hTail
    · have hLen := congrArg List.length hNil
      simp only [List.length_drop, List.length_nil] at hLen
      exact (Nat.not_lt_of_ge (Nat.sub_eq_zero_iff_le.mp hLen)) hIndex
  obtain ⟨u,hLocal,hAt,hAddress,hReg⟩ := loadedRescaleProductSteps stage chunk old alphaWord
    alpha ht hAddr hFrame hAlphaBytes hAlphaLo hAlphaHi hAlpha
  obtain ⟨hStore,hu,hRun⟩ := observeRescaleStoreInPrefix hp stage chunk
    (fun j => fl (old j.val*alpha)) hAt hAddress hReg (fun _ => rfl)
    (hTail.after_local_nonempty hLocal hSeen) hSeen
  exact ⟨_,hLoad,hWait,hStore,hu,hRun⟩

/-- The load, its checked wait, and the scaled write belong to one actual execution of the
chunk. The input premise supplies the Tensor Memory values that the load observed. -/
theorem observeRescaledChunk {g pos : Nat} {t : TState} {F : List (Nat × Value)} (hp : Pre p l m)
    (stage : Fin 2) (chunk : Fin 8) (old : Nat → ℝ) (alphaWord : Value) (alpha : ℝ)
    (ht : At t (rescaleLoadPc stage chunk) F)
    (hAddr : t.regs (rescaleAddressReg stage chunk) =
      some (b32 (outputAddress l g stage (16 * chunk.val))))
    (hFrame : ∀ r ∈ F.map Prod.fst,
      r ∉ rescaleDataRegs stage chunk ∧ rescaleLocalKeeps stage chunk r)
    (hRead : ∀ vals, X.get (g, pos) = some ⟨rescaleLoadPc stage chunk,
      .tc (.ld (outputAddress l g stage (16 * chunk.val)) vals .s32x32b)⟩ →
      vals = List.ofFn fun i : Fin 16 => fl (old i.val)) (hAlphaBytes : alphaWord.bytes = 4)
    (hAlphaLo : valFloat .f32 (splitValue 64 (joinValue alphaWord alphaWord)).1 = .ok alpha)
    (hAlphaHi : valFloat .f32 (splitValue 64 (joinValue alphaWord alphaWord)).2 = .ok alpha)
    (hAlpha : if chunk.val = 0 then t.regs (statsReg stage .alpha) = some alphaWord
      else t.regs (rescaleAlphaPair stage) = some (joinValue alphaWord alphaWord))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u, X.get (g, pos) = some ⟨rescaleLoadPc stage chunk,
        .tc (.ld (outputAddress l g stage (16 * chunk.val))
          (List.ofFn fun i : Fin 16 => fl (old i.val)) .s32x32b)⟩ ∧
      X.get (g, pos + 1) = some ⟨rescaleLoadPc stage chunk, .tc .waitLd⟩ ∧
      X.get (g, pos + 2) = some ⟨rescaleStorePc stage chunk,
        .tc (.st (outputAddress l g stage (16 * chunk.val))
          (List.ofFn fun i : Fin 16 => fl (old i.val * alpha)) .s32x32b)⟩ ∧
      At u (rescaleStorePc stage chunk + 1)
        ((rescaleAlphaPair stage, joinValue alphaWord alphaWord) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 3)) none :=
  observeRescaledChunkInPrefix hp stage chunk old alphaWord alpha ht hAddr hFrame hRead
    hAlphaBytes hAlphaLo hAlphaHi hAlpha hr (.inl rfl)

end
end PTX.Kernels.TmlFa4Fwd.Correction
