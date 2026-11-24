-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionAccumulatorLoadProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeNumerics
import all Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeNumerics
import Kernels.TmlFa4Fwd.Proof.Safety.TmemFinalLoadProvenance
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityWait

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.TcMma

/-- Products actually computed from a recorded load and its explicit wait.
The data are retained until the subsequent ordinary writes. -/
structure ChunkProductsReached (l : Launch) (X : Execution) (g start : Nat)
    (stage : Fin 2) (chunk : Fin 16) (reciprocal : ℝ) (F : List (Nat × Value))
    (ending : Option TState) where
  values : Nat → ℝ
  before : TState
  ready : TState
  checkpoint : At ready (finalizeLoadPc stage chunk+10)
    (finalizeProductFacts stage chunk values reciprocal ++ F)
  wait : X.get (g,start+1) = some ⟨finalizeLoadPc stage chunk+5,.tc .waitLd⟩
  returned : Run kernel Assumptions.all l g {} ((X.tr g).take (start+2)) (some before)
  remaining : Run kernel Assumptions.all l g before ((X.tr g).drop (start+2)) ending
  localSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before ready

/-- Given a released accumulator load, every chunk computes its true normalized products. -/
theorem chunkProductsOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    (hValues : ∀ i, CompletedValues l Assumptions.all X i) {g : Nat} (hg : g < l.threads)
    (stage : Fin 2) (chunk : Fin 16) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (finalizeLoadPc stage chunk) F)
    {ds : List Nat} {words : List Value} (hCount : words.length = 8)
    (hCode : kernel.code[finalizeLoadPc stage chunk]? =
      some ⟨none,.tcLd ds (finalizeAddressReg stage chunk) .s32x32b none⟩)
    (hLoad : X.get (g,c.pos) = some ⟨finalizeLoadPc stage chunk,
      .tc (.ld (outputAddress l g stage (8*chunk.val)) words .s32x32b)⟩)
    (hReturned : Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1))
      (some (setRegs (next c.ready) ds words)))
    (hRemaining : Run kernel Assumptions.all l g (setRegs (next c.ready) ds words)
      ((X.tr g).drop (c.pos+1)) c.ending)
    (hRelease : c.pos+1 = (X.tr g).length → Step.Released l X g)
    (reciprocal : ℝ)
    (hRecip : (finalizeReciprocalPair stage,.pair (fl reciprocal) (fl reciprocal)) ∈ F)
    (hFresh : ∀ a ∈ F.map Prod.fst,
      a ∉ finalizeDataRegs stage chunk ∧
      (∀ q ∈ finalizePacks stage chunk, q.1 ≠ a) ∧
      (∀ q ∈ finalizeMuls stage chunk, q.1 ≠ a)) :
    Nonempty (ChunkProductsReached l X g c.pos stage chunk reciprocal F c.ending) := by
  let s := setRegs (next c.ready) ds words
  have hd : ds = finalizeDataRegs stage chunk :=
    (Op.tcLd.inj (Instr.mk.inj
      (Option.some.inj (hCode.symm.trans (finalizeRegisterCode stage chunk)))).2).1
  have hAt : At s (finalizeLoadPc stage chunk+1) F := by
    have h := c.checkpoint
    have hSkel := setRegs_skel (next c.ready) ds words
    refine ⟨hSkel.1.trans (congrArg (· + 1) h.1),hSkel.2.1.trans h.2.1,
      hSkel.2.2.1.trans h.2.2.1,hSkel.2.2.2.trans h.2.2.2.1,?_⟩
    apply holds_of_mem
    intro pair hMem
    rw [setRegs_other _ _ _ _ (hd.symm ▸ (hFresh _ (List.mem_map_of_mem hMem)).1)]
    exact holds_mem h.2.2.2.2 hMem
  have hWord (i : Nat) (hi : i < 8) : ∃ real : ℝ, words[i]? = some (fl real) :=
    Safety.finalizationLoadFloats hp hMax.1 hCuQ hValues stage chunk hLoad i (hCount.symm ▸ hi)
  let v : Nat → ℝ := fun i => if h : i < 8 then Classical.choose (hWord i h) else 0
  have hData (i : Nat) (hi : i < 8) :
      s.regs (finalizeDataBase stage chunk+i) = some (fl (v i)) := by
    have hDistinct : (finalizeDataRegs stage chunk).Nodup := by
      fin_cases stage <;> fin_cases chunk <;> decide
    apply setRegs_get ds words (next c.ready) i _ _ (hd.symm ▸ hDistinct)
    · rw [hd]
      simp only [finalizeDataRegs,List.getElem?_ofFn,dite_eq_left hi]
    · simpa only [v,dite_eq_left hi] using Classical.choose_spec (hWord i hi)
  have hCoeff := holds_mem hAt.2.2.2.2 hRecip
  obtain ⟨packed,hPacked,hPackedRecip,hPair,hLocal⟩ :=
    finalizeChunkPacksLocal (l := l) (g := g) stage chunk v reciprocal hAt hData hCoeff
      (fun a ha => (hFresh a ha).2.1)
  obtain ⟨hEvent,hPast,hTail⟩ := Softmax.probabilityCollectiveOfMaximal hg (Nat.succ_pos _)
    (len_of_get hLoad) (finalizeWaitTemplate hp stage chunk hPacked) rfl nofun hReturned hLocal
    hRemaining (fun hLast => ⟨X,hMax,rfl,hRelease hLast⟩)
  obtain ⟨u,hU,hUlocal⟩ := finalizeChunkMulsLocal (l := l) (g := g)
    stage chunk v reciprocal (hPacked.next : At (next packed) (finalizeLoadPc stage chunk+6) F)
    hPair hPackedRecip (fun a ha => (hFresh a ha).2.2)
  rw [hPacked.1] at hEvent
  exact ⟨⟨v,next packed,u,hU,hEvent,hPast,hTail,hUlocal⟩⟩

end PTX.Kernels.TmlFa4Fwd.Correction
