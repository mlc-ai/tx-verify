-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.CuQNumericWitness
import all Kernels.TmlFa4Fwd.Audit.SpecWitness
public import Kernels.TmlFa4Fwd.Audit.OutputStep
public import Kernels.TmlFa4Fwd.Proof.Lib.ScheduleCoords

namespace PTX.Kernels.TmlFa4Fwd
open TensorDescriptor
noncomputable section

private theorem adjacentReadToStoreOfDecodedWord
    (word : Value) (hWidth : word.bytes = 4) (hByte : word.byteAt 0 = (word,0))
    (hRead : ∀ t : TState, t.regs 2393 = some word →
      readBits adjacentLaunch adjacentWriter t 32 (.reg 2393) = .ok (BitVec.ofNat 64 138)) :
    ∃ out, Run kernel Assumptions.all adjacentLaunch adjacentWriter adjacentReadState
      [Epilogue.endpointEvent adjacentObserved 1 0,
        ⟨2954, .rd (Epilogue.endpointAccess adjacentObserved 2)
          (word.toBytes.map some)⟩,
        ⟨2958, .wait (Epilogue.readyLoc adjacentLaunch adjacentWriter 0) 0 true true .cta⟩,
        ⟨2963, .tensorStore adjacentParams.oMapAddress adjacentStore⟩] (some out) := by
  let t0 := adjacentReadState
  let t1 := next (setReg t0 2392 (PTX.Proof.b32 129))
  let t2 := next (setReg t1 2393 word)
  let t2a := next (setReg t2 2394 (PTX.Proof.b32 (2^30+129)))
  let t2b := next (setReg t2a 2395 (PTX.Proof.b32 (2^30-9)))
  let t3 := next (setReg t2b 7229 (PTX.Proof.b32 0))
  let t4 := next (setReg t3 9748 (.pred true))
  let t5 := next (setReg (next (setReg {t4 with pc := 2961} 7868
    (.ptr 64 true (.param (param 10)) 0))) 7869 (PTX.Proof.b64 0))
  let a0 := Epilogue.endpointAccess adjacentObserved 1
  let a1 := Epilogue.endpointAccess adjacentObserved 2
  let b0 := ((PTX.Proof.b32 129).toBytes.map some : List (Option Byte))
  let b1 := (word.toBytes.map some : List (Option Byte))
  let ready := Epilogue.readyLoc adjacentLaunch adjacentWriter 0
  have read0 : EStep kernel Assumptions.all adjacentLaunch adjacentWriter t0
      (Epilogue.endpointEvent adjacentObserved 1 0) (some t1) := by
    refine ⟨.read a0 (afterLoad t0 [2392]), ?_, b0, rfl, rfl, ?_⟩
    · set_option maxRecDepth 100000 in kernel_rfl
    · have hScalar := PTX.Proof.rebuild_scalar (v := PTX.Proof.b32 129) (by decide) rfl
      rw [PTX.Proof.afterLoad_ok rfl rfl hScalar]
      rfl
  have read1 : EStep kernel Assumptions.all adjacentLaunch adjacentWriter t1
      ⟨2954,.rd (Epilogue.endpointAccess adjacentObserved 2)
        (word.toBytes.map some)⟩ (some t2) := by
    refine ⟨.read a1 (afterLoad t1 [2393]), ?_, b1, ?_, rfl, ?_⟩
    · set_option maxRecDepth 100000 in kernel_rfl
    · simp [b1, a1, Value.toBytes, hWidth, Epilogue.endpointAccess]
    · have hScalar := PTX.Proof.rebuild_scalar (v := word) (by omega) hByte
      rw [PTX.Proof.afterLoad_ok rfl rfl hScalar]
      rfl
  have hFirst : run kernel Assumptions.all adjacentLaunch adjacentWriter 1 t2 = some t2a := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSecond : run kernel Assumptions.all adjacentLaunch adjacentWriter 1 t2a = some t2b := by
    have hAt : PTX.Proof.At t2a 2956 [] := ⟨rfl,rfl,rfl,rfl,trivial⟩
    apply PTX.Flow.run_local Flow.code_2956 rfl hAt
    rw [Assumptions.execLocalA_all_eq_numeric,Assumptions.execLocalA_eq_nil
      (show 2956 ∉ Assumptions.swExp2Sites by decide) rfl,
      PTX.Proof.execLocalA_nil,execLocal_int rfl]
    have h2394 : readBits adjacentLaunch adjacentWriter t2a 32 (.reg 2394) =
        .ok (BitVec.ofNat 64 (2^30+129)) := by kernel_rfl
    have hValue : readValue adjacentLaunch adjacentWriter t2a 32 (.reg 2394) =
        .ok (PTX.Proof.b32 (2^30+129)) := by rfl
    simp only [execInt,DType.width,hValue,h2394,hRead t2a rfl,bind,Except.bind,
      pure,Except.pure]
    rfl
  have hThird : run kernel Assumptions.all adjacentLaunch adjacentWriter 1 t2b = some t3 := by
    set_option maxRecDepth 100000 in kernel_rfl
  have readyPath : run kernel Assumptions.all adjacentLaunch adjacentWriter 3 t2 = some t3 :=
    run_comp (m := 2) (n := 1) (run_comp (m := 1) (n := 1) hFirst hSecond) hThird
  have waitStep : EStep kernel Assumptions.all adjacentLaunch adjacentWriter t3
      ⟨2958, .wait ready 0 true true .cta⟩ (some t4) := by
    refine ⟨.wait ready 0 (fun ok => next (setReg t3 9748 (.pred ok))) true .cta,
      ?_, true, rfl, rfl⟩
    set_option maxRecDepth 100000 in kernel_rfl
  have storePath : run kernel Assumptions.all adjacentLaunch adjacentWriter 3 t4 = some t5 := by
    set_option maxRecDepth 100000 in kernel_rfl
  have storeStep : EStep kernel Assumptions.all adjacentLaunch adjacentWriter t5
      ⟨2963, .tensorStore adjacentParams.oMapAddress adjacentStore⟩ (some (next t5)) := by
    let words : List (BitVec 64) := [0, 2 ^ 30 - 9, 0, 138]
    let source := Epilogue.sharedSlot adjacentLaunch adjacentWriter 0 0
    have hOrigin : Epilogue.originOf words = oCoordinate adjacentObserved 1 0 0 0 := by
      funext axis
      fin_cases axis <;> rfl
    have coord (r n : Nat)
        (h : readBits adjacentLaunch adjacentWriter t5 32 (.reg r) = .ok (BitVec.ofNat 64 n)) :
        readBits adjacentLaunch adjacentWriter t5 32 (.reg r) = .ok (BitVec.ofNat 64 n) := h
    have hCoords : (Epilogue.storeCoords 0 0).mapM (readBits adjacentLaunch adjacentWriter t5 32) =
        .ok words := by
      have h0 := coord 7229 0 (by kernel_rfl)
      have h1 := coord 2395 (2^30-9) (by kernel_rfl)
      have h2 := coord 7227 0 (by kernel_rfl)
      change ([.reg 7229, .reg 2395, .reg 7227, .reg 2393] : List Opnd).mapM
        (readBits adjacentLaunch adjacentWriter t5 32) = .ok words
      simp only [List.mapM_cons,List.mapM_nil,h0,h1,h2,
        hRead t5 rfl,bind,Except.bind,pure,Except.pure]
      rfl
    have hSource : sharedEffAddr adjacentLaunch adjacentWriter t5 false 2535 3072 =
        .ok source := by kernel_rfl
    have hPolicy : cachePolicyRead adjacentLaunch adjacentWriter t5 (some (.reg 7869)) =
        .ok () := by kernel_rfl
    have hOut := Epilogue.storeTemplate adjacentPre 0 0 adjacentWriter t5 source words
      rfl rfl rfl hCoords hSource (by decide) hPolicy (by
        intro axis
        fin_cases axis <;> decide) (by decide)
    have hSpec : Epilogue.storeSpec adjacentParams source words = adjacentStore := by
      unfold Epilogue.storeSpec
      rw [hOrigin]
      rfl
    refine ⟨.tensorStore adjacentParams.oMapAddress adjacentStore (next t5), ?_, rfl, rfl⟩
    rw [Epilogue.epilogue_out_all_eq_nil (show Epilogue.EpiloguePc t5.pc from
      (show Epilogue.EpiloguePc 2963 from .inl ⟨by decide, by decide⟩)), hOut, hSpec]
  exact ⟨next t5, .step .refl read0 (.step .refl read1 (.step (run_rtg readyPath) waitStep
    (.step (run_rtg storePath) storeStep (.nil _))))⟩

/-- The actual floating-point payload of the numeric witness reaches the output TMA
instruction and places its destination over the original launch word. -/
public theorem writebackGeometryCanCoverFloatCuQ :
    ∃ (p : Params) (l : Launch) (m : Mem0), Pre p l m ∧ p.qOffset p.batch = 137 ∧
      let changed := { p with qOffset := fun i => if i = p.batch then 138 else p.qOffset i }
      let g := 6 * l.block + 416
      let store := Epilogue.writebackStoreSpec changed l g 1 0 0 0 0
      Epilogue.assignedCoordinates changed 1 6 = (0, 0) ∧
      (⟨store.outer, store.descriptor⟩ : (n : Nat) × Descriptor n) = ⟨3, p.oMap⟩ ∧
      TensorStore.Valid 6 store ∧ BoxAligned store.descriptor store.origin ∧
      (∃ start out, Run kernel Assumptions.all l g start
        [Epilogue.endpointEvent changed 1 0,
          ⟨2954,.rd (Epilogue.endpointAccess changed 2)
            (Audit.cuQNormalCorrectionValue.toBytes.map some)⟩,
          ⟨2958, .wait (Epilogue.readyLoc l g 0) 0 true true .cta⟩,
          ⟨2963, .tensorStore p.oMapAddress store⟩] (some out)) ∧
      ∀ k < 4, TensorStore.writeLoc store 2 8 k =
        some ((globalLoc (p.cuQBase + 4 * p.batch)).at k) := by
  refine ⟨adjacentParams, adjacentLaunch, adjacentMemory, adjacentPre, rfl, ?_⟩
  refine ⟨by decide +kernel, rfl, ?_, by decide +kernel, ?_, ?_⟩
  · refine ⟨by decide, by decide, ?_, rfl, rfl, rfl⟩
    intro ys h
    cases h
  · have hRead (t : TState) (h : t.regs 2393 = some Audit.cuQNormalCorrectionValue) :
        readBits adjacentLaunch adjacentWriter t 32 (.reg 2393) = .ok (BitVec.ofNat 64 138) := by
      have hb := Audit.cuQNormalCorrectionBits
      unfold Audit.cuQNormalCorrectionValue at hb h
      simp only [readBits,readReg,h,bind,Except.bind,hb,pure,Except.pure]
      rfl
    obtain ⟨out, hr⟩ := adjacentReadToStoreOfDecodedWord _ (by decide) rfl hRead
    exact ⟨adjacentReadState, out, hr⟩
  · intro k hk
    have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel


end
end PTX.Kernels.TmlFa4Fwd
