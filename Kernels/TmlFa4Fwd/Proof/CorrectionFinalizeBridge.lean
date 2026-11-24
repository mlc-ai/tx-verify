-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeChunk
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part133
import Kernels.TmlFa4Fwd.Flow.Code.Part134
import Kernels.TmlFa4Fwd.Flow.Code.Part135
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Flow.Code.Part138
import Kernels.TmlFa4Fwd.Flow.Code.Part139
import Kernels.TmlFa4Fwd.Flow.Code.Part140
import Kernels.TmlFa4Fwd.Flow.Code.Part141

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The gap after a chunk computes the next tensor address and, in the first subbox,
the even vector's shared address. -/
def finalizeBridgePc (stage : Fin 2) (chunk : Fin 16) : Nat :=
  finalizeLoadPc stage chunk - if chunk.val < 4 then 2 else 1

theorem finalizeBridge_pc (stage : Fin 2) (chunk : Fin 16) (hn : 0 < chunk.val) :
    outputStorePc stage (finalizeSubset ⟨chunk.val - 1, by omega⟩)
      (finalizeVector ⟨chunk.val - 1, by omega⟩ 1) + 1 = finalizeBridgePc stage chunk := by
  unfold outputStorePc finalizeSubset finalizeVector finalizeBridgePc finalizeLoadPc
  dsimp only
  change (8492 + 296 * stage.val +
    (if (chunk.val - 1) / 4 = 0 then
      19 * ((2 * ((chunk.val - 1) % 4) + 1) / 2) +
        4 * ((2 * ((chunk.val - 1) % 4) + 1) % 2)
    else 75 + 68 * ((chunk.val - 1) / 4 - 1) +
      17 * ((2 * ((chunk.val - 1) % 4) + 1) / 2) +
        3 * ((2 * ((chunk.val - 1) % 4) + 1) % 2))) + 1 = _
  by_cases h : chunk.val < 4
  · simp only [ite_eq_left h, ite_eq_left (show (chunk.val - 1) / 4 = 0 by omega)]
    omega
  · by_cases h4 : chunk.val = 4
    · simp [h4]
      omega
    · simp only [ite_eq_right h, ite_eq_right (show (chunk.val - 1) / 4 ≠ 0 by omega)]
      omega

private def finalizeAddInstr (dst src : Nat) (opnd : Opnd) : Instr :=
  ⟨none, .int ⟨.add, .int .s 32, false, [some dst], [.reg src, opnd]⟩⟩

private theorem finalizeAddressCode (stage : Fin 2) (chunk : Fin 16) (hn : 0 < chunk.val) :
    kernel.code[finalizeBridgePc stage chunk]? =
      some (finalizeAddInstr (finalizeAddressReg stage chunk) 1629
        (.imm (128 * (stage.val : Int) + 8 * (chunk.val : Int)))) := by
  fin_cases stage <;> fin_cases chunk <;> try (simp at hn)
  · exact Flow.code_8497
  · exact Flow.code_8516
  · exact Flow.code_8535
  · exact Flow.code_8554
  · exact Flow.code_8571
  · exact Flow.code_8588
  · exact Flow.code_8605
  · exact Flow.code_8622
  · exact Flow.code_8639
  · exact Flow.code_8656
  · exact Flow.code_8673
  · exact Flow.code_8690
  · exact Flow.code_8707
  · exact Flow.code_8724
  · exact Flow.code_8741
  · exact Flow.code_8793
  · exact Flow.code_8812
  · exact Flow.code_8831
  · exact Flow.code_8850
  · exact Flow.code_8867
  · exact Flow.code_8884
  · exact Flow.code_8901
  · exact Flow.code_8918
  · exact Flow.code_8935
  · exact Flow.code_8952
  · exact Flow.code_8969
  · exact Flow.code_8986
  · exact Flow.code_9003
  · exact Flow.code_9020
  · exact Flow.code_9037

private theorem finalizeAddRun {l : Launch} {g pc d r : Nat} {t : TState}
    {F : List (Nat × Value)} {opnd : Opnd} {a b : Nat} (ht : At t pc F)
    (hPc : 8480 ≤ pc) (hCode : kernel.code[pc]? = some (finalizeAddInstr d r opnd))
    (hRead : t.regs r = some (b32 a)) (hA : a < 2 ^ 32) (hB : b < 2 ^ 32)
    (hLocal : opnd.varying? = none)
    (hOp : readBits l g t 32 opnd = .ok (BitVec.ofNat 64 b))
    (hValue : readValue l g t 32 opnd = .ok (b32 b))
    (hFresh : ∀ rv ∈ F, rv.1 ≠ d) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (pc + 1) ((d, b32 ((a + b) % (2 ^ 32))) :: F) := by
  let u := next (setReg t d (b32 ((a + b) % (2 ^ 32))))
  have hCore : run kernel [] l g 1 t = some u := by
    have hIsLocal : (finalizeAddInstr d r opnd).op.isLocal = true := by
      change (Option.toList none ++ (opnd.varying?).toList).isEmpty = true
      simp [hLocal]
    apply run_local hCode hIsLocal ht
    rw [execLocalA_nil, execLocal_int rfl]
    have hSum : a + b < 2 ^ 64 := by omega
    have hValueA : readValue l g t 32 (.reg r) = .ok (b32 a) := by
      simp [readValue, readReg, hRead, pure, Except.pure]
    simp only [execInt, DType.width, hValueA, hValue, readBits_b32 hRead hA, hOp,
      pure, Except.pure, bind, Except.bind, ← BitVec.ofNat_add, truncBits, toNat_ofNat_lt hSum,
      b32, u]
  have hOut : out kernel Assumptions.all l g t = out kernel [] l g t := by
    apply Assumptions.out_all_eq_nil _ _ _ (ht.1.symm ▸ hCode) rfl
    all_goals
      rw [ht.1]
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega
  have hAll : run kernel Assumptions.all l g 1 t = some u := by
    simpa only [run, tauStep, hOut] using hCore
  exact ⟨u, run_rtg hAll, ht.set hFresh⟩

/-- The actual address add always uses the first stage's base with the encoded column offset. -/
theorem finalizeBridgeTmem {l : Launch} {g : Nat} {t : TState} {F : List (Nat × Value)}
    (stage : Fin 2) (chunk : Fin 16) (hn : 0 < chunk.val)
    (ht : At t (finalizeBridgePc stage chunk) F)
    (hBase : t.regs 1629 = some (b32 (outputAddress l g 0 0)))
    (hFresh : ∀ rv ∈ F, rv.1 ≠ finalizeAddressReg stage chunk) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (finalizeBridgePc stage chunk + 1)
        ((finalizeAddressReg stage chunk, b32 (outputAddress l g stage (8 * chunk.val))) :: F) := by
  let col := 128 * stage.val + 8 * chunk.val
  have hCol : col < 256 := by
    have hs := stage.isLt
    have hc := chunk.isLt
    dsimp only [col]
    omega
  have hAddr := tmem_warp_encoding_lt l g (col := 256 + col) (by omega)
  have hBaseBound : outputAddress l g 0 0 < 2 ^ 32 :=
    tmem_warp_encoding_lt l g (col := 256) (by decide)
  have hPC : 8480 ≤ finalizeBridgePc stage chunk := by
    unfold finalizeBridgePc finalizeLoadPc
    split <;> omega
  have hOp : readBits l g t 32 (.imm (128 * (stage.val : Int) + 8 * (chunk.val : Int))) =
      .ok (BitVec.ofNat 64 col) := by
    have hInt : (128 * (stage.val : Int) + 8 * (chunk.val : Int)) = (col : Int) := by
      push_cast [col]
      rfl
    rw [hInt]
    simp only [readBits, BitVec.ofInt_natCast,
      truncBits_ofNat (show col < 2 ^ 32 by omega) (by decide), pure, Except.pure]
  obtain ⟨u, hu, hU⟩ := finalizeAddRun ht hPC (finalizeAddressCode stage chunk hn) hBase
    hBaseBound (by omega) rfl hOp
    (by simp [readValue, hOp, b32, bind, Except.bind, pure, Except.pure]) hFresh
  have hSum : outputAddress l g 0 0 + col = outputAddress l g stage (8 * chunk.val) := by
    simp only [outputAddress, outputColumn, Fin.val_zero, Nat.mul_zero, Nat.add_zero, col]
    omega
  have hBound : outputAddress l g 0 0 + col < 2 ^ 32 := by
    change 65536 * laneBase l g + (256 + col) < 2 ^ 32 at hAddr
    change 65536 * laneBase l g + 256 + col < 2 ^ 32
    omega
  rw [Nat.mod_eq_of_lt hBound, hSum] at hU
  exact ⟨u, hu, hU⟩

/-- The first subbox materializes the three additional even vectors from previously
computed vectors by toggling swizzle bit one or two. -/
def finalizeEvenBase (chunk : Fin 16) : Fin 16 := if chunk.val = 3 then 2 else 0

def finalizeEvenDeltaReg (chunk : Fin 16) : Nat := if chunk.val = 2 then 6504 else 6502

def finalizeEvenDelta (l : Launch) (g : Nat) (chunk : Fin 16) : Nat :=
  let bit := if chunk.val = 2 then 4 else 2
  if (rowOf l g % 8) &&& bit = 0 then 16 * bit else 2 ^ 32 - 16 * bit

private theorem finalizeEvenCode (stage : Fin 2) (chunk : Fin 16) (hn : 0 < chunk.val)
    (hc : chunk.val < 4) :
    kernel.code[finalizeBridgePc stage chunk + 1]? =
      some (finalizeAddInstr (outputStoreAddrReg stage (finalizeVector chunk 0))
        (outputStoreAddrReg stage (finalizeVector (finalizeEvenBase chunk) 0))
        (.reg (finalizeEvenDeltaReg chunk))) := by
  fin_cases stage <;> fin_cases chunk <;> try (simp at hn hc)
  · exact Flow.code_8498
  · exact Flow.code_8517
  · exact Flow.code_8536
  · exact Flow.code_8794
  · exact Flow.code_8813
  · exact Flow.code_8832

private theorem finalizeEvenArithmetic {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (g : Nat) (stage : Fin 2) (chunk : Fin 16)
    (hn : 0 < chunk.val) (hc : chunk.val < 4) :
    (finalizeVectorAddress l g stage (finalizeEvenBase chunk) 0 +
      finalizeEvenDelta l g chunk) % 2 ^ 32 = finalizeVectorAddress l g stage chunk 0 := by
  let base := l.sharedBase + (3072 + 65536 * stage.val) + 128 * rowOf l g
  have hb : base + 128 < 2 ^ 32 := by
    have hs := stage.isLt
    have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
    have hShared := hp.shared.2.1
    dsimp only [base]
    omega
  have hAddr (c : Fin 16) : finalizeVectorAddress l g stage c 0 =
      base + 16 * ((finalizeVector c 0).val ^^^ (rowOf l g % 8)) := by
    simp only [finalizeVectorAddress, outputChunkLoc, sharedSlot, Loc.at, base]
    omega
  rw [hAddr, hAddr]
  let r := rowOf l g % 8
  let bit := if chunk.val = 2 then 4 else 2
  let src := (finalizeVector (finalizeEvenBase chunk) 0).val ^^^ r
  let dst := (finalizeVector chunk 0).val ^^^ r
  have hd : 16 * dst < 128 := by
    have hx : dst < 8 := Nat.xor_lt_two_pow (n := 3) (finalizeVector chunk 0).isLt
      (Nat.mod_lt _ (by decide))
    omega
  have hOffsets : (16 * src + (if r &&& bit = 0 then 16 * bit else 2 ^ 32 - 16 * bit)) %
      2 ^ 32 = 16 * dst := by
    dsimp only [src, dst, bit]
    have hR : r < 8 := Nat.mod_lt _ (by decide)
    generalize r = row at hR ⊢
    fin_cases chunk <;> try (simp at hn hc)
    all_goals interval_cases row <;> decide
  change (base + 16 * src + (if r &&& bit = 0 then 16 * bit else 2 ^ 32 - 16 * bit)) %
    2 ^ 32 = base + 16 * dst
  rw [Nat.add_assoc, Nat.add_mod base, hOffsets,
    Nat.mod_eq_of_lt (a := base) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Compute the shared address of the next even vector in the first subbox. -/
theorem finalizeBridgeEven {p : Params} {l : Launch} {m : Mem0} {g : Nat} {t : TState}
    {F : List (Nat × Value)} (hp : Pre p l m) (stage : Fin 2)
    (chunk : Fin 16) (hn : 0 < chunk.val) (hc : chunk.val < 4)
    (ht : At t (finalizeBridgePc stage chunk + 1) F)
    (hBase : t.regs (outputStoreAddrReg stage (finalizeVector (finalizeEvenBase chunk) 0)) =
      some (b32 (finalizeVectorAddress l g stage (finalizeEvenBase chunk) 0)))
    (hDelta : t.regs (finalizeEvenDeltaReg chunk) = some (b32 (finalizeEvenDelta l g chunk)))
    (hFresh : ∀ rv ∈ F, rv.1 ≠ outputStoreAddrReg stage (finalizeVector chunk 0)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (finalizeLoadPc stage chunk)
        ((outputStoreAddrReg stage (finalizeVector chunk 0),
          b32 (finalizeVectorAddress l g stage chunk 0)) :: F) := by
  have hPc : finalizeBridgePc stage chunk + 1 + 1 = finalizeLoadPc stage chunk := by
    unfold finalizeBridgePc finalizeLoadPc
    simp only [ite_eq_left hc]
    omega
  have hLo : 8480 ≤ finalizeBridgePc stage chunk + 1 := by
    unfold finalizeBridgePc finalizeLoadPc
    simp only [ite_eq_left hc]
    omega
  have hA : finalizeVectorAddress l g stage (finalizeEvenBase chunk) 0 < 2 ^ 32 := by
    have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
    have hXor : ((finalizeVector (finalizeEvenBase chunk) 0).val ^^^ rowOf l g % 8) < 8 :=
      Nat.xor_lt_two_pow (n := 3)
        (finalizeVector (finalizeEvenBase chunk) 0).isLt (Nat.mod_lt (rowOf l g) (by decide))
    have hStage := stage.isLt
    have hShared := hp.shared.2.1
    simp only [finalizeVectorAddress, outputChunkLoc, sharedSlot, Loc.at]
    omega
  have hB : finalizeEvenDelta l g chunk < 2 ^ 32 := by
    unfold finalizeEvenDelta
    split <;> dsimp only <;> split <;> decide
  obtain ⟨u, hu, hU⟩ := finalizeAddRun ht hLo (finalizeEvenCode stage chunk hn hc)
    hBase hA hB rfl (readBits_b32 hDelta hB)
    (by simp [readValue, readReg, hDelta, pure, Except.pure]) hFresh
  rw [hPc, finalizeEvenArithmetic hp g stage chunk hn hc] at hU
  exact ⟨u, hu, hU⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
