-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedAddress
import Kernels.TmlFa4Fwd.Flow.Code.Part104

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

private theorem unbiasedProbabilityStage (l : Launch) (g : Nat) (w : Fin 8) :
    Seg kernel Assumptions.all l g 2 6661 [(1062,b32 w.val)]
      6663 [(644,.pred ((stageOf w).val = 1)),(5176,b32 (scoreColumn (stageOf w)))] := by
  intro t ht
  fin_cases w <;> seg_fp ht using decide

variable {p : Params} {l : Launch}

private theorem unbiasedProbabilityTid {m : Mem0} (hp : Pre p l m) (g : Nat) (stage : Fin 2) :
    Seg kernel Assumptions.all l g 1 6663 [(5176,b32 (scoreColumn stage))]
      6664 [(5177,b32 (g % l.block)),(5176,b32 (scoreColumn stage))] := by
  intro t ht
  have hTid := (sregValue_oneDim hp.cluster.2.2 g).1
  have hBlock : g % l.block < 512 := hp.block ▸ Nat.mod_lt g (by rw [hp.block]; decide)
  have hSmall : g % l.block < 2^32 := by omega
  let u := next (setReg t 5177 (b32 (g % l.block)))
  have hu : run kernel Assumptions.all l g 1 t = some u := by
    apply run_local Flow.code_6663 rfl ht
    rw [Assumptions.execLocalA_all_eq_numeric,
      Assumptions.execLocalA_eq_nil (by rw [ht.1]; decide) rfl]
    simp [u,execLocalA,execLocalRule,execLocal,Op.rule,MoveInstr.rule,execMove,DType.width,
      readValue,readBits,SReg.width,hTid,bind,Except.bind,pure,Except.pure,
      truncBits_ofNat hSmall (by decide),Value.bytes,b32]
  exact ⟨u,hu,ht.set (by simp)⟩

private theorem unbiasedProbabilityLaneField {m : Mem0} (hp : Pre p l m) (g : Nat) (stage : Fin 2) :
    Seg kernel Assumptions.all l g 2 6664
      [(5177,b32 (g % l.block)),(5176,b32 (scoreColumn stage))]
      6666 [(5179,b32 (65536 * laneBase l g)),(5176,b32 (scoreColumn stage))] := by
  intro t ht
  have hBlock : g % l.block < 512 := hp.block ▸ Nat.mod_lt g (by rw [hp.block]; decide)
  have hSmall : g % l.block < 4294967296 := by omega
  have hShift : (g % l.block) * 65536 < 4294967296 := by omega
  have hMask : ((g % l.block) * 65536) &&& 6291456 = 65536 * laneBase l g := by
    have h := tmem_lane_field_mask l g
    rwa [Nat.shiftLeft_eq] at h
  have hMaskN : ((g % l.block % 4294967296) * 65536 % 4294967296) &&& 6291456 =
      65536 * laneBase l g := by
    rw [Nat.mod_eq_of_lt hSmall,Nat.mod_eq_of_lt hShift,hMask]
  have hField : 65536 * laneBase l g < 2^32 := by
    simpa only [Nat.add_zero,Nat.reducePow] using tmem_warp_encoding_lt l g (col := 0) (by decide)
  seg_fp ht using norm_bits [hMaskN,Nat.mod_eq_of_lt hField]

/-- The four destination registers of the unbiased probability publication. -/
def unbiasedProbabilityFacts (l : Launch) (g : Nat) (stage : Fin 2) : List (Nat × Value) :=
  [(5183,b32 (probabilityAddress l g stage 0)),(5185,b32 (probabilityAddress l g stage 1)),
    (5181,b32 (probabilityAddress l g stage 2)),(5184,b32 (probabilityAddress l g stage 3))]

def roundScoreFacts (l : Launch) (g : Nat) (stage : Fin 2) (round : Round) :
    List (Nat × Value) :=
  List.ofFn fun q => (scoreReg round q,b32 (scoreAddress l g stage q))

theorem scoreBaseAddressBits (l : Launch) (g c : Nat) (hc : c < 512) :
    Value.bits 32 (truncBits 32 (BitVec.ofNat 64 c) |||
      truncBits 32 (BitVec.ofNat 64 (65536 * laneBase l g))) =
        b32 (65536 * laneBase l g + c) := by
  have hField : 65536 * laneBase l g < 2^32 :=
    by simpa only [Nat.add_zero,Nat.reducePow] using
      tmem_warp_encoding_lt l g (col := 0) (by decide)
  have hOr := tmem_lane_or_column (lane := laneBase l g) hc
  rw [truncBits_ofNat (by omega : c < 2^32) (by decide),truncBits_ofNat hField (by decide),
    ← BitVec.ofNat_or,Nat.or_comm c]
  simpa only [Nat.shiftLeft_eq,Nat.mul_comm (laneBase l g) 65536,Nat.reducePow,b32]
    using congrArg (fun n => Value.bits 32 (BitVec.ofNat 64 n)) hOr

private theorem unbiasedProbabilityOr (l : Launch) (g : Nat) (stage : Fin 2) :
    Seg kernel Assumptions.all l g 6 6666
      [(5179,b32 (65536 * laneBase l g)),(5176,b32 (scoreColumn stage))]
      6672 (unbiasedProbabilityFacts l g stage ++ roundScoreFacts l g stage .unbiased) := by
  fin_cases stage <;> intro t ht <;>
    simp only [unbiasedProbabilityFacts,roundScoreFacts,List.ofFn_succ,List.ofFn_zero,
      List.cons_append,List.nil_append,scoreReg,scoreAddress,scoreColumn,probabilityAddress,
      probabilityColumn]
      at ht ⊢ <;>
    seg_fp ht using
      first
      | exact probabilityAddressBits l g 0 64 (by decide) (by decide)
      | exact probabilityAddressBits l g 0 80 (by decide) (by decide)
      | exact probabilityAddressBits l g 0 96 (by decide) (by decide)
      | exact probabilityAddressBits l g 0 112 (by decide) (by decide)
      | exact probabilityAddressBits l g 128 64 (by decide) (by decide)
      | exact probabilityAddressBits l g 128 80 (by decide) (by decide)
      | exact probabilityAddressBits l g 128 96 (by decide) (by decide)
      | exact probabilityAddressBits l g 128 112 (by decide) (by decide)
      | exact scoreBaseAddressBits l g 0 (by decide)
      | exact probabilityAddressBits l g 0 32 (by decide) (by decide)
      | exact scoreBaseAddressBits l g 128 (by decide)
      | exact probabilityAddressBits l g 128 32 (by decide) (by decide)

/-- The lane and stage values used again by the plain correction publication. -/
def unbiasedAddressRows (l : Launch) (g : Nat) (w : Fin 8) : List (Nat × Value) :=
  [(644,.pred ((stageOf w).val = 1)),(5176,b32 (scoreColumn (stageOf w))),
    (5177,b32 (g%l.block))]

def unbiasedSetupWrites : List Nat :=
  [644,5176,5177,5178,5179,5180,5181,5182,5183,5184,5185,1055,5186,5187,5126]

private theorem plainLocalCode (i : Fin 15) :
    ∃ ins, kernel.code[6661+i.val]? = some ins ∧ Assumptions.coreOp ins.op = true ∧
      nextPc ins.op (6661+i.val) = 6661+i.val+1 ∧
      (∀ target, ¬ BrxTarget ins.op target) ∧
      (writesRegs ins.op).all unbiasedSetupWrites.contains = true := by
  fin_cases i
  · exact ⟨_,Flow.code_6661,rfl,rfl,fun _ => nofun,rfl⟩
  · exact ⟨_,Flow.code_6662,rfl,rfl,fun _ => nofun,rfl⟩
  · exact ⟨_,Flow.code_6663,rfl,rfl,fun _ => nofun,rfl⟩
  · exact ⟨_,Flow.code_6664,rfl,rfl,fun _ => nofun,rfl⟩
  · exact ⟨_,Flow.code_6665,rfl,rfl,fun _ => nofun,rfl⟩
  · exact ⟨_,Flow.code_6666,rfl,rfl,fun _ => nofun,rfl⟩
  · exact ⟨_,Flow.code_6667,rfl,rfl,fun _ => nofun,rfl⟩
  · exact ⟨_,Flow.code_6668,rfl,rfl,fun _ => nofun,rfl⟩
  · exact ⟨_,Flow.code_6669,rfl,rfl,fun _ => nofun,rfl⟩
  · exact ⟨_,Flow.code_6670,rfl,rfl,fun _ => nofun,rfl⟩
  · exact ⟨_,Flow.code_6671,rfl,rfl,fun _ => nofun,rfl⟩
  · exact ⟨_,Flow.code_6672,rfl,rfl,fun _ => nofun,rfl⟩
  · exact ⟨_,Flow.code_6673,rfl,rfl,fun _ => nofun,rfl⟩
  · exact ⟨_,Flow.code_6674,rfl,rfl,fun _ => nofun,rfl⟩
  · exact ⟨_,Flow.code_6675,rfl,rfl,fun _ => nofun,rfl⟩

theorem unbiasedSetupFrame {l : Launch} {g n : Nat} {t u : TState}
    (hLo : 6661 ≤ t.pc) (hHi : t.pc+n ≤ 6676)
    (hRun : run kernel Assumptions.all l g n t = some u) :
    ∀ r ∉ unbiasedSetupWrites, u.regs r = t.regs r := by
  apply fixedFrame (first := 6661) (stop := 6676) (kept := fun r => r ∉ unbiasedSetupWrites)
    _ _ hLo hHi hRun
  · intro pc hlo hhi
    let i : Fin 15 := ⟨pc-6661,by omega⟩
    have hi : 6661+i.val = pc := by dsimp [i]; omega
    obtain ⟨ins,hCode,hCore,hPc,hNo,hWrites⟩ := plainLocalCode i
    rw [hi] at hCode hPc
    refine ⟨ins,hCode,hCore,hPc,hNo,?_⟩
    intro r hr hIn
    apply hr
    simpa only [List.contains_eq_mem,decide_eq_true_eq] using List.all_eq_true.mp hWrites r hIn
  · intro pc hlo hhi hm
    simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false] at hm
    omega

private theorem unbiasedRowFrameAfterTid {l : Launch} {g n : Nat} {t u : TState}
    (hLo : 6664 ≤ t.pc) (hHi : t.pc+n ≤ 6672)
    (hRun : run kernel Assumptions.all l g n t = some u) :
    ∀ r ∈ [644,5176,5177], u.regs r = t.regs r := by
  apply fixedFrame (first := 6664) (stop := 6672) _ _ hLo hHi hRun
  · intro pc hlo hhi
    interval_cases pc
    · exact ⟨_,Flow.code_6664,rfl,rfl,fun _ => nofun,by simp [writesRegs]⟩
    · exact ⟨_,Flow.code_6665,rfl,rfl,fun _ => nofun,by simp [writesRegs]⟩
    · exact ⟨_,Flow.code_6666,rfl,rfl,fun _ => nofun,by simp [writesRegs]⟩
    · exact ⟨_,Flow.code_6667,rfl,rfl,fun _ => nofun,by simp [writesRegs]⟩
    · exact ⟨_,Flow.code_6668,rfl,rfl,fun _ => nofun,by simp [writesRegs]⟩
    · exact ⟨_,Flow.code_6669,rfl,rfl,fun _ => nofun,by simp [writesRegs]⟩
    · exact ⟨_,Flow.code_6670,rfl,rfl,fun _ => nofun,by simp [writesRegs]⟩
    · exact ⟨_,Flow.code_6671,rfl,rfl,fun _ => nofun,by simp [writesRegs]⟩
  · intro pc hlo hhi hm
    simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false] at hm
    omega

/-- Decode the addresses and retain the exact thread and stage selection. -/
theorem unbiasedTensorAddressSegmentWithRows {m : Mem0} (hp : Pre p l m) (g : Nat) (w : Fin 8) :
    Seg kernel Assumptions.all l g 11 6661 [(1062,b32 w.val)]
      6672 (unbiasedAddressRows l g w ++ (unbiasedProbabilityFacts l g (stageOf w) ++
        roundScoreFacts l g (stageOf w) .unbiased)) := by
  intro t ht
  let stage := stageOf w
  obtain ⟨s,hSRun,hS⟩ := (unbiasedProbabilityStage l g w).apply ht
  obtain ⟨u,hURun,hU⟩ := (unbiasedProbabilityTid hp g stage).apply
    (hS.mono ⟨hS.2.2.2.2.2.1,trivial⟩)
  have hKeepStage : u.regs 644 = s.regs 644 := by
    refine fixedFrame (first := 6663) (stop := 6664) (kept := fun r => r = 644) ?_ ?_
      (by rw [hS.1]) (by rw [hS.1]) hURun 644 rfl
    · intro pc hlo hhi
      have hPc : pc = 6663 := by omega
      subst pc
      exact ⟨_,Flow.code_6663,rfl,rfl,fun _ => nofun,by
        intro r hr; subst r; decide⟩
    · intro pc hlo hhi
      have hPc : pc = 6663 := by omega
      rw [hPc]
      decide
  have hStage : u.regs 644 = some (.pred (stage.val = 1)) :=
    hKeepStage.trans hS.2.2.2.2.1
  obtain ⟨v,hVRun,hV⟩ :=
    ((unbiasedProbabilityLaneField hp g stage).comp (unbiasedProbabilityOr l g stage)).apply hU
  have hKeep := unbiasedRowFrameAfterTid (by rw [hU.1])
    (by rw [hU.1]) hVRun
  exact ⟨v,run_comp (run_comp hSRun hURun) hVRun,
    hV.mono ((holds_append ..).mpr ⟨
      ⟨(hKeep 644 (by decide)).trans hStage,
        (hKeep 5176 (by decide)).trans hU.2.2.2.2.2.1,
        (hKeep 5177 (by decide)).trans hU.2.2.2.2.1,trivial⟩,hV.2.2.2.2⟩)⟩

/-- The unbiased round computes its score and probability addresses from its warp and lane. -/
theorem unbiasedTensorAddressSegment {m : Mem0} (hp : Pre p l m) (g : Nat) (w : Fin 8) :
    Seg kernel Assumptions.all l g 11 6661 [(1062,b32 w.val)]
      6672 (unbiasedProbabilityFacts l g (stageOf w) ++
        roundScoreFacts l g (stageOf w) .unbiased) := by
  intro t ht
  obtain ⟨u,hr,hu⟩ := (unbiasedTensorAddressSegmentWithRows hp g w).apply ht
  exact ⟨u,hr,hu.mono ((holds_append ..).mp hu.2.2.2.2).2⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
