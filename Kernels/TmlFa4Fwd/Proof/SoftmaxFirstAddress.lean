-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedAddress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxPublishTail
import Kernels.TmlFa4Fwd.Flow.Code.Part060

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0}

private theorem firstStagePrep (hp : Pre p l m) (g : Nat) (warp : Fin 8) :
    Seg kernel Assumptions.all l g 5 3850 (tailFrame l warp) 3855
      [(3218, b32 (scoreColumn (stageOf warp))),
        (3217, b32 (l.sharedBase + 8 * (stageOf warp).val))] := by
  have hBase := hp.shared.2.1
  fin_cases warp <;> intro t ht <;>
    seg_fp ht using norm_bits [scoreColumn, stageOf]

private theorem firstTid (hp : Pre p l m) (g : Nat) (warp : Fin 8) :
    Seg kernel Assumptions.all l g 1 3855
      [(3218, b32 (scoreColumn (stageOf warp))),
        (3217, b32 (l.sharedBase + 8 * (stageOf warp).val))] 3856
      [(3219, b32 (g % l.block)), (3218, b32 (scoreColumn (stageOf warp))),
        (3217, b32 (l.sharedBase + 8 * (stageOf warp).val))] := by
  intro t ht
  have hTid := (sregValue_oneDim hp.cluster.2.2 g).1
  have hBlock : g % l.block < 512 := hp.block ▸ Nat.mod_lt g (by rw [hp.block]; decide)
  have hSmall : g % l.block < 2^32 := by omega
  let u := next (setReg t 3219 (b32 (g % l.block)))
  have hu : run kernel Assumptions.all l g 1 t = some u := by
    apply run_local Flow.code_3855 rfl ht
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil (by
      rw [ht.1]
      decide) rfl]
    simp [u, execLocalA, execLocalRule, execLocal, Op.rule, MoveInstr.rule, execMove,
      DType.width, readValue, readBits, SReg.width, hTid, bind, Except.bind,
      pure, Except.pure, truncBits_ofNat hSmall (by decide), Value.bytes, b32]
  exact ⟨u, hu, ht.set (by simp)⟩

private theorem firstLaneField (hp : Pre p l m) (g : Nat) (warp : Fin 8) :
    Seg kernel Assumptions.all l g 2 3856
      [(3219, b32 (g % l.block)), (3218, b32 (scoreColumn (stageOf warp))),
        (3217, b32 (l.sharedBase + 8 * (stageOf warp).val))] 3858
      [(3221, b32 (65536 * laneBase l g)), (3219, b32 (g % l.block)),
        (3218, b32 (scoreColumn (stageOf warp))),
        (3217, b32 (l.sharedBase + 8 * (stageOf warp).val))] := by
  intro t ht
  have hBlock : g % l.block < 512 := hp.block ▸ Nat.mod_lt g (by rw [hp.block]; decide)
  have hSmall : g % l.block < 4294967296 := by omega
  have hShift : (g % l.block) * 65536 < 4294967296 := by omega
  have hMask : ((g % l.block) * 65536) &&& 6291456 = 65536 * laneBase l g := by
    have h := tmem_lane_field_mask l g
    rwa [Nat.shiftLeft_eq] at h
  have hMaskN : ((g % l.block % 4294967296) * 65536 % 4294967296) &&& 6291456 =
      65536 * laneBase l g := by
    rw [Nat.mod_eq_of_lt hSmall, Nat.mod_eq_of_lt hShift, hMask]
  have hField : 65536 * laneBase l g < 2^32 := by
    simpa only [Nat.add_zero, Nat.reducePow] using tmem_warp_encoding_lt l g (col := 0) (by decide)
  seg_fp ht using norm_bits [hMaskN, Nat.mod_eq_of_lt hField]

/-- The destination words for the first P publication, ordered by its quarter stores. -/
def firstAddressFacts (l : Launch) (g : Nat) (stage : Fin 2) : List (Nat × Value) :=
  [(3223, b32 (probabilityAddress l g stage 0)), (3224, b32 (probabilityAddress l g stage 3)),
    (3225, b32 (probabilityAddress l g stage 2)), (3226, b32 (probabilityAddress l g stage 1)),
    (3219, b32 (g % l.block)), (3217, b32 (l.sharedBase + 8 * stage.val))]

private theorem firstAddressOr (l : Launch) (g : Nat) (stage : Fin 2) :
    Seg kernel Assumptions.all l g 5 3858
      [(3221, b32 (65536 * laneBase l g)), (3219, b32 (g % l.block)),
        (3218, b32 (scoreColumn stage)), (3217, b32 (l.sharedBase + 8 * stage.val))]
      3863 (firstAddressFacts l g stage) := by
  fin_cases stage <;> intro t ht <;>
    simp only [firstAddressFacts, scoreColumn, probabilityAddress, probabilityColumn] at ht ⊢ <;>
    seg_fp ht using
      first
      | exact probabilityAddressBits l g 0 64 (by decide) (by decide)
      | exact probabilityAddressBits l g 0 112 (by decide) (by decide)
      | exact probabilityAddressBits l g 0 96 (by decide) (by decide)
      | exact probabilityAddressBits l g 0 80 (by decide) (by decide)
      | exact probabilityAddressBits l g 128 64 (by decide) (by decide)
      | exact probabilityAddressBits l g 128 112 (by decide) (by decide)
      | exact probabilityAddressBits l g 128 96 (by decide) (by decide)
      | exact probabilityAddressBits l g 128 80 (by decide) (by decide)

/-- The first post-bias instructions read the thread ID and derive all four P destinations. -/
theorem firstPAddressSegment (hp : Pre p l m) (g : Nat) (warp : Fin 8) :
    Seg kernel Assumptions.all l g 13 3850 (tailFrame l warp) 3863
      (firstAddressFacts l g (stageOf warp)) :=
  (((firstStagePrep hp g warp).comp (firstTid hp g warp)).comp
    (firstLaneField hp g warp)).comp (firstAddressOr l g (stageOf warp))

/-- Registers written by the first P publication address calculation. -/
def firstAddressWrites : List Nat := [493, 1047] ++ (List.range 11).map (3216 + ·)

private theorem firstAddressCode (i : Fin 13) :
    ∃ ins, kernel.code[3850 + i.val]? = some ins ∧
      Assumptions.coreOp ins.op = true ∧ nextPc ins.op (3850 + i.val) = 3850 + i.val + 1 ∧
      (∀ target, ¬ BrxTarget ins.op target) ∧
      (writesRegs ins.op).all (· ∈ firstAddressWrites) = true := by
  fin_cases i
  · exact ⟨_, Flow.code_3850, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_3851, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_3852, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_3853, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_3854, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_3855, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_3856, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_3857, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_3858, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_3859, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_3860, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_3861, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_3862, rfl, rfl, fun _ => nofun, by decide⟩

/-- Apart from its listed destinations, the address setup preserves the bias and geometry. -/
theorem firstPAddressFrame {l : Launch} {g n : Nat} {t u : TState}
    (hStart : 3850 ≤ t.pc) (hEnd : t.pc + n ≤ 3863)
    (hRun : run kernel Assumptions.all l g n t = some u) :
    ∀ r ∉ firstAddressWrites, u.regs r = t.regs r := by
  apply fixedFrame (first := 3850) (stop := 3863) _ _ hStart hEnd hRun
  · intro pc hlo hhi
    let i : Fin 13 := ⟨pc - 3850, by omega⟩
    have hi : 3850 + i.val = pc := by dsimp [i]; omega
    obtain ⟨ins, hc, hCore, hPC, hNoBrx, hWrites⟩ := firstAddressCode i
    rw [hi] at hc hPC
    refine ⟨ins, hc, hCore, hPC, hNoBrx, fun r hr hm => ?_⟩
    exact hr (of_decide_eq_true (List.all_eq_true.mp hWrites r hm))
  · intro pc hlo hhi
    simp [Assumptions.swExp2Sites]
    omega

/-- The actual bias tail advances to the mask geometry with live P destinations. -/
theorem firstPAddressTrace (hp : Pre p l m) (warp : Fin 8) {g : Nat} {t : TState} {es : List Event}
    (ht : At t 3850 (tailFrame l warp)) (hr : Run kernel Assumptions.all l g t es none) :
    ∃ u, At u 3863 (firstAddressFacts l g (stageOf warp)) ∧
      (∀ q : Fin 4, u.regs (probabilityReg .first q) =
        some (b32 (probabilityAddress l g (stageOf warp) q))) ∧
      Run kernel Assumptions.all l g u es none ∧
      ∀ r ∉ firstAddressWrites, u.regs r = t.regs r := by
  obtain ⟨u, hLocal, hu⟩ := (firstPAddressSegment hp g warp).apply ht
  refine ⟨u, hu, fun q => holds_mem hu.2.2.2.2 ?_, hr.after_local (run_rtg hLocal),
    firstPAddressFrame ht.1.ge (by rw [ht.1]) hLocal⟩
  fin_cases q <;> simp [probabilityReg, firstAddressFacts]

end
end PTX.Kernels.TmlFa4Fwd.Softmax
