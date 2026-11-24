-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxPublish
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.TauFrame
import Kernels.TmlFa4Fwd.Flow.Code.Part098
import Kernels.TmlFa4Fwd.Flow.Code.Part102

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

private theorem biasedStageColumn (l : Launch) (g : Nat) (stage : Fin 2) :
    Seg kernel Assumptions.all l g 1 6299 [(637, .pred (stage.val = 1))]
      6300 [(4816, b32 (scoreColumn stage))] := by
  fin_cases stage <;> intro t ht <;> seg_fp ht using decide

private theorem biasedLaneId {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) :
    Seg kernel Assumptions.all l g 1 6300 [(4816, b32 (scoreColumn stage))]
      6301 [(4817, b32 (g % l.block)), (4816, b32 (scoreColumn stage))] := by
  intro t ht
  have hTid := (sregValue_oneDim hp.cluster.2.2 g).1
  have hBlock : g % l.block < 512 := hp.block ▸ Nat.mod_lt g (by rw [hp.block]; decide)
  have hSmall : g % l.block < 2 ^ 32 := by omega
  let u := next (setReg t 4817 (b32 (g % l.block)))
  have hu : run kernel Assumptions.all l g 1 t = some u := by
    apply run_local Flow.code_6300 rfl ht
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil (by
      rw [ht.1]
      decide) rfl]
    simp [u, execLocalA, execLocalRule, execLocal, Op.rule, MoveInstr.rule, execMove,
      DType.width, readValue, readBits, SReg.width, hTid, bind, Except.bind,
      pure, Except.pure, truncBits_ofNat hSmall (by decide), Value.bytes, b32]
  exact ⟨u, hu, ht.set (by simp)⟩

private theorem biasedLaneField {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) :
    Seg kernel Assumptions.all l g 2 6301
      [(4817, b32 (g % l.block)), (4816, b32 (scoreColumn stage))]
      6303 [(4819, b32 (65536 * laneBase l g)), (4816, b32 (scoreColumn stage))] := by
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
  have hField : 65536 * laneBase l g < 2 ^ 32 := by
    simpa only [Nat.add_zero, Nat.reducePow] using tmem_warp_encoding_lt l g (col := 0) (by decide)
  seg_fp ht using norm_bits [hMaskN, Nat.mod_eq_of_lt hField]

/-- The four P destinations derived from the biased round's warp-field and stage reads. -/
def biasedAddressFacts (l : Launch) (g : Nat) (stage : Fin 2) : List (Nat × Value) :=
  [(4821, b32 (probabilityAddress l g stage 0)), (4822, b32 (probabilityAddress l g stage 3)),
    (4823, b32 (probabilityAddress l g stage 2)), (4824, b32 (probabilityAddress l g stage 1))]

/-- Combining the TMEM warp field, stage column and quarter gives the modeled P address. -/
theorem probabilityAddressBits (l : Launch) (g stageCol extra : Nat)
    (hb : stageCol + extra < 512) (hor : stageCol ||| extra = stageCol + extra) :
    Value.bits 32
      (truncBits 32 (truncBits 32 (BitVec.ofNat 64 stageCol) |||
        truncBits 32 (BitVec.ofNat 64 (65536 * laneBase l g))) |||
        truncBits 32 (BitVec.ofNat 64 extra)) =
      b32 (65536 * laneBase l g + (stageCol + extra)) := by
  let field := 65536 * laneBase l g
  have hBounds (c : Nat) (hc : c < 512) : field + c < 2 ^ 32 := by
    simpa only [field, Nat.reducePow] using tmem_warp_encoding_lt l g hc
  have hField : field < 2 ^ 32 := by simpa only [Nat.add_zero] using hBounds 0 (by decide)
  have hLane (c : Nat) (hc : c < 512) : field ||| c = field + c := by
    simpa only [field, Nat.shiftLeft_eq, Nat.mul_comm, Nat.reducePow] using
      tmem_lane_or_column (lane := laneBase l g) (col := c) hc
  have hSc : stageCol < 512 := by omega
  have hExtra : extra < 2 ^ 32 := by omega
  rw [truncBits_ofNat (w := 32) (n := stageCol) (by omega) (by decide),
    truncBits_ofNat hField (by decide), truncBits_ofNat hExtra (by decide),
    ← BitVec.ofNat_or, Nat.or_comm stageCol, hLane stageCol hSc,
    truncBits_ofNat (hBounds stageCol hSc) (by decide),
    ← BitVec.ofNat_or, ← hLane stageCol hSc, Nat.or_assoc, hor, hLane _ hb]
  rfl

private theorem biasedAddressOr (l : Launch) (g : Nat) (stage : Fin 2) :
    Seg kernel Assumptions.all l g 5 6303
      [(4819, b32 (65536 * laneBase l g)), (4816, b32 (scoreColumn stage))]
      6308 (biasedAddressFacts l g stage) := by
  fin_cases stage <;> intro t ht <;>
    simp only [biasedAddressFacts, scoreColumn, probabilityAddress, probabilityColumn] at ht ⊢ <;>
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

/-- The biased round computes all four TMEM P addresses in nine local instructions. -/
theorem biasedPAddressSegment {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) :
    Seg kernel Assumptions.all l g 9 6299 [(637, .pred (stage.val = 1))]
      6308 (biasedAddressFacts l g stage) :=
  (((biasedStageColumn l g stage).comp (biasedLaneId hp g stage)).comp
    (biasedLaneField hp g stage)).comp (biasedAddressOr l g stage)

private theorem addressCode (i : Fin 9) :
    ∃ ins, kernel.code[6299 + i.val]? = some ins ∧
      Assumptions.coreOp ins.op = true ∧ nextPc ins.op (6299 + i.val) = 6299 + i.val + 1 ∧
      (∀ target, ¬ BrxTarget ins.op target) ∧
      (writesRegs ins.op).all (fun r => decide (4816 ≤ r ∧ r < 4825)) = true := by
  fin_cases i
  · exact ⟨_, Flow.code_6299, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_6300, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_6301, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_6302, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_6303, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_6304, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_6305, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_6306, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_6307, rfl, rfl, fun _ => nofun, by decide⟩

/-- A straight-line Core region preserves every register outside its audited write sets. -/
theorem fixedFrame {l : Launch} {g n first stop : Nat} {t u : TState}
    {kept : Nat → Prop}
    (hCodeAt : ∀ pc, first ≤ pc → pc < stop →
      ∃ ins, kernel.code[pc]? = some ins ∧ Assumptions.coreOp ins.op = true ∧
        nextPc ins.op pc = pc + 1 ∧ (∀ target, ¬ BrxTarget ins.op target) ∧
        ∀ r, kept r → r ∉ writesRegs ins.op)
    (hOff : ∀ pc, first ≤ pc → pc < stop → pc ∉ Assumptions.swExp2Sites)
    (hStart : first ≤ t.pc) (hEnd : t.pc + n ≤ stop)
    (hRun : run kernel Assumptions.all l g n t = some u) :
    ∀ r, kept r → u.regs r = t.regs r := by
  induction n generalizing t with
  | zero =>
    have he : t = u := Option.some.inj hRun
    cases he
    exact fun _ _ => rfl
  | succ n ih =>
    obtain ⟨ins, hCode, hCore, hPC, hNoBrx, hWrites⟩ := hCodeAt t.pc hStart (by omega)
    have hModel := Assumptions.tauStep_all_eq_nil (L := l) (g := g)
      (hOff t.pc hStart (by omega)) hCode hCore
    cases hStep : tauStep kernel [] l g t with
    | none => simp [run, hModel, hStep] at hRun
    | some s =>
      have hTail : run kernel Assumptions.all l g n s = some u := by
        simpa only [run, hModel, hStep, Option.bind_some] using hRun
      have hTau := tauStep_iff.mp hStep
      have hNext : s.pc = t.pc + 1 := by
        rcases tau_core_frame hCode hTau with rfl | hLoc
        · rfl
        · exact hLoc.pc.elim (fun h => h.trans hPC) (fun h => (hNoBrx _ h).elim)
      intro r hr
      exact (ih (by omega) (by omega) hTail r hr).trans (tau_core_regs hCode hTau (hWrites r hr))

/-- This address sequence preserves the packed exponents and all other registers outside
its decoded destination range. -/
theorem biasedPAddressFrame {l : Launch} {g n : Nat} {t u : TState}
    (hStart : 6299 ≤ t.pc) (hEnd : t.pc + n ≤ 6308)
    (hRun : run kernel Assumptions.all l g n t = some u) :
    ∀ r, r < 4816 ∨ 4825 ≤ r → u.regs r = t.regs r := by
  apply fixedFrame (first := 6299) (stop := 6308) _ _ hStart hEnd hRun
  · intro pc hlo hhi
    let i : Fin 9 := ⟨pc - 6299, by omega⟩
    have hi : 6299 + i.val = pc := by dsimp [i]; omega
    obtain ⟨ins, hc, hCore, hPC, hNoBrx, hWrites⟩ := addressCode i
    rw [hi] at hc hPC
    refine ⟨ins, hc, hCore, hPC, hNoBrx, ?_⟩
    intro r hr hm
    have h := of_decide_eq_true (List.all_eq_true.mp hWrites r hm)
    omega
  · intro pc hlo hhi
    simp [Assumptions.swExp2Sites]
    omega

/-- The four temporaries of the main P release's local argument setup. -/
def biasedReleaseScratch : List Nat := [1052, 5096, 5097, 5098]

private theorem biasedReleaseCode (i : Fin 4) :
    ∃ ins, kernel.code[6528 + i.val]? = some ins ∧
      Assumptions.coreOp ins.op = true ∧ nextPc ins.op (6528 + i.val) = 6528 + i.val + 1 ∧
      (∀ target, ¬ BrxTarget ins.op target) ∧
      (writesRegs ins.op).all (· ∈ biasedReleaseScratch) = true := by
  fin_cases i
  · exact ⟨_, Flow.code_6528, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_6529, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_6530, rfl, rfl, fun _ => nofun, by decide⟩
  · exact ⟨_, Flow.code_6531, rfl, rfl, fun _ => nofun, by decide⟩

/-- The biased main P release keeps all registers except its argument temporaries. -/
theorem biasedReleaseFrame {l : Launch} {g n : Nat} {t u : TState}
    (hStart : 6528 ≤ t.pc) (hEnd : t.pc + n ≤ 6532)
    (hRun : run kernel Assumptions.all l g n t = some u) :
    ∀ r ∉ biasedReleaseScratch, u.regs r = t.regs r := by
  apply fixedFrame (first := 6528) (stop := 6532) _ _ hStart hEnd hRun
  · intro pc hlo hhi
    let i : Fin 4 := ⟨pc - 6528, by omega⟩
    have hi : 6528 + i.val = pc := by dsimp [i]; omega
    obtain ⟨ins, hc, hCore, hPC, hNoBrx, hWrites⟩ := biasedReleaseCode i
    rw [hi] at hc hPC
    refine ⟨ins, hc, hCore, hPC, hNoBrx, ?_⟩
    intro r hr hm
    exact hr (of_decide_eq_true (List.all_eq_true.mp hWrites r hm))
  · intro pc hlo hhi
    simp [Assumptions.swExp2Sites]
    omega

end
end PTX.Kernels.TmlFa4Fwd.Softmax
