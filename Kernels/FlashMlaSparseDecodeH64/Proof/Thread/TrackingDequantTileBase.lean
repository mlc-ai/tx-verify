-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRegisterRegion
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2
import Lemmas.Isa.Rule

@[expose] public section

/-! # Concrete dequantization tile bases are independent of cache contents -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The body and epilogue of the dequantizer after entering the ring. -/
def dequantTileRegion (pc : Nat) : Prop := 2667 ≤ pc

instance (pc : Nat) : Decidable (dequantTileRegion pc) :=
  inferInstanceAs (Decidable (2667 ≤ pc))

set_option maxRecDepth 100000 in
theorem dequant_tile_region_closed : controlRegionClosed dequantTileRegion = true := by
  decide +kernel

private def dstRegion (pc : Nat) : Bool := decide (2667 ≤ pc ∧ pc ≤ 3607)
private def symRegion (pc : Nat) : Bool := decide (2673 ≤ pc ∧ pc ≤ 2692)
private def oneRegion (pc : Nat) : Bool := pc == 2692
private def choiceRegion (pc : Nat) : Bool := pc == 2693

/-- The base of the first chunk is live across all the stores in the current body. -/
def dequantBaseRegion (pc : Nat) : Bool := decide (2694 ≤ pc ∧ pc ≤ 3594)

set_option maxRecDepth 100000 in
private theorem dst_audit : registerRegionChecked 516 dstRegion [2666] = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem sym_audit : registerRegionChecked 2787 symRegion [2672] = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem one_audit : registerRegionChecked 2794 oneRegion [2691] = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem choice_audit : registerRegionChecked 2795 choiceRegion [2692] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem base_audit : registerRegionChecked 2472 dequantBaseRegion [2693] = true := by
  decide +kernel

/-- Address facts of the actual dequantizer. The selected tile may be either ring slot. -/
structure DequantTileBase (L : Launch) (g : Nat) (t : TState) : Prop where
  region : dequantTileRegion t.pc
  dst : decide (2667 ≤ t.pc ∧ t.pc ≤ 3607) = true → t.regs 516 = some (b32 (Wg2.dstOff L g))
  symbol : decide (2673 ≤ t.pc ∧ t.pc ≤ 2692) = true → t.regs 2787 = some (b32 L.sharedBase)
  second : (t.pc == 2692) = true → t.regs 2794 = some (b32 (L.sharedBase + 65536))
  selected : (t.pc == 2693) = true → ∃ b : Fin 2,
    t.regs 2795 = some (b32 (L.sharedBase + Wg2.tileBase b.val))
  chunk : dequantBaseRegion t.pc = true → ∃ b : Fin 2,
    t.regs 2472 = some (b32 (L.sharedBase + Wg2.tileBase b.val + Wg2.dstOff L g))

private def chooseTile : IntInstr :=
  ⟨.selp, .int .b 32, false, [some 2795], [.reg 2787, .reg 2794, .reg 135]⟩

private theorem select_tile_from_tau {t u : TState} (hPc : t.pc = 2692)
    (hBase : t.regs 2787 = some (b32 L.sharedBase))
    (hSecond : t.regs 2794 = some (b32 (L.sharedBase + 65536)))
    (hTau : Tau kernel Assumptions.all L g t u) :
    ∃ b : Fin 2, u.regs 2795 = some (b32 (L.sharedBase + Wg2.tileBase b.val)) := by
  have hRules := Thread.asms_localRule_int (L := L) (g := g) (t := t) (i := chooseTile)
    (by rw [hPc]; decide) (by rw [hPc]; decide) (by rw [hPc]; decide) rfl
  have hCode : kernel.code[t.pc]? = some ⟨none, .int chooseTile⟩ := hPc ▸ Flow.code_2692
  have hf := tau_fault_free hTau
  have hOut : out kernel Assumptions.all L g t =
      match execMove L g t (.int chooseTile) with
      | .ok v => Out.tau v
      | .error f => Out.ev (.ub f) := by
    have hExec : execLocalA Assumptions.all L g t (.int chooseTile) =
        execMove L g t (.int chooseTile) := by
      rw [execLocalA_noSegment (Proof.asms_segment_free t), execLocalRule_of_none hRules,
        execLocal_selp rfl]
    unfold out
    rw [hf, hCode]
    change (match execLocalA Assumptions.all L g t (.int chooseTile) with
      | .ok v => Out.tau v
      | .error f => Out.ev (.ub f)) = _
    rw [hExec]
  unfold Tau at hTau
  rw [hOut] at hTau
  cases hPick : t.regs 135 with
  | none =>
    simp only [chooseTile, execMove, readReg, hPick] at hTau
    cases hTau
  | some pick =>
    cases pick with
    | pred b =>
      cases b with
      | false =>
        simp [chooseTile, execMove, hPick, hSecond, readValue, readReg, b32,
          DType.width, Value.bytes] at hTau
        obtain rfl := Out.tau.inj hTau
        exact ⟨1, rfl⟩
      | true =>
        simp [chooseTile, execMove, hPick, hBase, readValue, readReg, b32,
          DType.width, Value.bytes] at hTau
        obtain rfl := Out.tau.inj hTau
        exact ⟨0, rfl⟩
    | _ => simp [chooseTile, execMove, readReg, hPick] at hTau

/-- Local execution preserves the tile-address facts, recomputing the base on loop entry. -/
theorem dequant_tile_base_tau {t u : TState}
    (hpre : Pre P L mem0) (hOld : DequantTileBase L g t)
    (hTau : Tau kernel Assumptions.all L g t u) : DequantTileBase L g u := by
  have hf := tau_fault_free hTau
  have hs := sharedBase_lt hpre
  refine ⟨control_region_tau dequant_tile_region_closed hOld.region hTau,
    register_region_tau (property := fun v => v = some (b32 (Wg2.dstOff L g)))
      dst_audit hOld.dst ?_ hTau,
    register_region_tau (property := fun v => v = some (b32 L.sharedBase))
      sym_audit hOld.symbol ?_ hTau,
    register_region_tau (property := fun v => v = some (b32 (L.sharedBase + 65536)))
      one_audit hOld.second ?_ hTau,
    register_region_tau
      (property := fun v => ∃ b : Fin 2, v = some (b32 (L.sharedBase + Wg2.tileBase b.val)))
      choice_audit hOld.selected ?_ hTau,
    register_region_tau (property := fun v => ∃ b : Fin 2,
      v = some (b32 (L.sharedBase + Wg2.tileBase b.val + Wg2.dstOff L g)))
      base_audit hOld.chunk ?_ hTau⟩
  · intro hp _
    have hPc : t.pc = 2666 := List.mem_singleton.mp hp
    have hRegion := hOld.region
    change 2667 ≤ t.pc at hRegion
    omega
  · intro hp _
    have hPc : t.pc = 2672 := List.mem_singleton.mp hp
    have ha : AtVector t 2672 [] t.sub t.acc := ⟨hPc, rfl, rfl, hf, trivial⟩
    obtain ⟨v, hRun, hAt⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
        AtVector v 2673 [(2787, b32 L.sharedBase)] t.sub t.acc := by
      seg_fp ha using
        (try unfold b32)
        (try norm_bits [Nat.add_zero])
    exact (one_step_matches hTau hRun) ▸ hAt.2.2.2.2.1
  · intro hp _
    have hPc : t.pc = 2691 := List.mem_singleton.mp hp
    have ha : AtVector t 2691 [(2787, b32 L.sharedBase)] t.sub t.acc :=
      ⟨hPc, rfl, rfl, hf, hOld.symbol (by rw [hPc]; decide), trivial⟩
    obtain ⟨v, hRun, hAt⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
        AtVector v 2692 [(2794, b32 (L.sharedBase + 65536))] t.sub t.acc := by
      seg_fp ha using
        (try unfold b32)
        (try norm_bits [Nat.add_zero])
    exact (one_step_matches hTau hRun) ▸ hAt.2.2.2.2.1
  · intro hp _
    have hPc : t.pc = 2692 := List.mem_singleton.mp hp
    exact select_tile_from_tau hPc (hOld.symbol (by rw [hPc]; decide))
      (hOld.second (by rw [hPc]; decide)) hTau
  · intro hp _
    have hPc : t.pc = 2693 := List.mem_singleton.mp hp
    obtain ⟨b, hb⟩ := hOld.selected (by rw [hPc]; decide)
    have ha : AtVector t 2693
        [(516, b32 (Wg2.dstOff L g)), (2795, b32 (L.sharedBase + Wg2.tileBase b.val))]
        t.sub t.acc := ⟨hPc, rfl, rfl, hf, hOld.dst (by rw [hPc]; decide), hb, trivial⟩
    have hDst := Wg2.dstOff_lt L g
    have hbLt := b.isLt
    have hbBound : Wg2.tileBase b.val ≤ 65536 := by
      unfold Wg2.tileBase Wg2.dequantBytes
      omega
    obtain ⟨v, hRun, hAt⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
        AtVector v 2694 [(2472, b32 (L.sharedBase + Wg2.tileBase b.val + Wg2.dstOff L g))]
          t.sub t.acc := by
      seg_fp ha using
        (try unfold b32)
        (try norm_bits [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc])
    exact ⟨b, (one_step_matches hTau hRun) ▸ hAt.2.2.2.2.1⟩

/-- The dequantizer's memory and barrier callbacks leave the address registers intact. -/
theorem dequant_tile_base_event {t u : TState} {e : Event}
    (hOld : DequantTileBase L g t) (he : EStep kernel Assumptions.all L g t e (some u)) :
    DequantTileBase L g u := by
  refine ⟨control_region_event dequant_tile_region_closed hOld.region he,
    register_region_event (property := fun v => v = some (b32 (Wg2.dstOff L g)))
      dst_audit (register_updates_local (by decide +kernel)) hOld.dst he,
    register_region_event (property := fun v => v = some (b32 L.sharedBase))
      sym_audit (register_updates_local (by decide +kernel)) hOld.symbol he,
    register_region_event (property := fun v => v = some (b32 (L.sharedBase + 65536)))
      one_audit (register_updates_local (by decide +kernel)) hOld.second he,
    register_region_event
      (property := fun v => ∃ b : Fin 2, v = some (b32 (L.sharedBase + Wg2.tileBase b.val)))
      choice_audit (register_updates_local (by decide +kernel)) hOld.selected he,
    register_region_event (property := fun v => ∃ b : Fin 2,
      v = some (b32 (L.sharedBase + Wg2.tileBase b.val + Wg2.dstOff L g)))
      base_audit (register_updates_local (by decide +kernel)) hOld.chunk he⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
