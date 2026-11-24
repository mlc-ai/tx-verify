-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.DequantOperandReadback
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmSums
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.DequantAfterPv
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.StageAfterPv
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryOperandLifetime
import Lemmas.Tcgen05.MmaObservedReads

@[expose] public section

/-! # The actual shared B snapshots of QK and PV -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow AsyncCopy Protocol MmaDataTrace MachineTracking

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem actual_kv_byte
    {g i index dest : Nat} {d : Wg1Mma.D} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {ops : MmaOperands}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : (∃ k, d.site = .qkMma k) ∨ ∃ k, d.site = .pvMma k)
    (hi : X.MmaIssue (g, i) dest s acc mask) (hops : X.async.mmaOperands (g, i) = some ops)
    (slot : Fin 64) (feature : Fin 512) (b : Fin 2)
    (hl : s.byteLoc .b index = some (kvOperandLoc L (ctaOf L g) d.i slot feature b))
    (stage : ∀ {w j : Nat} {a : Acc} {bs : List Byte} {v : Option Byte},
      X.MmaRead (g, i) true index (kvOperandLoc L (ctaOf L g) d.i slot feature b) v →
      EpiloguePvHistory P L X w j → ctaOf L w = ctaOf L g → X.Writes (w, j) a bs →
      a.Covers (kvOperandLoc L (ctaOf L g) d.i slot feature b) →
      ByteCausality L X (kvOperandLoc L (ctaOf L g) d.i slot feature b)
        (.async (g, i) (.mmaRead true index)) (.thread (w, j))) :
    ops.b[index]? = some (some (.float .bf16
      (dequant (Wg2.gatheredByte P L g d.i slot.val) feature.val), b.val)) := by
  let cta := ctaOf L g
  let l := kvOperandLoc L cta d.i slot feature b
  obtain ⟨v, hRead, hGet⟩ := hX.mma_read_exists hi hops (isB := true) hl
  have hh := fun t ht => (hs t ht).machine
  obtain ⟨issuer, hIssuer⟩ := GemmRing.exists_issuer (cta := cta) hpre hX hh
  have hSelf : g = issuer := hIssuer g i d rfl hd (by
    rcases hsite with ⟨k, hk⟩ | ⟨k, hk⟩ <;> simp [hk])
  subst issuer
  have hretire : KvOperandRetirement P L X (g, i) index d.i l := by
    constructor
    · intro w j dq r step a bs hSt hSite hBlock hPhase hCta hw hCov
      change ctaOf L w = cta at hCta
      have hwLt := Frame.lt_of_get hX hw.choose_spec
      have hwg := RingRoleGeometry.of_trace hX hwLt (hh w hwLt) hSt
      obtain ⟨lane, hLane⟩ := RawRing.consumer_of_wg2 hpre hCta hwg
      subst w
      obtain ⟨_, wait, hLt, hFinish, hBefore⟩ :=
        DequantAfterPv.earlier_b_read_completed hpre hX hh hIssuer rfl hRead hd hsite
          hBlock hPhase.symm hw.choose_spec hSt ⟨r, step, hSite⟩
      exact completed_mma_source_before_store hi hRead.1 hFinish rfl hLt hBefore rfl hw hCov
    · exact fun hHistory hCta hw hCov => stage hRead hHistory hCta hw hCov
  have hDequant : Wg1MmaGemmTrace.completed .dequant d.site = true := by
    rcases hsite with ⟨k, hk⟩ | ⟨k, hk⟩ <;> rw [hk] <;> rfl
  have hValue := dequant_operand_readback hpre hX hs hIssuer rfl hi.choose_spec
    hd hDequant slot feature b hRead hretire
  change ops.b[index]? = some v at hGet
  rw [hGet, hValue]

/-- The observed QK B row contains the exact dequantized key features for its sparse slot. -/
theorem qk_key_operand {g i : Nat} {d : Wg1Mma.D} {issue : Fin 16} {ops : MmaOperands}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .qkMma issue)
    (hi : X.MmaIssue (g, i) Wg1Mma.tmemP (qkOperands L g d.i issue)
      (qkAccum issue) [0, 0, 0, 0])
    (hops : X.async.mmaOperands (g, i) = some ops) (col : Fin 128) :
    Bf16Operand ops.b col.val fun k =>
      dequant (Wg2.gatheredByte P L g d.i (col.val % 64)) (qkDepthAt col issue.val k) := by
  intro k hk b hb
  let depth : Fin 16 := ⟨k, hk⟩
  let sub : Fin 2 := ⟨b, hb⟩
  let slot : Fin 64 := ⟨col.val % 64, by omega⟩
  let feature : Fin 512 := ⟨qkFeature issue col depth, by
    have hi := issue.isLt
    have hc := col.isLt
    dsimp [qkFeature, depth]
    omega⟩
  refine actual_kv_byte hpre hX hs hd (.inl ⟨issue, hsite⟩) hi hops slot feature sub
    (qkKeyByte L g d.i issue col depth sub) ?_
  intro w j a bs v hRead hHistory hCta hw hCov
  obtain ⟨wait, hLt, scope, hObs, hScopes, hPath⟩ :=
    QueryOperandLifetime.qk_completion_before_endpoint hpre hX hs hi hd hsite
      hw.choose_spec hCta.symm hHistory.softmax hHistory.qk.counts
  exact completed_mma_source_before_store hi hRead.1 (.inr ⟨scope, hObs, hScopes⟩)
    rfl hLt hPath rfl hw hCov

/-- The observed PV B row contains the exact dequantized value features for its sparse slots. -/
theorem pv_value_operand {g i : Nat} {d : Wg1Mma.D} {issue : Fin 8} {ops : MmaOperands}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue)
    (hi : X.MmaIssue (g, i) (Wg1Mma.pvDest issue) (pvOperands L g d.i issue)
      (pvAccum d.i issue) [0, 0, 0, 0])
    (hops : X.async.mmaOperands (g, i) = some ops) (col : Fin 256) :
    Bf16Operand ops.b col.val fun k =>
      dequant (Wg2.gatheredByte P L g d.i (16 * (issue.val / 2) + k)) (pvFeature issue col) := by
  intro k hk b hb
  let depth : Fin 16 := ⟨k, hk⟩
  let sub : Fin 2 := ⟨b, hb⟩
  let slot : Fin 64 := ⟨pvSlot issue depth, by
    have hi := issue.isLt
    dsimp [pvSlot, depth]
    omega⟩
  let feature : Fin 512 := ⟨pvFeature issue col, by
    have hc := col.isLt
    dsimp [pvFeature]
    omega⟩
  refine actual_kv_byte hpre hX hs hd (.inr ⟨issue, hsite⟩) hi hops slot feature sub
    (pvValueByte L g d.i issue col depth sub) ?_
  intro w j a bs v hRead hHistory hCta hw hCov
  obtain ⟨issuer, hIssuer⟩ :=
    GemmRing.exists_issuer (cta := ctaOf L w) hpre hX (fun t ht => (hs t ht).machine)
  have hSelf := hIssuer g i d hCta.symm hd (by simp [hsite])
  subst issuer
  obtain ⟨_, wait, hLt, hFinish, hBefore, _⟩ :=
    StageAfterPv.actual_operand_completed (isB := true) (index := _)
      hpre hX hs hIssuer hCta.symm (.inl ⟨_, _, _, _, hi⟩) hd
      (.inr ⟨issue, hsite⟩) hw.choose_spec hHistory
  exact completed_mma_source_before_store hi hRead.1 hFinish rfl hLt hBefore rfl hw hCov

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
