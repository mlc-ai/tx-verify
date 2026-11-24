-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasRendezvous
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstBiasTrace
import Kernels.TmlFa4Fwd.Flow.Code.Part056
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

private def biasScaleLoad (index dst : Nat) : Op := .mem {
  kind := .load
  space := some .param
  sem := .weak
  elem := .int .b 32
  addr := ⟨.param (param index) false, 0⟩
  dsts := [some dst] }

private theorem biasInvCode : kernel.code[3591]? = some ⟨none, biasScaleLoad 14 7135⟩ := by
  have hName : param 14 =
      "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_obje\
      ct_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf\
      16gmemalign16o1i64div8_0_param_14" := by
    unfold param
    decide +kernel
  rw [Flow.code_3591, biasScaleLoad, hName]

private theorem biasScaleCode : kernel.code[3592]? = some ⟨none, biasScaleLoad 12 7132⟩ := by
  have hName : param 12 =
      "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_obje\
      ct_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf\
      16gmemalign16o1i64div8_0_param_12" := by
    unfold param
    decide +kernel
  rw [Flow.code_3592, biasScaleLoad, hName]

/-- After the Bias release, the lane reads both ABI scale words before the first FMA. All
already-loaded score and Bias operands survive the two parameter reads. -/
theorem firstBiasFmaScaleLoads {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (ht : At t 3591 []) :
    ∃ u, At u 3593 [(7135, b32 p.invScaleBits), (7132, b32 p.scaleLog2Bits)] ∧
      run kernel Assumptions.all l g 2 t = some u ∧
      ∀ r, r ≠ 7135 → r ≠ 7132 → u.regs r = t.regs r := by
  obtain ⟨hInvBits, hInv⟩ := hp.values (14, p.invScaleBits) (by simp [Params.scalarWords])
  obtain ⟨hScaleBits, hScale⟩ := hp.values (12, p.scaleLog2Bits) (by simp [Params.scalarWords])
  let v := next (setReg t 7135 (b32 p.invScaleBits))
  have hvRun : run kernel Assumptions.all l g 1 t = some v := by
    apply run_local biasInvCode rfl ht
    rw [Assumptions.execLocalA_all_eq_numeric,
      Assumptions.execLocalA_eq_nil (by rw [ht.1]; decide) rfl, execLocalA_nil, biasScaleLoad,
      execLocal_mem rfl]
    change (match l.params (param 14) with
      | some x => Except.ok (next (setReg t 7135 (MemExt.same.extendBits 32 x)))
      | none => Except.error Fault.badParam) = _
    rw [hInv]
    change Except.ok (next (setReg t 7135
      (.bits 32 (truncBits 32 (BitVec.ofNat 64 p.invScaleBits))))) = _
    rw [truncBits_ofNat hInvBits (by decide)]
    rfl
  have hv : At v 3592 [(7135, b32 p.invScaleBits)] := ht.set (by simp)
  let u := next (setReg v 7132 (b32 p.scaleLog2Bits))
  have huRun : run kernel Assumptions.all l g 1 v = some u := by
    apply run_local biasScaleCode rfl hv
    rw [Assumptions.execLocalA_all_eq_numeric,
      Assumptions.execLocalA_eq_nil (by rw [hv.1]; decide) rfl, execLocalA_nil, biasScaleLoad,
      execLocal_mem rfl]
    change (match l.params (param 12) with
      | some x => Except.ok (next (setReg v 7132 (MemExt.same.extendBits 32 x)))
      | none => Except.error Fault.badParam) = _
    rw [hScale]
    change Except.ok (next (setReg v 7132
      (.bits 32 (truncBits 32 (BitVec.ofNat 64 p.scaleLog2Bits))))) = _
    rw [truncBits_ofNat hScaleBits (by decide)]
    rfl
  have hu : At u 3593 [(7132, b32 p.scaleLog2Bits), (7135, b32 p.invScaleBits)] :=
    hv.set (by simp)
  refine ⟨u, hu.mono ⟨hu.2.2.2.2.2.1, hu.2.2.2.2.1, trivial⟩, run_comp hvRun huRun, ?_⟩
  intro r hInv hScale
  simp only [u, v, next, setReg, Function.update_of_ne hInv, Function.update_of_ne hScale]

/-- Registers written between the first Bias fence and the first affine instruction. -/
def firstBiasEntryWritten : List Nat := 7135 :: 7132 :: biasFenceWritten false

/-- The actual first Bias release and scale reads lead to the first affine instruction
with the unpacked Bias data and score packs preserved on the same trace. -/
theorem firstBiasFmaEntryTrace {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j : Nat} {t : TState}
    (ht : At t 3581 (biasFenceFacts l g warp false))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let pos := if laneOf l g = 0 then j + 3 else j + 2
    ∃ u, X.get (g, j) = some ⟨3581, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      X.get (g, j + 1) = some ⟨3583, .bar (11 + (stageOf warp).val) (some 128) .sync⟩ ∧
      (laneOf l g = 0 → X.get (g, j + 2) = some
        ⟨3590, .arrive (signalLoc l g (stageOf warp) 0) 0 1 true .cta⟩) ∧
      At u 3593 [(7135, b32 p.invScaleBits), (7132, b32 p.scaleLog2Bits)] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) none ∧
      ∀ r ∉ firstBiasEntryWritten, u.regs r = t.regs r := by
  obtain ⟨v, hFence, hBar, hRelease, hv, hvRun, hFrame⟩ :=
    biasFinishTraceFramed hp warp false ht hRun
  have hvScale : At v 3591 [] := hv.mono trivial
  obtain ⟨u, hu, huLocal, hKeep⟩ := firstBiasFmaScaleLoads (g := g) hp hvScale
  refine ⟨u, hFence, hBar, hRelease, hu, hvRun.after_local (run_rtg huLocal), ?_⟩
  intro r hReg
  simp only [firstBiasEntryWritten, List.mem_cons, not_or] at hReg
  exact (hKeep r hReg.1 hReg.2.1).trans (hFrame r hReg.2.2)

private theorem firstBiasEntryItems :
    (biasBodyItems false).all (fun item =>
      [item.biasLow, item.biasHigh, item.qk].all (fun r => !firstBiasEntryWritten.contains r)) =
      true := by
  kernel_rfl

/-- At the actual post-read fence, the observed score and Bias operands are enough to
start the numerical round at its first publication index. -/
theorem firstRoundFromBiasFence {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j batch head base blocks biasCap pastTile : Nat}
    {t : TState} (bias : Nat → Option ℝ) (qk : Nat → ℝ × ℝ) (hb : batch < p.batch)
    (hRow : 128 * base + (g % l.block) % 128 < p.qLength batch + 256)
    (hBlocks : 128 * (blocks - 1) ≤ p.kLength batch)
    (ht : At t 3581 (biasFenceFacts l g warp false))
    (hGeometry : Holds t.regs
      [(1229, b32 (blocks-1)), (1224, b32 (p.kLength batch)),
        (2868, b32 (128 * base)), (1223, maskSigned (-(p.qLength batch : Int)))])
    (hLo : t.regs 793 = some (biasValue (bias 793)))
    (hHi : t.regs 792 = some (biasValue (bias 792)))
    (hDot : readERealPair l g t (.reg 7303) =
      some (.ok (((qk 7303).1 : ℝ), ((qk 7303).2 : ℝ))))
    (hInputs : ∀ i ∈ biasBodyItems false,
      t.regs i.biasLow = some (biasValue (bias i.biasLow)) ∧
      t.regs i.biasHigh = some (biasValue (bias i.biasHigh)) ∧
      readERealPair l g t (.reg i.qk) = some (.ok (((qk i.qk).1 : ℝ), ((qk i.qk).2 : ℝ))))
    (hLive : ∀ col < 128,
      let row := 128 * base + (g % l.block) % 128
      visitKey blocks 0 col < p.keyCount batch row →
      firstBiasLogit (abiFloat p.invScaleBits) bias qk col =
        some (score p batch head row (visitKey blocks 0 col) / abiFloat p.scaleLog2Bits))
    (hLoop : Holds t.regs (firstLoopGeometry blocks biasCap pastTile))
    (hBar : t.regs 5127 = some (b32 (3 + warp.val)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let pos := if laneOf l g = 0 then j + 3 else j + 2
    X.get (g, j) = some ⟨3581, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      X.get (g, j + 1) = some ⟨3583, .bar (11 + (stageOf warp).val) (some 128) .sync⟩ ∧
      (laneOf l g = 0 → X.get (g, j + 2) = some
        ⟨3590, .arrive (signalLoc l g (stageOf warp) 0) 0 1 true .cta⟩) ∧
      FirstRoundProgress p l X warp g pos batch head (128 * base + (g % l.block) % 128)
        blocks biasCap pastTile := by
  obtain ⟨u, hFence, hRendezvous, hRelease, hu, huRun, hFrame⟩ :=
    firstBiasFmaEntryTrace hp warp ht hr
  have huGeometry : At u 3593
      [(1229, b32 (blocks-1)), (1224, b32 (p.kLength batch)),
        (2868, b32 (128 * base)), (1223, maskSigned (-(p.qLength batch : Int)))] :=
    hu.mono ⟨(hFrame _ (by decide)).trans hGeometry.1,
      (hFrame _ (by decide)).trans hGeometry.2.1, (hFrame _ (by decide)).trans hGeometry.2.2.1,
      (hFrame _ (by decide)).trans hGeometry.2.2.2.1, trivial⟩
  have huLoop : Holds u.regs (firstLoopGeometry blocks biasCap pastTile) :=
    ⟨(hFrame _ (by decide)).trans hLoop.1, (hFrame _ (by decide)).trans hLoop.2.1,
      (hFrame _ (by decide)).trans hLoop.2.2.1, (hFrame _ (by decide)).trans hLoop.2.2.2.1,
      trivial⟩
  have huTail : Holds u.regs (tailFrame l warp) :=
    ⟨(hFrame _ (by decide)).trans ht.2.2.2.2.2.2.1,
      (hFrame _ (by decide)).trans ht.2.2.2.2.2.2.2.1, trivial⟩
  have hPacked (r : Nat) (hR : r ∉ firstBiasEntryWritten) :
      readERealPair l g u (.reg r) = readERealPair l g t (.reg r) := by
    simp only [readERealPair, readValue, readReg, hFrame r hR]
  refine ⟨hFence, hRendezvous, hRelease, firstRoundFromBiasReady hp warp bias qk hb
    hRow hBlocks huGeometry ((hFrame _ (by decide)).trans hLo) ((hFrame _ (by decide)).trans hHi)
    hu.2.2.2.2.1 ((hPacked _ (by decide)).trans hDot) ?_ hLive huLoop huTail hu.2.2.2.2.2.1
    ((hFrame _ (by decide)).trans hBar) huRun⟩
  intro i hi
  obtain ⟨hL, hH, hQ⟩ := hInputs i hi
  have hKeep (r : Nat) (hr : r ∈ [i.biasLow, i.biasHigh, i.qk]) : r ∉ firstBiasEntryWritten := by
    simpa using List.all_eq_true.mp (List.all_eq_true.mp firstBiasEntryItems i hi) r hr
  exact ⟨(hFrame _ (hKeep _ (by simp))).trans hL, (hFrame _ (hKeep _ (by simp))).trans hH,
    (hPacked _ (hKeep _ (by simp))).trans hQ⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
