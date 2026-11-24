-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionAccumulatorLoadProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleNumerics
import all Kernels.TmlFa4Fwd.Proof.CorrectionTmemLoads
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityWait
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Proof.Safety.TmemWordSizes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.TcMma Prologue

/-- The rescale load has issued its sixteen real words and retained the
pending dataflow wait at the same instruction. -/
structure RescaleLoadIssued (l : Launch) (X : Execution) (g : Nat)
    (stage : Fin 2) (chunk : Fin 8) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (rescaleLoadPc stage chunk) F) where
  values : List Value
  size : values.length = 16
  issued : X.get (g,c.pos) = some ⟨rescaleLoadPc stage chunk,
    .tc (.ld (outputAddress l g stage (16*chunk.val)) values .s32x32b)⟩
  recorded : Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1))
    (some {setRegs (next c.ready) (rescaleDataRegs stage chunk) values with
      pc := c.ready.pc,sub := 1})
  remaining : Run kernel Assumptions.all l g
    {setRegs (next c.ready) (rescaleDataRegs stage chunk) values with pc := c.ready.pc,sub := 1}
    ((X.tr g).drop (c.pos+1)) c.ending

/-- Every correction lane that reaches the load and is released at that
boundary issues its actual rescale load. -/
theorem rescaleLoadIssuedOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : SyncGuarded l kernel X) (hLayout : LayoutInjective X)
    {g : Nat} (hg : g < l.threads) (stage : Fin 2) (chunk : Fin 8)
    {F : List (Nat × Value)} (c : OpeningTripCursor l X g (rescaleLoadPc stage chunk) F)
    (hAddr : c.ready.regs (rescaleAddressReg stage chunk) =
      some (b32 (outputAddress l g stage (16*chunk.val)))) :
    Nonempty (RescaleLoadIssued l X g stage chunk c) := by
  have hCode := rescaleRegisterCode stage chunk
  have hLen : (rescaleDataRegs stage chunk).length = 16 := List.length_ofFn
  have hOut := outputLoadTemplate hp stage (by have := chunk.isLt; omega : 16*chunk.val < 128)
    c.checkpoint.1 c.checkpoint.2.1 c.checkpoint.2.2.2.1 hCode hLen (by decide)
    (rescaleWaitHook stage chunk) hAddr
  obtain ⟨words,hSize,he,hPast,hTail⟩ := Step.tcLoadOfMaximal hMax hGuard hLayout hg c.positive
    c.bounded c.released c.recorded c.remaining c.localSteps hOut
    (fun _ _ _ ⟨_,hWrite,_⟩ => Safety.tensorWroteWordBytes hp hMax.1 hWrite)
    (Assumptions.wfStep _ _ hMax.1 le_snoc (Execution.notifiedInOrder_of_eq rfl)
      (Execution.noNewRead_snoc rfl))
  exact ⟨⟨words,hSize,by simpa only [c.checkpoint.1] using he,hPast,hTail⟩⟩

/-- A rescale load whose warp peers have issued can take its pending load wait. -/
theorem RescaleLoadIssued.waitOfMaximal {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    {stage : Fin 2} {chunk : Fin 8} {F : List (Nat × Value)}
    {c : OpeningTripCursor l X g (rescaleLoadPc stage chunk) F} (a : RescaleLoadIssued l X g
      stage chunk c)
    (hPeers : c.pos+1 = (X.tr g).length → ∀ peer ∈ warpLanes l g, ∃ k,
      X.TcK (peer,k) (((X.tr g).take c.pos).countP isTcColl)) :
    let u := setRegs (next c.ready) (rescaleDataRegs stage chunk) a.values
    X.get (g,c.pos+1) = some ⟨rescaleLoadPc stage chunk,.tc .waitLd⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+2)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (c.pos+2)) c.ending := by
  let u := setRegs (next c.ready) (rescaleDataRegs stage chunk) a.values
  let s := {u with pc := c.ready.pc,sub := 1}
  have hSkel := setRegs_skel (next c.ready) (rescaleDataRegs stage chunk) a.values
  have hs : s.pc = rescaleLoadPc stage chunk := c.checkpoint.1
  have hf : s.fault = none := hSkel.2.2.2.trans c.checkpoint.2.2.2.1
  have hPending : out kernel Assumptions.all l g s = .ev (.tc .waitLd u) := by
    rw [out_event hf (hs.symm ▸ rescaleRegisterCode stage chunk) rfl rfl]
    change Out.ev (tcLdTmpl Assumptions.all l g s _) = _
    have hHook := hs.symm ▸ rescaleWaitHook stage chunk
    simp only [tcLdTmpl,hHook,show s.sub ≠ 0 from Nat.one_ne_zero,↓reduceIte]
    exact congrArg (fun state => Out.ev (.tc .waitLd state))
      (resumeLoad hSkel.1 (hSkel.2.1.trans c.checkpoint.2.1))
  obtain ⟨he,hPast,hTail⟩ := Softmax.probabilityCollectiveOfMaximal hg (Nat.succ_pos _)
    (len_of_get a.issued) hPending rfl nofun a.recorded .refl a.remaining (fun h =>
      ⟨X,hMax,rfl,Step.releasedOfTcOrdinal a.issued rfl rfl (hPeers h) h⟩)
  exact ⟨by simpa only [hs] using he,hPast,hTail⟩

end PTX.Kernels.TmlFa4Fwd.Correction
