-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleChunkLoadProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemRescaleChunkInputs
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityWait
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof TcMma Prologue Thread.Correction

/-- After its returned load wait has all warp peers, a lane executes the
local FP32 products and issues the store in its real trace. -/
theorem RescaleLoadIssued.storeOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {stage : Fin 2} {chunk : Fin 8}
    {F : List (Nat × Value)} {c : OpeningTripCursor l X g (rescaleLoadPc stage chunk) F}
    (a : RescaleLoadIssued l X g stage chunk c) (old : Nat → ℝ)
    (hOld : a.values = List.ofFn fun i : Fin 16 => fl (old i.val))
    {word : Value} {alpha : ℝ} (hFactor : RescaleFactorWord word alpha)
    (hAlpha : if chunk.val = 0 then c.ready.regs (statsReg stage .alpha) = some word
      else c.ready.regs (rescaleAlphaPair stage) = some (joinValue word word))
    (hAddr : c.ready.regs (rescaleAddressReg stage chunk) =
      some (b32 (outputAddress l g stage (16*chunk.val))))
    (hFrame : ∀ r ∈ F.map Prod.fst,
      r ∉ rescaleDataRegs stage chunk ∧ rescaleLocalKeeps stage chunk r)
    (hWait : X.get (g,c.pos+1) = some ⟨rescaleLoadPc stage chunk,.tc .waitLd⟩)
    (hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+2))
      (some (setRegs (next c.ready) (rescaleDataRegs stage chunk) a.values)))
    (hTail : Run kernel Assumptions.all l g
      (setRegs (next c.ready) (rescaleDataRegs stage chunk) a.values)
      ((X.tr g).drop (c.pos+2)) c.ending)
    (hPeers : c.pos+2 = (X.tr g).length → ∀ peer ∈ warpLanes l g, ∃ k,
      X.TcK (peer,k) (((X.tr g).take c.pos).countP isTcColl+1)) :
    ∃ u, At u (rescaleStorePc stage chunk+1) ((rescaleAlphaPair stage,joinValue word word)::F) ∧
      X.get (g,c.pos+2) = some ⟨rescaleStorePc stage chunk,.tc (.st
        (outputAddress l g stage (16*chunk.val)) (List.ofFn fun j : Fin 16 => fl (old j.val*alpha))
        .s32x32b)⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+3)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (c.pos+3)) c.ending := by
  obtain ⟨u,hSteps,hu,hAddress,hRegs⟩ := loadedRescaleProductSteps stage chunk old word alpha
    c.checkpoint hAddr hFrame hFactor.width (by rw [hFactor.unpack]; exact hFactor.value)
    (by rw [hFactor.unpack]; exact hFactor.value) hAlpha
  have hOut := rescaleStoreOut hp stage chunk (fun j => fl (old j.val*alpha)) hu hAddress hRegs
    (fun _ => rfl)
  have hRank := countP_take_succ (p := isTcColl) a.issued rfl
  have hReady (hLast : c.pos+2 = (X.tr g).length) : Step.Released l X g :=
    Step.releasedOfTcOrdinal hWait rfl hRank (hPeers hLast) hLast
  rw [hOld] at hPast hTail
  obtain ⟨he,hRecorded,hRemain⟩ := Softmax.probabilityCollectiveOfMaximal hg (Nat.succ_pos _)
    (len_of_get hWait) hOut rfl nofun hPast hSteps hTail (fun h => ⟨X,hMax,rfl,hReady h⟩)
  exact ⟨_,hu.next,hu.1 ▸ he,hRecorded,hRemain⟩

end PTX.Kernels.TmlFa4Fwd.Correction
