-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleChunkProductProgress
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionRescaleVisitObserved
import Kernels.TmlFa4Fwd.Proof.Progress.Async
import Kernels.TmlFa4Fwd.Proof.Safety.MmaOperandCoverage
import Kernels.TmlFa4Fwd.Proof.Protocol.RepeatedProbabilityHistory
import Kernels.TmlFa4Fwd.Proof.Protocol.RescalePublicationValues
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Lemmas.Flow.CountTake
import Lemmas.Step.WarpLanes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof TcMma Prologue Thread.Correction

/-- All warp lanes execute the rescale load, its dataflow wait and the scaled
store. Each boundary uses actual peer operations at the common ordinal. -/
theorem rescaleWarpChunkOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {lead rank : Nat} (stage : Fin 2) (chunk : Fin 8) (F : Nat → List (Nat × Value))
    (coeff : Nat → Value) (alpha : Nat → ℝ)
    (c : ∀ g, SameWarp l lead g → OpeningTripCursor l X g (rescaleLoadPc stage chunk) (F g))
    (hInput : ∀ g (hw : SameWarp l lead g),
      ((X.tr g).take (c g hw).pos).countP isTcColl = rank ∧ RescaleFactorWord (coeff g) (alpha g) ∧
      (if chunk.val = 0 then (c g hw).ready.regs (statsReg stage .alpha) = some (coeff g)
       else (c g hw).ready.regs (rescaleAlphaPair stage) = some (joinValue (coeff g) (coeff g))) ∧
      (c g hw).ready.regs (rescaleAddressReg stage chunk) =
        some (b32 (outputAddress l g stage (16*chunk.val))) ∧
      ∀ r ∈ (F g).map Prod.fst, r ∉ rescaleDataRegs stage chunk ∧ rescaleLocalKeeps stage chunk r) :
    ∀ g (hw : SameWarp l lead g),
      ∃ d : OpeningTripCursor l X g (rescaleStorePc stage chunk+1)
          ((rescaleAlphaPair stage,joinValue (coeff g) (coeff g))::F g),
        d.pos = (c g hw).pos+3 ∧ ((X.tr g).take d.pos).countP isTcColl = rank+3 := by
  classical
  have hCuQ := ((hFrame X hMax.1).metadataProtected hp).1
  have hGuard := Progress.syncGuarded hp hMax.1 hCuQ
  have hLayout := Mma.actualMmaLayoutInjective hMax.1
  have hOperands := Safety.mmaOperandsOfProbabilities hp hMax.1 (hFrame X hMax.1)
    (Protocol.Scores.completedPvProbabilitiesOfExecution hp hMax.1 hFrame)
  have hFinite := Protocol.Statistics.rescaleStoreValuesOfOutputFootprint hp hMax.1 hFrame
  have peerWarp (g : Nat) (hw : SameWarp l lead g) {h} (hm : h ∈ warpLanes l g) :
      SameWarp l lead h := by
    obtain ⟨lane,hl,rfl⟩ := List.mem_map.mp hm
    exact Step.sameWarp_trans hw (Step.sameWarp_lane (by rw [hp.block]) hw.1.2.1
      ((List.mem_range.mp hl).trans_le (min_le_left _ _))).1
  let load (g : Nat) (hw : SameWarp l lead g) := Classical.choice
    (rescaleLoadIssuedOfMaximal hp hMax hGuard hLayout hw.1.2.1 stage chunk
      (c g hw) (hInput g hw).2.2.2.1)
  have loadRank (g : Nat) (hw : SameWarp l lead g) : X.TcK (g,(c g hw).pos) rank :=
    ⟨⟨_,(load g hw).issued,rfl⟩,(hInput g hw).1⟩
  have wait (g : Nat) (hw : SameWarp l lead g) := (load g hw).waitOfMaximal hMax hw.1.2.1
    (fun _ h hm => ⟨_,(hInput g hw).1.symm ▸ loadRank h (peerWarp g hw hm)⟩)
  have waitRank (g : Nat) (hw : SameWarp l lead g) :
      X.TcK (g,(c g hw).pos+1) (rank+1) := by
    refine ⟨⟨_,(wait g hw).1,rfl⟩,?_⟩
    rw [countP_take_succ (p := isTcColl) (load g hw).issued rfl,(hInput g hw).1]
  have product (g : Nat) (hw : SameWarp l lead g) :
      ∃ (old : Nat → ℝ) (u : TState), At u (rescaleStorePc stage chunk+1)
          ((rescaleAlphaPair stage,joinValue (coeff g) (coeff g))::F g) ∧
        X.get (g,(c g hw).pos+2) = some ⟨rescaleStorePc stage chunk,.tc (.st
          (outputAddress l g stage (16*chunk.val)) (List.ofFn fun j : Fin 16 =>
            fl (old j.val*alpha g)) .s32x32b)⟩ ∧
        Run kernel Assumptions.all l g {} ((X.tr g).take ((c g hw).pos+3)) (some u) ∧
        Run kernel Assumptions.all l g u ((X.tr g).drop ((c g hw).pos+3)) (c g hw).ending := by
    obtain ⟨old,hOld⟩ := rescaleLoadValuesAt hp hMax.1 hCuQ hOperands hFinite
      (g := g) (index := (c g hw).pos) stage chunk
    obtain ⟨_,hFactor,hAlpha,hAddr,hRegs⟩ := hInput g hw
    exact ⟨old,(load g hw).storeOfMaximal hp hMax hw.1.2.1 old (hOld _ (load g hw).issued)
      hFactor hAlpha hAddr hRegs (wait g hw).1 (wait g hw).2.1 (wait g hw).2.2 (fun _ h hm =>
        ⟨_,(hInput g hw).1.symm ▸ waitRank h (peerWarp g hw hm)⟩)⟩
  have storeRank (g : Nat) (hw : SameWarp l lead g) : X.TcK (g,(c g hw).pos+2) (rank+2) := by
    obtain ⟨_,_,_,he,_⟩ := product g hw
    refine ⟨⟨_,he,rfl⟩,?_⟩
    rw [countP_take_succ (p := isTcColl) (wait g hw).1 rfl,(waitRank g hw).2]
  intro g hw
  obtain ⟨_,u,hu,he,hPast,hTail⟩ := product g hw
  have hReleased := Step.releasedOfTcOrdinal he rfl (storeRank g hw).2
    (fun h hm => ⟨_,storeRank h (peerWarp g hw hm)⟩)
  refine ⟨⟨(c g hw).pos+3,u,u,(c g hw).ending,Nat.succ_pos _,len_of_get he,hReleased,
    hu,hPast,hTail,.refl⟩,rfl,?_⟩
  exact (countP_take_succ (p := isTcColl) he rfl).trans (congrArg (·+1) (storeRank g hw).2)

end PTX.Kernels.TmlFa4Fwd.Correction
