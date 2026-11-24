-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleWarpChunkProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionWarpRescaleVisit
import all Kernels.TmlFa4Fwd.Proof.CorrectionRescaleStage
import all Kernels.TmlFa4Fwd.Proof.CorrectionTmemStores
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityWait
import Lemmas.Flow.CountTake
import Lemmas.Step.WarpLanes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof TcMma Prologue Thread.Correction

/-- A warp taking the rescale path performs all eight chunks. Local lane
positions may differ, and every collective advances the shared ordinal. -/
theorem rescaleWarpProductsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {lead rank : Nat} (stage : Fin 2) (F : Nat → List (Nat × Value))
    (coeff : Nat → Value) (alpha : Nat → ℝ)
    (hRegs : ∀ g, SameWarp l lead g → RescaleVisitFrame l g stage (F g))
    (c : ∀ g, SameWarp l lead g → OpeningTripCursor l X g (rescaleLoadPc stage 0) (F g))
    (hInput : ∀ g (hw : SameWarp l lead g),
      ((X.tr g).take (c g hw).pos).countP isTcColl = rank ∧ RescaleFactorWord (coeff g) (alpha g) ∧
      (c g hw).ready.regs (statsReg stage .alpha) = some (coeff g)) :
    ∀ g (hw : SameWarp l lead g),
      ∃ d : OpeningTripCursor l X g (rescaleSignalPc stage) (F g),
        d.pos = (c g hw).pos+25 ∧ ((X.tr g).take d.pos).countP isTcColl = rank+25 := by
  classical
  have walk (n : Nat) (hn : n ≤ 8) : ∀ g (hw : SameWarp l lead g),
      ∃ d : OpeningTripCursor l X g (rescaleStagePc stage n) (F g),
        d.pos = (c g hw).pos+3*n ∧ ((X.tr g).take d.pos).countP isTcColl = rank+3*n ∧
        (if n = 0 then d.ready.regs (statsReg stage .alpha) = some (coeff g)
         else d.ready.regs (rescaleAlphaPair stage) = some (joinValue (coeff g) (coeff g))) := by
    induction n with
    | zero =>
      intro g hw
      exact ⟨c g hw,rfl,(hInput g hw).1,(hInput g hw).2.2⟩
    | succ n ih =>
      let chunk : Fin 8 := ⟨n,by omega⟩
      let start (g : Nat) (hw : SameWarp l lead g) :=
        Classical.choose (ih (by omega) g hw)
      have hSite : rescaleStagePc stage n = rescaleLoadPc stage chunk :=
        dite_eq_left chunk.isLt
      let atLoad (g : Nat) (hw : SameWarp l lead g) : OpeningTripCursor l X g
          (rescaleLoadPc stage chunk) (F g) :=
        let d := start g hw
        ⟨d.pos,d.before,d.ready,d.ending,d.positive,d.bounded,d.released,
          ⟨d.checkpoint.1.trans hSite,d.checkpoint.2⟩,d.recorded,d.remaining,d.localSteps⟩
      have input (g : Nat) (hw : SameWarp l lead g) :=
        Classical.choose_spec (ih (show n ≤ 8 by omega) g hw)
      have run := rescaleWarpChunkOfMaximal hp hMax hFrame (rank := rank+3*n) stage chunk F
        coeff alpha atLoad (fun g hw => by
          have hAddr := (hRegs g hw).accumulator
            (rescaleAddressReg stage chunk,b32 (outputAddress l g stage (16*chunk.val)))
            (List.mem_ofFn.mpr ⟨chunk,rfl⟩)
          exact ⟨(input g hw).2.1,(hInput g hw).2.1,(input g hw).2.2,
            holds_mem (atLoad g hw).checkpoint.2.2.2.2 hAddr,(hRegs g hw).data chunk⟩)
      intro g hw
      obtain ⟨e,hPos,hOrd⟩ := run g hw
      have hEnd := e.checkpoint.mono e.checkpoint.2.2.2.2.2
      refine ⟨⟨e.pos,e.before,e.ready,e.ending,e.positive,e.bounded,e.released,
        ⟨hEnd.1.trans (rescaleStageNext stage chunk),hEnd.2⟩,
        e.recorded,e.remaining,e.localSteps⟩,?_,?_,e.checkpoint.2.2.2.2.1⟩
      · change e.pos = _
        change e.pos = (start g hw).pos+3 at hPos
        have hPrev := (input g hw).1
        change (start g hw).pos = _ at hPrev
        omega
      · change ((X.tr g).take e.pos).countP isTcColl = _
        omega
  let done (g : Nat) (hw : SameWarp l lead g) := Classical.choose (walk 8 (by decide) g hw)
  have hDone (g : Nat) (hw : SameWarp l lead g) := Classical.choose_spec (walk 8 (by decide) g hw)
  have wait (g : Nat) (hw : SameWarp l lead g) :
      let d := done g hw
      X.get (g,d.pos) = some ⟨rescaleStorePc stage 7+1,.tc .waitSt⟩ ∧
        Run kernel Assumptions.all l g {} ((X.tr g).take (d.pos+1)) (some (next d.ready)) ∧
        Run kernel Assumptions.all l g (next d.ready) ((X.tr g).drop (d.pos+1)) d.ending := by
    let d := done g hw
    have ht : At d.ready (rescaleStorePc stage 7+1) (F g) := d.checkpoint
    have hOut : out kernel Assumptions.all l g d.ready = .ev (.tc .waitSt (next d.ready)) := by
      rw [out_event ht.2.2.2.1 (ht.1.symm ▸ finishWaitCode stage) rfl rfl]
      change Out.ev (tcTmpl l g d.ready .tcWaitSt) = _
      have hb : l.block%32 = 0 := by rw [hp.block]
      simp [tcTmpl,hb,ofExec,pure,Except.pure]
    obtain ⟨he,hs,hr⟩ := Softmax.probabilityCollectiveOfMaximal hw.1.2.1 d.positive d.bounded
      hOut rfl nofun d.recorded d.localSteps d.remaining (fun h => ⟨X,hMax,rfl,d.released h⟩)
    exact ⟨by simpa only [ht.1] using he,hs,hr⟩
  have hRank (g : Nat) (hw : SameWarp l lead g) : X.TcK (g,(done g hw).pos) (rank+24) :=
    ⟨⟨_,(wait g hw).1,rfl⟩,(hDone g hw).2.1⟩
  intro g hw
  let d := done g hw
  have hPeers (h : Nat) (hm : h ∈ warpLanes l g) : ∃ k, X.TcK (h,k) (rank+24) := by
    obtain ⟨lane,hl,rfl⟩ := List.mem_map.mp hm
    have hs := Step.sameWarp_lane (by rw [hp.block]) hw.1.2.1
      ((List.mem_range.mp hl).trans_le (min_le_left _ _))
    exact ⟨_,hRank _ (Step.sameWarp_trans hw hs.1)⟩
  obtain ⟨he,hs,hr⟩ := wait g hw
  have hPos : d.pos = (c g hw).pos+24 := (hDone g hw).1
  refine ⟨⟨d.pos+1,next d.ready,next d.ready,d.ending,Nat.succ_pos _,len_of_get he,
    Step.releasedOfTcOrdinal he rfl (hRank g hw).2 hPeers,d.checkpoint.next,hs,hr,.refl⟩,?_,?_⟩
  · change d.pos+1 = _
    omega
  · exact (countP_take_succ (p := isTcColl) he rfl).trans (congrArg (·+1) (hRank g hw).2)

end PTX.Kernels.TmlFa4Fwd.Correction
