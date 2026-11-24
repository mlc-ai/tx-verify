-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstBiasAddresses
import Kernels.TmlFa4Fwd.Proof.SoftmaxGroupCoordinates
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Lemmas.Step.ExitLast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Epilogue Prologue

private theorem firstVisitCarryRegs (l : Launch) (g : Nat) (warp : Fin 8) :
    ∀ x ∈ singleVisitGeometryCarry l g warp, x.1 ∈ firstGeometryCarryRegs := by
  have hRegs : ((singleVisitGeometryCarry l g warp).map Prod.fst).all
      (fun r => firstGeometryCarryRegs.contains r) = true := rfl
  intro x hx
  have h := List.all_eq_true.mp hRegs x.1 (List.mem_map_of_mem hx)
  simpa only [List.contains_eq_mem,decide_eq_true_eq] using h

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    (hFootprint : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads)
    (hWarp : warpIndex l g < 8) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
include hp hX hComplete hFootprint hg hWarp hb hLo

/-- A complete selected lane records its actual bias-ready wait before the first score round. -/
theorem firstVisitGeometryTraceOfComplete (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
    let stage := stageOf warp
    let tile := (assignedCoordinates p batch (g/l.block)).1
    ∃ (atMetadata fails : Nat) (u : TState), FirstGeometryReads p X g atMetadata batch ∧
      (X.tr g).drop (atMetadata+3) =
        List.replicate fails ⟨3420,.wait (waitLoc l g stage 0) 1 false true .cta⟩ ++
          ⟨3420,.wait (waitLoc l g stage 0) 1 true true .cta⟩ ::
            (X.tr g).drop (atMetadata+3+fails+1) ∧
      At u 3425 ([(1229,b32 (Mma.trips p batch tile-1)),(2770,b32 0)] ++
        firstGeometryAckFacts p l g batch tile stage ++ singleVisitGeometryCarry l g warp) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (atMetadata+3+fails+1)) none := by
  let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
  let stage := stageOf warp
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g lane = g :=
    Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  obtain ⟨finish,⟨site,kind⟩,hExit,hKind⟩ := Thread.exitedOfComplete hX hComplete hg
  change kind = .exit at hKind
  subst kind
  have hSite := actualExitPc hX hExit
  have hExit' : X.get (warpLane l g lane,finish) = some ⟨site,.exit⟩ := hSelf.symm ▸ hExit
  have hWork := hHi.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  obtain ⟨hCuQ,hUsedK⟩ := hFootprint.metadataProtected hp
  obtain ⟨chosen,_,hc,hChosenLo,hChosenHi,ends,cur,hFollow⟩ :=
    activeTileOfEvent hp hX hg hWarp hl hWork hCuQ hExit'
      (by change 3231 < site; omega)
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
  have hBatch := (hUnique chosen ⟨hc,hChosenLo,hChosenHi⟩).trans
    (hUnique batch ⟨hb,hLo,hHi⟩).symm
  subst chosen
  let suffix := (X.tr (warpLane l g lane)).drop (cur.pos lane)
  have hLast : suffix[finish-cur.pos lane]? = some ⟨site,.exit⟩ := by
    unfold suffix
    rwa [List.getElem?_drop,Nat.add_sub_of_le hFollow.before]
  have hRun := cur.continuation lane hl
  have hEnd : ends lane = none := by
    cases hEnd : ends lane with
    | none => rfl
    | some _ =>
      rw [hEnd] at hRun
      exact (hRun.no_exit hLast).elim
  rw [hEnd] at hRun
  have hRun := hRun.after_local_nonempty (cur.localSteps lane hl) hFollow.nonempty
  have ht := cur.checkpoint lane hl
  rw [hSelf] at hRun
  obtain ⟨v,hV,hv⟩ := (firstActiveBiasAddresses hp g warp batch).apply ht
  have hQ off (ho : off ≤ 1) : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase+4*(batch+off))).at k) :=
    hCuQ _ (by omega)
  obtain ⟨fails,u,hReads,hAck,hu,hU⟩ := firstGeometryReadyTraceFramed hp hX stage hb
    (assignedCoordinates_valid hp hLo hHi).1 (firstVisitCarryRegs l g warp)
    hv hQ (hUsedK batch hb) (hRun.after_local (run_rtg hV))
  exact ⟨cur.pos lane,fails,u,hReads,hAck,hu,hU⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
