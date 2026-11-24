-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.StatsCreditHistory
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
public import Kernels.TmlFa4Fwd.Proof.PrologueFenceProgress
import Kernels.TmlFa4Fwd.Proof.CorrectionLseFallback
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Barrier
import Lemmas.MBarrier.MBarrierInitOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.MBarrier Prologue Epilogue Correction

noncomputable section

/-- Any actual correction lane with a statistics credit has a tile assigned to its CTA. -/
theorem statisticsCreditRequiresWork {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hRole : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (hCredit : correctionAction e = some (.statsCredit stage)) :
    g/l.block < tilePrefix p p.batch * p.heads := by
  let cta := g/l.block
  let cutoff := tilePrefix p (min p.batch 31) * p.heads
  by_cases hFirst : cta < cutoff
  · exact hFirst.trans_le (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (Nat.min_le_left ..)))
  obtain ⟨loc,n,hKind⟩ := correctionStatsCreditKind hCredit
  have hSite := (correctionStatsCreditObservation stage hKind).mp hCredit
  have hPc : 7859 < e.pc ∧ e.pc < 9201 := by
    fin_cases stage <;> simp at hSite <;> omega
  have hg := event_thread_lt hX he
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have he' : X.get (warpLane l g (laneOf l g),j) = some e := by rwa [hSelf]
  have hRouted :=
    correctionFirstRouteOfEvent hp hX hg hRole.1 hRole.2 hLane (by omega) he'
  rw [ite_eq_right hFirst] at hRouted
  obtain ⟨ends, start, hs⟩ := hRouted
  rcases correctionFallbackGroupEvent hp hX hg start (Nat.le_of_not_gt hFirst) hPc.1 hs with
    ⟨_, _, done, hDone⟩ | ⟨first,batch,_,_,hb,_,hTile,_,_,_⟩
  · exact (exhaustedCannotVisitEarlier hp hPc.2 done hDone).elim
  · exact hTile.trans_le (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (by omega)))

/-- A maximal execution has actually initialized the per-stage statistics credit object. -/
theorem statisticsCreditInitialized {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {cta : Nat} (hc : cta < l.grid) (stage : Fin 2) :
    ∃ r ∈ X.objects (statsCreditLoc l cta stage), r.action = .init 128 := by
  let g := cta*l.block + 0
  have hb : 0 < l.block := by rw [hp.block]; decide
  have hg : g < l.threads := NamedBar.cta_thread_lt hc hb
  obtain ⟨hCTA,hLocal⟩ := NamedBar.lane_cta (c := cta) hb hb
  have hw : warpIndex l g = 0 := by unfold warpIndex g; rw [hLocal]
  obtain ⟨a,n,hSame,_,_,hInit⟩ := warp0InitializerRecords hp hMax hg hw
  have ha : a/l.block = cta := hSame.1.2.2.symm.trans hCTA
  let slot : Fin 34 := ⟨24+stage.val, by have := stage.isLt; omega⟩
  obtain ⟨j,_,he⟩ := hInit slot
  have hExpected : (initEvent l a slot).kind = .mbInit (statsCreditLoc l cta stage) 128 := by
    unfold initEvent statsCreditLoc
    rw [ha]
    fin_cases stage <;> rfl
  obtain ⟨k,r,hRecord,_,hAction,_,_⟩ := init_record_of_consistent hMax.1
    (show X.MbInit (a,j) (statsCreditLoc l cta stage) 128 from
      ⟨(initEvent l a slot).pc, hExpected ▸ he⟩)
  exact ⟨r,List.mem_of_getElem? hRecord,hAction⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread
