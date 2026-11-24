-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OutputFree
public import Kernels.TmlFa4Fwd.Proof.PrologueFenceProgress
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.OutputBarrierFacts
import Lemmas.Step.CtaBarNamed
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Barrier
import Lemmas.MBarrier.MBarrierInitOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Output
open PTX PTX.Proof PTX.Flow PTX.MBarrier Epilogue Prologue

noncomputable section

private theorem idleSearchEventIsExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g cta : Nat} (hg : g < l.threads) (hCTA : cta < l.grid)
    (hIdle : tilePrefix p p.batch * p.heads ≤ cta)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs)
    (hBase : ∀ lane < 32, (7506, b64 p.cuQBase) ∈ F lane)
    (hWarp : ∀ lane < 32, (1062, b32 13) ∈ F lane)
    (hReads : CuQReadsFromLaunch p X)
    {lane j : Nat} {e : Event} (hLate : 2873 < e.pc)
    {first shuffles votes : Nat} (hFirst : first < p.batch)
    (cur : SchedulerWarpAt l X g 2824 (fun lane => groupSearchFacts p cta first lane (F lane))
      shuffles votes ends)
    (hFollow : WarpFollowsEvent l X g cur.pos lane j e) :
    e.kind = .exit := by
  rcases cur.searchGroupTo hp hX hg hCTA hFirst hF hBase hWarp hReads
      (.inr hFollow) hLate with
    ⟨_, done, hDone⟩ | ⟨hMore, ⟨_, next, hNext⟩ | ⟨hSelect, _, _⟩⟩
  · have hRemain := hDone hFollow
    obtain ⟨v, hLocal, hv, hf, hW⟩ := done.exitWithoutTileLocal hp lane hRemain.lane
    have hRun := (done.continuation lane hRemain.lane).after_local_nonempty hLocal hRemain.nonempty
    have hExit := drainExitTraceOfNonempty hv hf hW hRun hRemain.nonempty
    have hMem : e ∈ (X.tr (warpLane l g lane)).drop (done.pos lane) := by
      apply List.mem_of_getElem? (i := j - done.pos lane)
      rw [List.getElem?_drop, Nat.add_sub_of_le hRemain.before]
      exact hRemain.get
    rw [hExit] at hMem
    obtain rfl := List.mem_singleton.mp hMem
    rfl
  · exact idleSearchEventIsExit hp hX hg hCTA hIdle hF hBase hWarp hReads hLate hMore next
      (hNext hFollow)
  · exact False.elim ((Nat.not_lt_of_ge
      ((Nat.mul_le_mul_right _ (tilePrefix_mono p (Nat.min_le_left ..))).trans hIdle)) hSelect)
termination_by p.batch - first
decreasing_by omega

/-- An output-free credit requires an assigned tile in the same CTA. -/
theorem freeRequiresWork {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta g j : Nat} {stage : Fin 2} (he : FreeCredit l X cta stage (g,j))
    (hCuQ : DrainCuQProtected p X) :
    cta < tilePrefix p p.batch * p.heads := by
  obtain ⟨e, he, hPc, hKind⟩ := he
  have hExact : X.get (g,j) = some ⟨freePc stage, .arrive (freeObject l cta stage) 0 1 true .cta⟩ :=
    by simpa only [← hPc, ← hKind] using he
  have hRange : 2768 ≤ e.pc ∧ e.pc < 3099 ∧ 2873 < e.pc := by
    rw [hPc]
    fin_cases stage <;> decide
  have hg := event_thread_lt hX he
  have hw := issuerWarpOfEpiloguePc hp hX he hRange.1 hRange.2.1
  obtain ⟨hAddr, _, _, _, _⟩ := OutputWarp.freeOperands hp hX stage hExact
  have hOwner : cta = g/l.block := congrArg Loc.cta hAddr
  rw [hOwner]
  by_contra! hIdle
  have hReads : CuQReadsFromLaunch p X := fun i hi =>
    cuQWordReadsFromLaunchOfProtected hp hX hi (hCuQ i hi)
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g lane = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hEvent : X.get (warpLane l g lane,j) = some e := by rwa [hSelf]
  obtain ⟨_, cut, hFollow⟩ :=
    warp13FirstGroupCutoffOfLateEvent hp hX hg hw hReads hl hEvent (by omega)
  let F := fun lane => schedulerStartupFrame p l (warpLane l g lane)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hCTA : g / l.block < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs :=
    fun lane _ => schedulerStartupFramed p l (warpLane l g lane)
  have hCta (lane : Nat) (hl : lane < 32) : (1072, b32 (g / l.block)) ∈ F lane := by
    have ha := (Step.sameWarp_lane hBlock hg hl).1.1.2.2
    simp [F, schedulerStartupFrame, warpLane, ha]
  have hBase : ∀ lane < 32, (7506, b64 p.cuQBase) ∈ F lane := by simp [F, schedulerStartupFrame]
  have hWarp : ∀ lane < 32, (1062, b32 13) ∈ F lane := by simp [F, schedulerStartupFrame]
  have hPast : tilePrefix p (min p.batch 31) * p.heads ≤ g/l.block := by
    exact (Nat.mul_le_mul_right _ (tilePrefix_mono p (Nat.min_le_left ..))).trans hIdle
  obtain ⟨start, hStart⟩ := cut.enterSearchAt hPast (hCTA.trans hp.grid.2.2) hF hCta
  have hNow := hStart.symm ▸ hFollow
  have hExit := idleSearchEventIsExit hp hX hg hCTA hIdle hF hBase hWarp hReads
    hRange.2.2 hp.shape.1 start hNow
  rw [hKind] at hExit
  cases hExit

/-- Maximal startup records the initialization of either output-free stage. -/
theorem freeInitializedOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {cta : Nat} (hc : cta < l.grid) (stage : Fin 2) :
    ∃ r ∈ X.objects (freeObject l cta stage), r.action = .init 32 := by
  let g := cta*l.block + 0
  have hb : 0 < l.block := by rw [hp.block]; decide
  have hg : g < l.threads := NamedBar.cta_thread_lt hc hb
  obtain ⟨hCTA,hLocal⟩ := NamedBar.lane_cta (c := cta) hb hb
  have hw : warpIndex l g = 0 := by unfold warpIndex g; rw [hLocal]
  obtain ⟨a,n,hSame,_,_,hInit⟩ := warp0InitializerRecords hp hMax hg hw
  have ha : a/l.block = cta := hSame.1.2.2.symm.trans hCTA
  let slot : Fin 34 := ⟨28+stage.val, by have := stage.isLt; omega⟩
  obtain ⟨j,_,he⟩ := hInit slot
  have hExpected : (initEvent l a slot).kind = .mbInit (freeObject l cta stage) 32 := by
    unfold initEvent freeObject
    rw [ha]
    fin_cases stage <;> rfl
  obtain ⟨k,r,hRecord,_,hAction,_,_⟩ := init_record_of_consistent hMax.1
    (show X.MbInit (a,j) (freeObject l cta stage) 32 from
      ⟨(initEvent l a slot).pc, hExpected ▸ he⟩)
  exact ⟨r,List.mem_of_getElem? hRecord,hAction⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Output
