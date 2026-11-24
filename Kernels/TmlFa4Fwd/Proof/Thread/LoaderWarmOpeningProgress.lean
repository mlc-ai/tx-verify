-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSingleVisitPublished
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderSingleVisitPublished
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainWords
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmStartInPrefix
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmStartInPrefix
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasEntry
import all Kernels.TmlFa4Fwd.Proof.LoaderBiasTailGuard
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderSingleVisitDrainStart
import Kernels.TmlFa4Fwd.Flow.Code.Part010
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Proof.LoaderRingEntry
import all Kernels.TmlFa4Fwd.Proof.LoaderRingMbarAddress
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.RecordedCheckpointPath
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader
  (warmPageRoots warmStartFrame warmBiasRoots warmLaneRoots primingVAdmissionWithTripsLaneExtra
    vPrimingResidual loaderPipelineCutOp loaderLinear RingShape ringShapeOfAt warmRoleSeedCore
    loaderPrimingFrontierFacts loaderWarmGateWithFrame loaderPhaseWord OpeningValueCommitReached
    loaderWarmCounterInit warmResidualCore warmResidual flagCore warmResidualBitSetup)

def openingWarmFrame (p : Params) (l : Launch) (g batch lane : Nat) : List (Nat × Value) :=
  let co := assignedCoordinates p batch (g/l.block)
  let warp := warpIndex l g
  (123,.pred (decide (warp ≠ 14))) ::
    warmStartFrame p l batch (co.2/6) (Mma.trips p batch co.1) warp
      (warpLane l g lane%l.block) ++ warmBiasRoots p batch co.1 co.2

set_option maxRecDepth 4096 in
private theorem openingBiasPhaseOfPath {l : Launch} {g warp : Nat} {events : List Event}
    {s t : TState} {F : List (Nat × Value)}
    (hs : At s 539 ((123,.pred (decide (warp ≠ 14)))::F))
    (ht : At t 903 []) (hPath : TraceReach kernel Assumptions.all l g s events t) :
    t.regs 7177 = some (loaderPhaseWord (decide (warp ≠ 14))) := by
  have floor {a b : TState} {es : List Event}
      (h : TraceReach kernel Assumptions.all l g a es b) (ha : 903 < a.pc) : 903 < b.pc :=
    traceRetainsFloor floor904.1 floor904.2 h (by omega)
  have found {u : TState} {es : List Event}
      (h : TraceReach kernel Assumptions.all l g t es u) (hu : u.pc < 903) : False :=
    Nat.not_lt_of_ge ht.1.ge (boundOnPath floor903 hu h)
  have hR := hs.mono (show Holds s.regs [(123,.pred (decide (warp ≠ 14)))] from
    ⟨hs.2.2.2.2.1,trivial⟩)
  obtain ⟨r,_,_,_,hPc,hSub,hAcc,hRegs,_,hTail⟩ :=
    loaderCutOfObservedPath hPath (low := 539) (cut := 675) (bypass := 903)
      (by decide) (by decide) (by set_option maxRecDepth 100000 in kernel_rfl) floor
      (by rw [hs.1]; decide) (ringShapeOfAt hs) (fun _ => hs.2.1)
      hR.2.2.2.2 (by rw [ht.1]; decide)
  have hr : At r 675 [(123,.pred (decide (warp ≠ 14)))] :=
    ⟨hPc,hSub,hAcc,traceStartClean hTail ht.2.2.2.1,hRegs⟩
  have hSeed : Seg kernel [] l g 1 675 [] 676 [(7177,b32 1)] := by
    intro u hu
    seg_fp hu using rfl
  obtain ⟨u,hu,hU⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) (by decide) hSeed hr
  let select := decide (warp ≠ 14)
  obtain ⟨v,hv,hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_676 select hU hU.2.2.2.2.2.1 (by simp)
  have hvAll := (loaderLinear (regs := []) (by decide) (by decide) hU.1
    (by simp) (by decide) hv).1
  have hAfter := hTail.afterLocalOfNoBack ((run_rtg hu).trans (run_rtg hvAll))
    (fun hBack => found (TraceReach.of_local hBack) (by
      have h := hV.1
      dsimp only [select] at h
      by_cases hc : warp ≠ 14 <;> simp [hc] at h <;> omega))
  have finish {v : TState} {es : List Event} {bit : Bool}
      (hv : 774 ≤ v.pc) (hV : RingShape v)
      (hp : Holds v.regs [(7177,loaderPhaseWord bit)])
      (h : TraceReach kernel Assumptions.all l g v es t) :
      t.regs 7177 = some (loaderPhaseWord bit) :=
    (retainLoaderFrame (lower := 774) (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl) floor904 (by rw [ht.1]; decide)
      h hv hV hp).1
  by_cases hRole : warp = 14
  · have hV' : At v 677 [] := by
      refine ⟨?_,hV.2.1,hV.2.2.1,hV.2.2.2.1,trivial⟩
      simpa [select,hRole] using hV.1
    obtain ⟨w,_,_,_,hPc,hSub,hAcc,_,_,hRest⟩ :=
      loaderCutOfObservedPath hAfter (F := []) (low := 677) (cut := 773) (bypass := 903)
        (by decide) (by decide) (by set_option maxRecDepth 100000 in kernel_rfl) floor
        (by rw [hV'.1]; decide) (ringShapeOfAt hV') (fun _ => hV'.2.1) trivial
        (by rw [ht.1]; decide)
    have hw : At w 773 [] := ⟨hPc,hSub,hAcc,traceStartClean hRest ht.2.2.2.1,trivial⟩
    have hReset : Seg kernel [] l g 1 773 [] 774 [(7177,loaderPhaseWord false)] := by
      intro z hz
      seg_fp hz using rfl
    obtain ⟨z,hz,hZ⟩ := linearFramed (by decide) (by decide)
      (by decide) (by decide) hReset hw
    have hLast := hRest.afterLocalOfNoBack (run_rtg hz)
      (fun hBack => found (TraceReach.of_local hBack) (by rw [hZ.1]; decide))
    simpa [hRole] using finish hZ.1.ge (ringShapeOfAt hZ) hZ.2.2.2.2 hLast
  · have hV' : At v 780 [(7177,loaderPhaseWord true)] := by
      refine ⟨?_,hV.2.1,hV.2.2.1,hV.2.2.2.1,hV.2.2.2.2.1,trivial⟩
      simpa [select,hRole] using hV.1
    simpa [hRole] using finish (by rw [hV'.1]; decide) (ringShapeOfAt hV') hV'.2.2.2.2 hAfter

private theorem openingWarmFrameAtValueCommit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g batch sShuffles sVotes shuffles votes : Nat}
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    {endsSeed ends : Nat → Option TState}
    (seed : SchedulerWarpReached l X g 415 (loaderPrimingFrontierFacts p l g batch)
      sShuffles sVotes endsSeed)
    {C : Nat → List (Nat × Value)} (commit : SchedulerWarpReached l X g 903 C shuffles votes ends)
    (lane : Nat) (hl : lane < 32) :
    Holds (commit.state lane).regs
      ((7177,loaderPhaseWord (decide (warpIndex l g ≠ 14))) ::
        openingWarmFrame p l g batch lane) := by
  let co := assignedCoordinates p batch (g/l.block)
  let n := Mma.trips p batch co.1
  let t := warpLane l g lane
  let warp := warpIndex l g
  let G := warmPageRoots p l batch (t%l.block)
  let F := warmStartFrame p l batch (co.2/6) n warp (t%l.block) ++
    warmBiasRoots p batch co.1 co.2
  have ⟨hTile,hHead⟩ := assignedCoordinates_valid hp hLo hHi
  have hSeed := seed.checkpoint lane hl
  have hStart : At (seed.state lane) 415
      (Loader.primingKAddressFacts p l batch co.2 co.1 warp lane ++ G) := by
    apply hSeed.mono
    have h := (holds_append ..).mp hSeed.2.2.2.2
    apply (holds_append ..).mpr
    refine ⟨h.1,?_⟩
    simp only [G,warmPageRoots,warmLaneRoots,List.cons_append,Holds]
    exact ⟨h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,
      holds_lookup h.1 rfl,holds_lookup h.1 rfl,trivial⟩
  obtain ⟨_,s,hLocal,hs⟩ := primingVAdmissionWithTripsLaneExtra hp (g := t)
    hb (hHead.trans hp.heads_signed) hTile hl
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hStart
  have hs' : At s 488 F := by
    refine hs.mono ?_
    simp only [F,warmStartFrame,warmBiasRoots,warmPageRoots,warmLaneRoots,List.cons_append,
      List.nil_append,Holds]
    repeat' apply And.intro
    all_goals first
      | trivial
      | exact holds_lookup hs.2.2.2.2 rfl
      | (have hLaneWarp : (32 * warp + lane) / 32 = warp := by omega
         rw [← hLaneWarp]
         exact holds_lookup hs.2.2.2.2 rfl)
  have hAt := commit.checkpoint lane hl
  obtain ⟨_,hPath⟩ := recordedCheckpointsPath (seed.bounded lane hl) (commit.bounded lane hl)
    (seed.recorded lane hl) (seed.localSteps lane hl) (commit.recorded lane hl)
    (commit.localSteps lane hl) (fun _ hBack =>
      Nat.not_lt_of_ge hAt.1.ge (boundOnPath floor903 (by rw [hSeed.1]; decide) hBack))
  have hReach := hPath.afterLocalOfNoBack hLocal (fun hBack =>
    Nat.not_lt_of_ge hAt.1.ge
      (boundOnPath floor903 (by rw [hs'.1]; decide) (TraceReach.of_local hBack)))
  have hTarget : 538 ≤ (commit.state lane).pc ∧ (commit.state lane).pc ≤ 903 := by
    rw [hAt.1]
    decide
  obtain ⟨r,_,_,_,hPc,hSub,hAcc,hHeld,_,hRest⟩ :=
    loaderCutOfObservedPath hReach (low := 488) (cut := 538) (bypass := 903)
      (by decide) (by decide) (by set_option maxRecDepth 100000 in kernel_rfl)
      (fun hTrace hAfter => by
        have hFloor := traceRetainsFloor floor904.1 floor904.2 hTrace (by omega)
        omega)
      (by rw [hs'.1]; decide) (ringShapeOfAt hs') (fun _ => hs'.2.1) hs'.2.2.2.2 hTarget
  have hR : At r 538 F := ⟨hPc,hSub,hAcc,traceStartClean hRest hAt.2.2.2.1,hHeld⟩
  have hWarp := holds_mem hHeld (show (1062,b32 warp) ∈ F by simp [F,warmStartFrame])
  obtain ⟨u,hu,hU⟩ := (warmRoleSeedCore (g := t) hw (warpIndex_lt hp g)).apply
    (hR.mono ⟨hWarp,trivial⟩)
  obtain ⟨huAll,hKeep⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide)
    hR.1 (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  have hU' : At u 539 (openingWarmFrame p l g batch lane) :=
    hU.mono ⟨hU.2.2.2.2.1,holdsSchedulerFrame hHeld hKeep (fun _ hm => List.mem_map_of_mem hm)⟩
  have hTail := hRest.afterLocalOfNoBack (run_rtg huAll) (fun hBack =>
    Nat.not_lt_of_ge hAt.1.ge
      (boundOnPath floor903 (by rw [hU.1]; decide) (TraceReach.of_local hBack)))
  refine ⟨openingBiasPhaseOfPath hU' (hAt.mono trivial) hTail,?_⟩
  exact retainLoaderFrame (lower := 539) (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) floor904 (by rw [hAt.1]; decide) hTail
    hU'.1.ge (ringShapeOfAt hU') hU'.2.2.2.2

def warmResidueFlag (word : Nat) : Bool := decide (toSigned 32 (BitVec.ofNat 64 word) < 0)

def openingWarmPublishedFrame (p : Params) (l : Launch) (g batch lane : Nat) : List (Nat × Value) :=
  let co := assignedCoordinates p batch (g/l.block)
  let t := warpLane l g lane
  [(164,.pred (warmResidueFlag (vPrimingResidual p batch co.1))),
    (7177,loaderPhaseWord (decide (warpIndex l g ≠ 14)))] ++
    openingWarmFrame p l g batch lane ++ drainSchedulerFrame p l t

/-- Both priming publications retain the exact launch frame and seeded warm Bias phase. -/
theorem openingValuePublishedWithWarmFrame {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch shuffles votes seedShuffles seedVotes : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hCuQ : DrainCuQProtected p X)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    {endsSeed ends : Nat → Option TState}
    (seed : SchedulerWarpReached l X g 415 (loaderPrimingFrontierFacts p l g batch)
      seedShuffles seedVotes endsSeed)
    {F : Nat → List (Nat × Value)} (commit : SchedulerWarpReached l X g 903 F shuffles votes ends) :
    ∃ after : SchedulerWarpReached l X g 905 (openingWarmPublishedFrame p l g batch)
        shuffles votes ends,
      ∀ lane < 32, ∃ j, after.pos lane = j+1 ∧
        PrimingPublication l X (warpLane l g lane,j) 1 := by
  let co := assignedCoordinates p batch (g/l.block)
  let thread := warpLane l g
  let frame := openingWarmPublishedFrame p l g batch
  let post (lane : Nat) := next (next (commit.state lane))
  obtain ⟨_,⟨first⟩⟩ := schedulerRootsOfMaximal hp hMax hg hw hCuQ
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) :
      X.get (thread lane,commit.pos lane) = some ⟨903,.asyncCommit⟩ ∧
      PrimingPublication l X (thread lane,commit.pos lane+1) 1 ∧
      At (post lane) 905 (frame lane) ∧
      Run kernel Assumptions.all l (thread lane) {}
        ((X.tr (thread lane)).take (commit.pos lane+2)) (some (post lane)) ∧
      Run kernel Assumptions.all l (thread lane) (post lane)
        ((X.tr (thread lane)).drop (commit.pos lane+2)) (ends lane) := by
    have hs := commit.checkpoint lane hl
    have hf := preserveStartupAtCommit first commit lane hl
    have hInputs := tripInputsAtCommit hp hb hLo hHi seed commit lane hl
    have hWarm := openingWarmFrameAtValueCommit hp hw hb hLo hHi seed commit lane hl
    have hAt : At (commit.state lane) 903 (frame lane) := by
      apply hs.mono
      change Holds (commit.state lane).regs
        ((164,.pred (warmResidueFlag (vPrimingResidual p batch co.1))) ::
          ((7177,loaderPhaseWord (decide (warpIndex l g ≠ 14))) ::
            openingWarmFrame p l g batch lane) ++ drainSchedulerFrame p l (thread lane))
      exact ⟨hInputs.2.2.1,(holds_append ..).mpr ⟨hWarm,hf.2.2⟩⟩
    have hC : At (commit.state lane) (Loader.copyCommitPc 1)
        [((Loader.copyArrivalAddress 1).1,b32 l.sharedBase)] := hs.mono ⟨hf.2.1,trivial⟩
    have hWidth : l.sharedBase+(Loader.copyArrivalAddress 1).2 < 2^32 := by
      have := hp.shared.2.1
      change l.sharedBase+40 < 2^32
      omega
    have hAlign : l.sharedBase%8 = 0 := by have := hp.shared.1; omega
    obtain ⟨he,hPub,hPre,hRest⟩ := Loader.copyCommitAndArriveOfMaximal hMax
      (Step.sameWarp_lane hBlock hg hl).1.1.2.1 1 hC hWidth hAlign
      (commit.localSteps lane hl) (commit.recorded lane hl) (commit.continuation lane hl)
      (commit.positive lane hl) (commit.bounded lane hl) (commit.released lane hl)
    exact ⟨he,hPub,hAt.next.next,hPre,hRest⟩
  have hCounts (pred : Event → Bool)
      (hCommit : pred ⟨903,.asyncCommit⟩ = false)
      (hArrival : ∀ loc, pred ⟨904,.asyncArrive loc true⟩ = false)
      (lane : Nat) (hl : lane < 32) :
      ((X.tr (thread lane)).take (commit.pos lane+2)).countP pred =
        ((X.tr (thread lane)).take (commit.pos lane)).countP pred := by
    obtain ⟨hC,hA,_,_,_⟩ := hLane lane hl
    rw [countP_take_succ_false hA (hArrival _),countP_take_succ_false hC hCommit]
  let after : SchedulerWarpReached l X g 905 frame shuffles votes ends :=
    ⟨⟨fun lane => commit.pos lane+2,post,post,
      ⟨fun lane hl => (hCounts _ rfl (fun _ => rfl) lane hl).trans (commit.ordinals.shfl lane hl),
        fun lane hl => (hCounts _ rfl (fun _ => rfl) lane hl).trans (commit.ordinals.vote lane hl)⟩,
      fun lane hl => (hLane lane hl).2.2.2.2,fun _ _ => .refl,
      fun lane hl => (hLane lane hl).2.2.1⟩,fun _ _ => Nat.succ_pos _,
      fun lane hl => len_of_get (hLane lane hl).2.1,
      fun lane hl => releasedIfLast (hLane lane hl).2.1 (by intro h; cases h),
      fun lane hl => (hLane lane hl).2.2.2.1⟩
  exact ⟨after,fun lane hl => ⟨commit.pos lane+1,rfl,(hLane lane hl).2.1⟩⟩

def warmFirstFrame (p : Params) (l : Launch) (g batch lane : Nat) : List (Nat × Value) :=
  let co := assignedCoordinates p batch (g/l.block)
  let n := Mma.trips p batch co.1
  let residual := vPrimingResidual p batch co.1
  let bias := decide (warpIndex l g ≠ 14)
  [(7174,b32 0),(7178,loaderPhaseWord bias),(7179,b32 2),(7180,b32 1),
    (1117,b32 (residual/2^31)),(1116,b32 (n-2)),
    (7,.pred (decide (10 < n) && warmResidueFlag residual))] ++
    openingWarmPublishedFrame p l g batch lane

set_option maxRecDepth 4096 in
private theorem warmEntryLocal {p : Params} {l : Launch} {g batch lane : Nat}
    {t : TState}
    (hLive : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hSize : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 < 2^31)
    (ht : At t 905 (openingWarmPublishedFrame p l g batch lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 917 (warmFirstFrame p l g batch lane) := by
  let co := assignedCoordinates p batch (g/l.block)
  let n := Mma.trips p batch co.1
  let residual := vPrimingResidual p batch co.1
  let bit := loaderPhaseWord (decide (warpIndex l g ≠ 14))
  let t' := warpLane l g lane
  let E := openingWarmPublishedFrame p l g batch lane
  let flag : Nat × Value := (7,.pred (decide (10 < n) && warmResidueFlag residual))
  have hN : (1088,b32 n) ∈ E := by
    simp [E,openingWarmPublishedFrame,openingWarmFrame,warmStartFrame,n,co]
  have hN' : (1091,b32 (n-1)) ∈ E := by
    simp [E,openingWarmPublishedFrame,openingWarmFrame,warmStartFrame,n,co]
  have hResidual : (1089,b32 residual) ∈ E := by
    simp [E,openingWarmPublishedFrame,openingWarmFrame,warmStartFrame,warmBiasRoots,residual,co]
  have hBit : (7177,bit) ∈ E := by simp [E,openingWarmPublishedFrame,bit]
  have hIn : At t 905 ([(1088,b32 n),(164,.pred (warmResidueFlag residual))]++E) :=
    ht.mono ⟨holds_mem ht.2.2.2.2 hN,ht.2.2.2.2.1,ht.2.2.2.2⟩
  obtain ⟨a,ha,hA⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (flagCore l t' n (warmResidueFlag residual) hSize) hIn
  have hA' : At a 907 ([(1088,b32 n)]++flag::E) :=
    hA.mono ⟨holds_mem hA.2.2.2.2.2 hN,hA.2.2.2.2⟩
  obtain ⟨b,hb,hB⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) (by decide)
    (warmResidualCore (l := l) (g := t') hSize) hA'
  have hWord : warmResidual n = n-2 := by
    unfold warmResidual
    rw [show n+(2^32-2)=n-2+2^32 by change 2 ≤ n at hLive; omega,
      Nat.add_mod_right,Nat.mod_eq_of_lt (by change n<2^31 at hSize; omega)]
  let G := (1116,b32 (n-2))::flag::E
  have hB' : At b 908 ([(1088,b32 n),(1091,b32 (n-1))]++G) := by
    apply hB.mono
    have h := hB.2.2.2.2
    exact ⟨holds_mem h.2.2 hN,holds_mem h.2.2 hN',hWord ▸ h.1,h.2⟩
  obtain ⟨c,hc,hC⟩ := loaderWarmGateWithFrame (l := l) (g := t') hSize
    (by set_option maxRecDepth 100000 in kernel_rfl) hB'
  have hPc : c.pc = 912 := by
    have h := hC.1
    change c.pc = (if n < 2 then 1353 else 912) at h
    rwa [ite_eq_right (Nat.not_lt_of_ge hLive)] at h
  have hcIn : At c 912 ([(1089,b32 residual)]++G) :=
    ⟨hPc,hC.2.1,hC.2.2.1,hC.2.2.2.1,
      holds_mem hC.2.2.2.2.2.2.2 hResidual,hC.2.2.2.2.2⟩
  have hRes : residual < 2^32 := Nat.mod_lt _ (by decide)
  obtain ⟨d,hd,hD⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) (by decide)
    (warmResidualBitSetup hRes) hcIn
  let H := (1117,b32 (residual/2^31))::G
  have hdIn : At d 913 ([(7177,bit)]++H) := hD.mono
    ⟨holds_mem hD.2.2.2.2.2.2.2 hBit,hD.2.2.2.2⟩
  have hInit (phase : Bool) : Seg kernel [] l t' 4 913 [(7177,loaderPhaseWord phase)]
      917 [(7174,b32 0),(7178,loaderPhaseWord phase),(7179,b32 2),(7180,b32 1)] := by
    cases phase <;> intro r hr <;> seg_fp hr using rfl
  obtain ⟨u,hu,hU⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (hInit (decide (warpIndex l g ≠ 14))) hdIn
  exact ⟨u,(run_rtg ha).trans ((run_rtg hb).trans ((run_rtg hc).trans ((run_rtg hd).trans
    (run_rtg hu)))),hU⟩

/-- A loader with remaining KV work enters the first actual warm visit after its priming packets. -/
theorem warmFirstOfOpeningPublication {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch shuffles votes : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hLive : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g 905
      (openingWarmPublishedFrame p l g batch) shuffles votes ends) :
    ∃ done : SchedulerWarpReached l X g 917 (warmFirstFrame p l g batch) shuffles votes ends,
      done.pos = cur.pos := by
  have hCount := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hLength := (hp.lengths batch hb).2.2
  exact cur.advanceLocalWithPosition (fun lane hl =>
    warmEntryLocal hLive (by omega) (cur.checkpoint lane hl))

private theorem noFirstWarmKeyPublicationBeforeOpeningValue {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j i : Nat} (hPub : PrimingPublication l X (g,j) 1) (hi : i ≤ j) :
    ¬ X.AsyncArrive (g,i) (readyObject l g 2) true := by
  rintro ⟨pc,he⟩
  have hBefore : pc < 905 := by
    by_contra! h
    have hFloor : auditedFloor 905 := by
      constructor <;> set_option maxRecDepth 100000 in kernel_rfl
    have hOrder : j < i := Thread.traceOrderOfPcFloor hX hFloor.1 hFloor.2
      (show X.get (g,j) = some ⟨904,.asyncArrive (readyObject l g 1) true⟩ from hPub) he
      (by change 904 < 905; decide) h
    omega
  obtain ⟨⟨site,rfl⟩,_,_,_⟩ := Loader.actualAsyncArrival hX he
  have hFirst : Loader.copyCommitPc site+1 ∈ [674,904] :=
    (by decide : ∀ site : Fin 6, Loader.copyCommitPc site+1 < 905 →
      Loader.copyCommitPc site+1 ∈ [674,904]) site hBefore
  obtain ⟨off,hoff,hLoc⟩ := Loader.loaderFixedAsyncAddress hp hX he hFirst
  have hx := congrArg Loc.addr hLoc
  change l.sharedBase+48 = l.sharedBase+off at hx
  simp at hoff
  omega

/-- The reached first warm round retains the actual lane cursors and the immutable launch frame. -/
structure WarmCacheStarted (p : Params) (l : Launch) (X : Execution) (g batch : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SchedulerWarpReached l X g 917 (warmFirstFrame p l g batch) shuffles votes ends
  unpublishedKey : ∀ lane < 32, ∀ index < reached.pos lane,
    ¬ X.AsyncArrive (warpLane l g lane,index) (readyObject l (warpLane l g lane) 2) true

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    {g batch shuffles votes seedShuffles seedVotes : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hCuQ : DrainCuQProtected p X) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hLive : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    {endsSeed ends : Nat → Option TState}
    (seed : SchedulerWarpReached l X g 415 (loaderPrimingFrontierFacts p l g batch)
      seedShuffles seedVotes endsSeed) {F : Nat → List (Nat × Value)}
    (commit : SchedulerWarpReached l X g 903 F shuffles votes ends)
include hp hMax hg hw hCuQ hb hLo hHi hLive seed commit

/-- Either loader warp moves from its recorded opening V packet to its first warm round. -/
theorem warmCacheStartedWithRankOfOpeningValueCommit :
    ∃ next : WarmCacheStarted p l X g batch, next.shuffles = shuffles := by
  obtain ⟨cur,hPub⟩ := openingValuePublishedWithWarmFrame hp hMax hg hw hCuQ hb hLo hHi seed commit
  obtain ⟨started,hPos⟩ := warmFirstOfOpeningPublication hp hb hLo hHi hLive cur
  refine ⟨⟨shuffles,votes,ends,started,?_⟩,rfl⟩
  intro lane hl index hi
  obtain ⟨j,hj,hArrival⟩ := hPub lane hl
  change index < started.pos lane at hi
  rw [hPos,hj] at hi
  exact noFirstWarmKeyPublicationBeforeOpeningValue hp hMax.1 hArrival (by omega)

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
