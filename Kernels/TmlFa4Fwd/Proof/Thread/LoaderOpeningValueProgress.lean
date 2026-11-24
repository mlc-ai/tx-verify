-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryStartProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPollProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyGate
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyExactOrdinal
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningBiasGuard
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVEntry
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Flow.ReturningPrefix
import Kernels.TmlFa4Fwd.Proof.LoaderMbarAddress
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPrefixWait
import Kernels.TmlFa4Fwd.Flow.Code.Part012

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.MBarrier Prologue Epilogue

noncomputable section

/-- Stable base registers for the opening V setup. -/
def openingValueBase (l : Launch) : List (Nat × Value) :=
  [(2535,b32 l.sharedBase),(7295,b64 (l.localBase+96)),(7294,b64 (l.localBase+64))]

/-- The opening V prelude starts with the shared base retained from initial allocation. -/
abbrev OpeningValueReached (l : Launch) (X : Execution) (g shuffles votes : Nat)
    (ends : Nat → Option TState) : Prop :=
  Nonempty (SchedulerWarpReached l X g 780 (fun _ => openingValueBase l)
    shuffles votes ends)

private theorem valueLoaderBypass {l : Launch} {g : Nat} {s : TState}
    (hs : At s 675 (loaderRoleFacts l 1)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 780 (openingValueBase l) := by
  have hNext : Seg kernel [] l g 1 675 (loaderRoleFacts l 1) 676
      ((7177,b32 1)::loaderRoleFacts l 1) := by
    intro t ht
    dsimp [loaderRoleFacts] at ht ⊢
    seg_fp ht using rfl
  obtain ⟨t,ht,hT⟩ := hNext s hs
  have hT := hT.mono hT.2.2.2.2.2
  obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g) Flow.code_676
    true hT hT.2.2.2.2.1 (by simp)
  have ht' := (loaderLinear (regs := []) (by decide) (by decide) hs.1
    (by simp) (by decide) ht).1
  have hu' := (loaderLinear (regs := []) (by decide) (by decide) hT.1
    (by simp) (by decide) hu).1
  exact ⟨u,run_rtg (run_comp ht' hu'),hU.mono hU.2.2.2.2.2⟩

/-- After recording its own first K publication, warp 15 takes the direct opening V route. -/
theorem openingValueReachedBySecondLoader {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (hw : warpIndex l g = 15) (hSh : 5 ≤ shuffles)
    {ends : Nat → Option TState} (hK : PrimingKeyCommitReached l X g shuffles votes ends) :
    OpeningValueReached l X g shuffles votes ends := by
  obtain ⟨F,⟨cur⟩⟩ := hK
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  obtain ⟨framed⟩ := cur.advanceLocal (pc' := 673) (G := fun _ => loaderRoleFacts l 1)
    (fun lane hl => by
      let thread := warpLane l g lane
      have hSame := (Step.sameWarp_lane hBlock hg hl).1
      have hWarp : warpIndex l thread = 14+(1 : Fin 2).val := hSame.2.symm.trans hw
      have hPos : 5 ≤ cur.pos lane := by
        have hBound : ((X.tr thread).take (cur.pos lane)).countP Execution.isShfl
            ≤ ((X.tr thread).take (cur.pos lane)).length := List.countP_le_length
        rw [cur.ordinals.shfl lane hl,List.length_take] at hBound
        omega
      have hs := cur.checkpoint lane hl
      have hF := loaderRoleFrameAtKeyCommit hp hMax.1 hSame.1.2.1 1 hWarp hPos
        (cur.bounded lane hl) (cur.recorded lane hl) (cur.localSteps lane hl) hs.1
      exact ⟨cur.state lane,.refl,hs.mono hF⟩)
  obtain ⟨done,_⟩ := primingKeyCursorAfterArrivalOfMaximal hp hMax hg (by omega) hSh framed
  exact done.advanceLocal (fun lane hl => valueLoaderBypass (done.checkpoint lane hl))

set_option maxRecDepth 15000 in
private theorem openingValueTailCode :
    (kernel.code.drop 785).all (fun i => Thread.staysPastEvent 785 i.op) = true := by kernel_rfl

private theorem openingValueTailSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (785 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem noValuePublicationAtPrimingWait {g : Nat} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {t u : TState}
    (hRun : Run kernel Assumptions.all l g {} (X.tr g) (some t))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) (hPc : u.pc = 782)
    (j : Nat) (hPub : X.AsyncArrive (g,j) (Thread.Loader.readyObject l g 1) true) :
    False := by
  obtain ⟨pc,hGet⟩ := hPub
  obtain ⟨⟨site,hSite⟩,_,_,_⟩ := actualAsyncArrival hX hGet
  by_cases hKey : site = 0
  · have hWhere : pc = 674 := by rw [hSite,hKey]; decide
    have hAddress := congrArg Loc.addr
      (loaderStartupAsyncAddress hp hX hGet (hWhere.symm ▸ (by decide : 674 ∈ [674,904])))
    simp only [hWhere,Thread.Loader.readyObject,readySlot_address] at hAddress
    have hBad : l.sharedBase + 8 + 32 = l.sharedBase + 32 := hAddress
    omega
  · have hHigh : 785 ≤ pc := by
      rw [hSite]
      fin_cases site <;> first | contradiction | decide
    have hTrace := hRun.returning_reach.append (TraceReach.of_local hLocal)
    simp only [List.append_nil] at hTrace
    have hLow := Thread.Loader.noEventAboveFinalFloor openingValueTailCode
      openingValueTailSegments hTrace (by rw [hPc]; decide) (List.mem_of_getElem? hGet)
    exact (Nat.not_lt_of_ge hHigh) hLow

/-- Both poll operands and the stable bases survive the opening V acquire. -/
def openingValueWaitFrame (l : Launch) :=
  [(1925,b32 (l.sharedBase+64)),(1926,b32 1)] ++ openingValueBase l

/-- The warp has recorded the successful empty acquire for its opening V packet. -/
abbrev OpeningValueAcquired (l : Launch) (X : Execution) (g shuffles votes : Nat)
    (ends : Nat → Option TState) :=
  SchedulerWarpReached l X g 785
    (fun _ => openingValueWaitFrame l) shuffles votes ends

/-- The actual successful initial V empty poll of a loader lane. -/
def OpeningValueWaitAt (l : Launch) (X : Execution) (g j : Nat) : Prop :=
  X.get (g,j) = some (primingVWaitEvent l g true)

/-- The opening poll is a slot-one empty acquisition at initial parity. -/
theorem OpeningValueWaitAt.emptyAcquire {l : Launch} {X : Execution} {g j : Nat}
    (h : OpeningValueWaitAt l X g j) : Thread.Loader.EmptyAcquire l X (g,j) 1 1 := by
  exact ⟨_,h,by simp [primingVWaitEvent,Thread.Loader.emptyObject,emptySlot_address]⟩

/-- A pending opening V wait can be advanced whenever a lane that has yet to publish V
has a phase-zero empty slot. The successful poll is recorded in every lane's trace. -/
theorem openingValueAcquiredOfReady (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (hStart : OpeningValueReached l X g shuffles votes ends)
    (ready : ∀ lane < 32, (∀ j, ¬ X.AsyncArrive (warpLane l g lane,j)
      (Thread.Loader.readyObject l (warpLane l g lane) 1) true) →
      let log := X.objects (Thread.Mma.Observation.emptyObject l g 1)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 0) :
    ∃ done : OpeningValueAcquired l X g shuffles votes ends,
      ∀ lane < 32, ∃ j, j+1 = done.pos lane ∧
        OpeningValueWaitAt l X (warpLane l g lane) j := by
  obtain ⟨cur⟩ := hStart
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hWidth : l.sharedBase + 64 < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase + 64) % 8 = 0 := by have := hp.shared.1; omega
  obtain ⟨prepared⟩ := cur.advanceLocal (fun lane hl => by
    have hs := cur.checkpoint lane hl
    obtain ⟨t,ht,hT⟩ := primingVWaitPrep hWidth _ (hs.mono ⟨hs.2.2.2.2.1,trivial⟩)
    obtain ⟨htA,keep⟩ := loaderLinear (regs := (openingValueBase l).map Prod.fst)
      (by decide) (by decide) hs.1 (by kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) ht
    exact ⟨t,run_rtg htA,hT.mono ((holds_append ..).mpr
      ⟨hT.2.2.2.2,holdsSchedulerFrame hs.2.2.2.2 keep (fun _ hm => List.mem_map_of_mem hm)⟩)⟩)
  let site := Thread.Loader.primingEmptySite 1
  have hCode : LoaderWaitCode site := Thread.Loader.primingEmptyCode 1
  obtain ⟨done,hTrace⟩ := loaderWarpWaitOfReadyLastTrace hMax hg hBlock hCode
    (by decide) hWidth hAlign prepared
    (fun _ _ => by simp [site,Thread.Loader.primingEmptySite,openingValueBase])
    (fun _ _ => by simp [site,Thread.Loader.primingEmptySite,openingValueBase])
    (fun _ _ => by simp [site,Thread.Loader.primingEmptySite,openingValueBase])
    (fun lane hl {_ _} hr hLoc hAt =>
      ready lane hl (noValuePublicationAtPrimingWait hp hMax.1 hr hLoc hAt.1))
  refine ⟨done,?_⟩
  intro lane hl
  obtain ⟨n,hPos,hRest⟩ := hTrace lane hl
  refine ⟨prepared.pos lane+n,hPos.symm,?_⟩
  change (X.tr (warpLane l g lane))[prepared.pos lane+n]? =
    some (primingVWaitEvent l (warpLane l g lane) true)
  rw [← List.getElem?_drop,hRest,List.getElem?_append_right (by simp)]
  simp [primingVWaitEvent,site,Thread.Loader.primingEmptySite]

/-- Enter the first local page-word load and transport the caller's stable operands. -/
theorem openingValueMetadataReachedWithFrame (hp : Pre p l m) {g shuffles votes : Nat}
    {ends : Nat → Option TState} (cur : OpeningValueAcquired l X g shuffles votes ends)
    {F : List (Nat × Value)} (hF : ∀ lane < 32, Holds (cur.state lane).regs F)
    (hKeep : ((kernel.code.drop 785).take 5).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true) :
    ∃ ready : SchedulerWarpReached l X g 790
        (fun _ => primingVFirstScratchFacts l ++ openingValueBase l ++ F) shuffles votes ends,
      ready.pos = cur.pos := by
  let G := openingValueBase l ++ F
  obtain ⟨raw,hPos,hBefore⟩ := cur.toSchedulerWarpAt.advanceLocalPreserving
    (pc' := 790) (G := fun _ => primingVFirstScratchFacts l ++ openingValueBase l ++ F)
    (fun lane hl => by
      have hs := cur.checkpoint lane hl
      have hStack : At (cur.state lane) 785 [(7295,b64 (l.localBase+96))] := by
        refine hs.mono ⟨holds_mem hs.2.2.2.2 ?_,trivial⟩
        simp [openingValueWaitFrame,openingValueBase]
      obtain ⟨t,ht,hT⟩ := primingVFirstScratchPrep hp.localMemory.2.1 _ hStack
      have hPreserve : ((kernel.code.drop 785).take 5).all
          (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true :=
        primingKeepAppend (F := openingValueBase l) (by kernel_rfl) hKeep
      obtain ⟨htA,hStable⟩ := loaderLinear (regs := G.map Prod.fst)
        (by decide) (by decide) hStack.1 hPreserve
        (by set_option maxRecDepth 100000 in kernel_rfl) ht
      have hHeld := ((holds_append ..).mp hs.2.2.2.2).2
      have hFrame : Holds (cur.state lane).regs G :=
        (holds_append ..).mpr ⟨hHeld,hF lane hl⟩
      have hAfter := holdsSchedulerFrame hFrame hStable (fun _ hm => List.mem_map_of_mem hm)
      apply Exists.intro t
      refine ⟨run_rtg htA,hT.mono ?_⟩
      rw [List.append_assoc]
      exact (holds_append ..).mpr ⟨hT.2.2.2.2,hAfter⟩)
  exact ⟨cur.reframe raw hPos hBefore,hPos⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
