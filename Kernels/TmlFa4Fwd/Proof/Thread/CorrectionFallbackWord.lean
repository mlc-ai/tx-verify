-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
public import Kernels.TmlFa4Fwd.Proof.CorrectionFallbackWarp
import Kernels.TmlFa4Fwd.Proof.CorrectionLseFromSelected
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.Termination
import Kernels.TmlFa4Fwd.Proof.NoCancellation
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Lemmas.Step.ExitLast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow Prologue Epilogue Correction.Fallback

/-- Correction's optional metadata lookup when advancing a request group. -/
@[no_expose] def CorrectionFallbackCuQRead (X : Execution) (i : EvId) (a : Acc)
    (bytes : List (Option Byte)) : Prop := X.get i = some ⟨7821, .rd a bytes⟩

def CorrectionFallbackAddresses (p : Params) (X : Execution) : Prop :=
  ∀ i a bytes, CorrectionFallbackCuQRead X i a bytes →
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4 * index), size := 4}

private theorem noCorrectionFallbackAfterSearch {l : Launch} {X : Execution} {g pos j : Nat}
    {s : TState} {ending : Option TState} (hPc : 7864 ≤ s.pc)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hj : pos ≤ j) {a : Acc} {bytes : List (Option Byte)}
    (he : X.get (g,j) = some ⟨7821,.rd a bytes⟩) : False := by
  have hCode : (kernel.code.drop 7864).all (fun i => staysPastEvent 7864 i.op) = true := by
    decide +kernel
  have hSites : ∀ site ∈ Assumptions.swExp2Sites, site < 7864 := by decide
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun hr
  have hMem : (⟨7821,.rd a bytes⟩ : Event) ∈ (X.tr g).drop pos := by
    apply List.mem_of_getElem? (i := j-pos)
    rw [List.getElem?_drop,Nat.add_sub_of_le hj]
    exact he
  exact (by decide : ¬ 7864 ≤ 7821) (eventTailEventsOfSegmentFloor hCode (fun site hlo hm _ _ =>
    (Nat.not_lt_of_ge hlo (hSites site hm)).elim) hWalk hPc _ hMem)

private theorem correctionFallbackReadOfComplete {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X)
    {g : Nat} (hg : g < l.threads) (hLoWarp : 8 ≤ warpIndex l g) (hHiWarp : warpIndex l g < 12)
    {src j : Nat} (hSrc : src < 32) {a : Acc} {bytes : List (Option Byte)}
    (he : CorrectionFallbackCuQRead X (warpLane l g src,j) a bytes) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4 * index), size := 4} := by
  let thread := warpLane l g src
  let cta := g/l.block
  let F := fallbackFrame p l g
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hGet : X.get (thread,j) = some ⟨7821,.rd a bytes⟩ := he
  obtain ⟨ends, entry, hFollow⟩ := Correction.correctionFirstRouteOfEvent
    hp hX hg hLoWarp hHiWarp hSrc (show 7801 < 7821 by decide) hGet
  by_cases hFirst : g/l.block < tilePrefix p (min p.batch 31)*p.heads
  · have hs : 7864 ≤ (entry.state src).pc := by
      rw [(entry.checkpoint src hSrc).1, ite_eq_left hFirst]
    exact (noCorrectionFallbackAfterSearch hs
      ((entry.continuation src hSrc).after_local_nonempty
        (entry.localSteps src hSrc) hFollow.nonempty)
      hFollow.before hGet).elim
  have hEnds (lane : Nat) (hl : lane < 32) : ends lane = none := by
    have hThread := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
    obtain ⟨pc,hExit⟩ := (hDone.1 (warpLane l g lane) hThread).resolve_left (noCanceled hX)
    let index := (X.tr (warpLane l g lane)).length-1
    have hExitGet : X.get (warpLane l g lane,index) = some ⟨pc,.exit⟩ := by
      simpa only [List.getLast?_eq_getElem?,Execution.get,index] using hExit
    have hPos : entry.pos lane ≤ index := by
      by_contra! hLt
      exact hFollow.noExit lane hl index hLt pc hExitGet
    have hSuffix : ((X.tr (warpLane l g lane)).drop (entry.pos lane))[index-entry.pos lane]? =
        some ⟨pc,.exit⟩ := by
      rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
      exact hExitGet
    have hr := entry.continuation lane hl
    cases h : ends lane with
    | none => rfl
    | some out =>
      rw [h] at hr
      exact (hr.no_exit hSuffix).elim
  have hCta : cta < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hCtaWord : cta + 1 < 2^32 := by have := hp.grid.2.2; omega
  obtain ⟨ready,hReady⟩ := entry.advanceLocalAt (pc' := 7807)
    (G := Correction.correctionFirstRouteFacts p l g) (by
      intro lane hl
      refine ⟨entry.state lane,.refl,?_⟩
      simpa only [ite_eq_right hFirst] using entry.checkpoint lane hl)
  obtain ⟨first,hStart⟩ := startSearch hp hg hCtaWord ready
  have hFrame : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ fallbackFrameRegs :=
    fun _ _ => fallbackFrame_mem
  have hBase : ∀ lane < 32, (7506,b64 p.cuQBase) ∈ F lane := by
    intro lane _
    simp [F,fallbackFrame,Correction.firstShuffleFacts,Correction.afterCreditFacts,
      Correction.creditFacts,Correction.entryFacts,nonzeroBarrierFacts,abiFacts]
  have done {G : Nat → List (Nat × Value)} {ord : Nat}
      (q : SchedulerWarpAt l X g 7864 G ord 0 ends) (hj : q.pos src ≤ j) : False := by
    have hr := (hEnds src hSrc ▸ q.continuation src hSrc).after_local (q.localSteps src hSrc)
    exact noCorrectionFallbackAfterSearch (q.checkpoint src hSrc).1.ge hr hj hGet
  suffices all : ∀ fuel first shuffles, p.batch-first = fuel → first < p.batch →
      ∀ cur : SchedulerWarpAt l X g 7810 (fun lane =>
        Correction.Fallback.groupSearchFacts p cta first lane (F lane)) shuffles 0 ends,
        cur.pos src ≤ j →
        ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4 * index), size := 4} by
    exact all _ 0 10 rfl hp.shape.1 first (hStart.symm ▸ hReady.symm ▸ hFollow.before)
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro b ord hFuel hb cur hLo
    rcases searchGroupToRecorded hp hX hg hCta hb hFrame hBase cur
      (src := src) (index := j) (target := ⟨7864,.exit⟩) (.inl hEnds) (by decide) with
      ⟨_,u,_,hInterval⟩ | ⟨hMore,⟨_,u,_,hInterval⟩ | ⟨_,u,_,hInterval⟩⟩
    · by_cases hHi : j < u.pos src
      · exact hInterval src hSrc j a bytes hLo hHi hGet
      · exact (done u (Nat.le_of_not_gt hHi)).elim
    · by_cases hHi : j < u.pos src
      · exact hInterval src hSrc j a bytes hLo hHi hGet
      · exact ih (p.batch-(b+31)) (by omega) (b+31) (ord+7) rfl hMore u (Nat.le_of_not_gt hHi)
    · by_cases hHi : j < u.pos src
      · exact hInterval src hSrc j a bytes hLo hHi hGet
      · exact (done u (Nat.le_of_not_gt hHi)).elim

/-- Every correction fallback lookup uses an in-range launch metadata word. -/
theorem correctionFallbackAddressesOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hComplete : ∀ Y, Maximal l kernel Assumptions.all m Y → Complete l Y) :
    CorrectionFallbackAddresses p X := by
  intro i a bytes hRead
  obtain ⟨g,j⟩ := i
  have he : X.get (g,j) = some ⟨7821,.rd a bytes⟩ := hRead
  have hg := event_thread_lt hX he
  have hRole := roleBodyPcOfEvent hp hX he (show 173 < 7821 by decide)
    (show 7821 ∉ registerHintSites by decide)
  have hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    change roleBodyPc (warpIndex l g) 7821 at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨Y,hXY,hMax⟩ := maximalExtension hp hX
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  exact correctionFallbackReadOfComplete hp hMax.1 (hComplete Y hMax)
    hg hw.1 hw.2 hl (hLane.symm ▸ Execution.le_get hXY he)

end PTX.Kernels.TmlFa4Fwd.Thread
