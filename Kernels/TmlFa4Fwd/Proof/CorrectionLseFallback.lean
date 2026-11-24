-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseFromSelected
public import Kernels.TmlFa4Fwd.Proof.CorrectionFallbackWarp
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
import Kernels.TmlFa4Fwd.Proof.CorrectionLseAfter
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Flow.Code.Part124

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Epilogue Prologue Mma

noncomputable section

private theorem emptyTileOut {l : Launch} {g : Nat} {t : TState}
    (hLo : 7932 ≤ t.pc) (hHi : t.pc < 7953) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  have hAll : ((kernel.code.drop 7932).take 21).all (fun i => Assumptions.coreOp i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  cases hc : kernel.code[t.pc]? with
  | none => simp only [out, hc]
  | some i =>
    have hm : i ∈ (kernel.code.drop 7932).take 21 := by
      apply List.mem_of_getElem? (i := t.pc - 7932)
      rwa [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
    apply Assumptions.out_all_eq_nil _ _ _ hc (List.all_eq_true.mp hAll _ hm)
    all_goals
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

/-- An exhausted correction scheduler goes locally to its terminal output-free acquire. -/
theorem exhaustedTileRun {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g lane : Nat} {t : TState}
    (ht : At t 7864 (Fallback.exhaustedScheduleFacts p (Fallback.fallbackFrame p l g lane))) :
    ∃ u, Relation.ReflTransGen
        (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 9201 [(7131, b32 (l.sharedBase + 232)), (7287, b32 1)] := by
  let thread := warpLane l g lane
  let F := Fallback.fallbackFrame p l g lane
  let S := [(1062, b32 (warpIndex l thread)), (1612, b32 (thread % l.block)),
    (1613, b32 (rowOf l thread)), (2535, b32 l.sharedBase)]
  have hAt : At t 7864 [(7273, b32 p.batch), (7277, b32 p.batch)] :=
    ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, trivial⟩
  have hSet : Seg kernel [] l thread 4 7864 [(7273, b32 p.batch), (7277, b32 p.batch)]
      7868 [(709, .pred true), (784, .pred false)] := by
    intro s hs
    have h32 : p.batch < 2 ^ 32 := by have := hp.shape.2.1; omega
    seg_fp hs using first | rfl | simp [compare, truncBits_ofNat h32 (by decide)]
  obtain ⟨u, hu, hU⟩ := hSet t hAt
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread)
    Flow.code_7868 true hU hU.2.2.2.2.1 (by simp)
  obtain ⟨hSelect, hFrame⟩ := groupLinear (regs := S.map Prod.fst) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) (run_comp hu hv)
  have hF : Holds t.regs F := ht.2.2.2.2.2.2
  have hS : Holds t.regs S :=
    ⟨holds_lookup hF (by rfl), holds_lookup hF (by rfl), holds_lookup hF (by rfl),
      holds_lookup hF (by rfl), trivial⟩
  have hCarry := holdsSchedulerFrame hS hFrame (fun _ hm => List.mem_map_of_mem hm)
  have hEntry : At v 7932 (S ++ [(784, .pred false)]) :=
    hV.mono ((holds_append _ _ _).2 ⟨hCarry, hV.2.2.2.2.2⟩)
  obtain ⟨s, hs, hS⟩ := correctionTileGeometry hp thread false v hEntry
  have hFlag := holds_lookup hS.2.2.2.2
    (show (correctionTileGeometryFacts l thread false).lookup 723 = some (.pred true) by rfl)
  obtain ⟨w, hw, hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread)
    Flow.code_7952 true hS hFlag (by simp)
  have hEnd : run kernel Assumptions.all l thread 21 v = some w :=
    schedulerLocalTransport (A := Assumptions.all) (lo := 7932) (len := 21)
      (by set_option maxRecDepth 100000 in kernel_rfl) emptyTileOut (run_comp hs hw)
      hEntry.1.ge (by rw [hEntry.1])
  have hRegisters : Holds w.regs (correctionTileGeometryFacts l thread false) := hW.2.2.2.2
  exact ⟨w, run_rtg (run_comp hSelect hEnd),
    hW.mono ⟨holds_lookup hRegisters (by rfl), holds_lookup hRegisters (by rfl), trivial⟩⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

theorem exhaustedCannotVisitEarlier (hp : Pre p l m) {g lane j shuffles votes : Nat}
    {ends : Nat → Option TState} {target : Event} (hPc : target.pc < 9201)
    (cur : SchedulerWarpAt l X g 7864
      (fun lane => Fallback.exhaustedScheduleFacts p (Fallback.fallbackFrame p l g lane))
      shuffles votes ends) (he : WarpFollowsEvent l X g cur.pos lane j target) : False := by
  obtain ⟨t, ht, hAt⟩ := exhaustedTileRun hp (cur.checkpoint lane he.lane)
  have hRun := (cur.continuation lane he.lane).after_local_nonempty
    ((cur.localSteps lane he.lane).trans ht) he.nonempty
  obtain ⟨visits, hWalk⟩ := walkFromRun hRun
  apply noEarlierCorrectionAfterStage (.inr (.inr rfl)) hPc hAt.1.ge
    (by rw [hAt.2.1]; decide) hWalk
  apply List.mem_of_getElem? (i := j - cur.pos lane)
  rw [List.getElem?_drop, Nat.add_sub_of_le he.before]
  exact he.get

theorem exhaustedCannotWrite (hp : Pre p l m) {g lane j pc shuffles votes : Nat}
    {ends : Nat → Option TState} {a : Acc} {bs : List Byte} (hPc : pc = 9073 ∨ pc = 9082)
    (cur : SchedulerWarpAt l X g 7864
      (fun lane => Fallback.exhaustedScheduleFacts p (Fallback.fallbackFrame p l g lane))
      shuffles votes ends) (he : WarpFollowsEvent l X g cur.pos lane j ⟨pc, .wr a bs⟩) : False := by
  exact exhaustedCannotVisitEarlier hp (show (Event.mk pc (.wr a bs)).pc < 9201 by
    dsimp only; omega) cur he

private theorem availableGroup {p : Params} {l : Launch} {X : Execution}
    {g first shuffles votes : Nat} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 7864
      (fun lane => Fallback.groupAvailableFacts p (g / l.block) first lane
        (Fallback.fallbackFrame p l g lane)) shuffles votes ends) :
    ∃ result : SchedulerWarpAt l X g 7864 (correctionGroupEntry p l g first) shuffles votes ends,
      result.pos = cur.pos := by
  apply cur.advanceLocalAt
  intro lane hl
  have ht := cur.checkpoint lane hl
  have h := ht.2.2.2.2
  have hPart := h.2.2.1
  rw [← prefixWindow_warp _ hl] at hPart
  exact ⟨_, .refl, ht.mono ⟨h.2.2.2.1, h.2.2.2.2.2.2.1, h.2.1, hPart,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩⟩

/-- The actual fallback chooses one request group or exhausts all available work. -/
theorem correctionFallbackGroupEvent (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane j shuffles votes : Nat} {ends : Nat → Option TState} {target : Event}
    (hg : g < l.threads)
    (cur : SchedulerWarpAt l X g 7807 (correctionFirstRouteFacts p l g) shuffles votes ends)
    (hFirst : tilePrefix p (min p.batch 31) * p.heads ≤ g / l.block) (hLate : 7859 < target.pc)
    (he : WarpFollowsEvent l X g cur.pos lane j target) :
    let cta := g / l.block
    (tilePrefix p p.batch * p.heads ≤ cta ∧
      ∃ sh, ∃ done : SchedulerWarpAt l X g 7864
        (fun lane => Fallback.exhaustedScheduleFacts p (Fallback.fallbackFrame p l g lane))
        sh votes ends, WarpFollowsEvent l X g done.pos lane j target) ∨
    ∃ first batch, first ≤ batch ∧ batch < first + 31 ∧ batch < p.batch ∧
      tilePrefix p batch * p.heads ≤ cta ∧ cta < tilePrefix p (batch + 1) * p.heads ∧
      ∃ sh, ∃ ready : SchedulerWarpAt l X g 7864 (correctionGroupEntry p l g first)
        sh votes ends, WarpFollowsEvent l X g ready.pos lane j target := by
  let cta := g / l.block
  let F := Fallback.fallbackFrame p l g
  have hCTA : cta < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hCta : cta + 1 < 2 ^ 32 := by have := hp.grid.2.2; omega
  obtain ⟨start, hPos⟩ := Fallback.startSearch hp hg hCta cur
  have hLoop (n first : Nat) (hn : p.batch - first = n) (hf : first < p.batch)
      (hLower : tilePrefix p (min p.batch (first + 31)) * p.heads ≤ cta)
      {sh : Nat}
      (s : SchedulerWarpAt l X g 7810 (fun lane => Fallback.groupSearchFacts p cta first lane
        (F lane)) sh votes ends)
      (hs : WarpFollowsEvent l X g s.pos lane j target) :
      (tilePrefix p p.batch * p.heads ≤ cta ∧
        ∃ sh, ∃ done : SchedulerWarpAt l X g 7864
          (fun lane => Fallback.exhaustedScheduleFacts p (F lane)) sh votes ends,
          WarpFollowsEvent l X g done.pos lane j target) ∨
      ∃ first batch, first ≤ batch ∧ batch < first + 31 ∧ batch < p.batch ∧
        tilePrefix p batch * p.heads ≤ cta ∧ cta < tilePrefix p (batch + 1) * p.heads ∧
        ∃ sh, ∃ ready : SchedulerWarpAt l X g 7864 (correctionGroupEntry p l g first)
          sh votes ends, WarpFollowsEvent l X g ready.pos lane j target := by
    induction n using Nat.strong_induction_on generalizing first sh with
    | h n ih =>
      have hBase : ∀ i < 32, (7506, b64 p.cuQBase) ∈ F i := by
        intro i hi
        exact List.mem_of_getElem? (i := 43) rfl
      have hr := Fallback.searchGroupTo hp hX hg hCTA hf
        (fun _ _ => Fallback.fallbackFrame_mem) hBase s (.inr hs) hLate
      rcases hr with ⟨hClip, done, hDone⟩ | ⟨hNext, ⟨hSkip, next, hKeep⟩ | ⟨hHere, found, hFound⟩⟩
      · have hAll : tilePrefix p p.batch * p.heads ≤ cta := by
          simpa only [Nat.min_eq_left hClip] using hLower
        exact .inl ⟨hAll, _, done, hDone hs⟩
      · exact ih (p.batch - (first + 31)) (by omega) (first + 31) rfl hNext hSkip next (hKeep hs)
      · let base := first + 31
        let stop := min p.batch (base + 31)
        have hBaseLower : tilePrefix p base * p.heads ≤ cta := by
          simpa only [base, Nat.min_eq_right hNext.le] using hLower
        have hAll : tilePrefix p stop * p.heads ≤ tilePrefix p p.batch * p.heads :=
          Nat.mul_le_mul_right p.heads (tilePrefix_mono p (Nat.min_le_left ..))
        obtain ⟨batch, ⟨hb, hLo, hHi⟩, _⟩ := tileBatch_existsUnique p (hHere.trans_le hAll)
        have hBeforeStop : batch < stop := by
          apply Nat.lt_of_not_ge
          intro hn
          have hMono := Nat.mul_le_mul_right p.heads (tilePrefix_mono p hn)
          exact (Nat.not_lt_of_ge (hMono.trans hLo)) hHere
        have hAfterBase : base ≤ batch := by
          by_contra! h
          have hBelow : batch + 1 ≤ base := by omega
          have hMono := Nat.mul_le_mul_right p.heads (tilePrefix_mono p hBelow)
          exact (Nat.not_lt_of_ge (hMono.trans hBaseLower)) hHi
        obtain ⟨selected, hSelected⟩ := availableGroup found
        exact .inr ⟨base, batch, hAfterBase, hBeforeStop.trans_le (Nat.min_le_right ..),
          hb, hLo, hHi, _, selected, hSelected.symm ▸ hFound hs⟩
  exact hLoop (p.batch - 0) 0 rfl hp.shape.1 hFirst start (hPos.symm ▸ he)

/-- Every visited fallback group either continues the scan, exits or selects its unique request.
A later write excludes the no-work exit and determines a valid LSE element. -/
theorem correctionFallbackLseStoreSpec (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g lane j pc shuffles votes : Nat}
    {ends : Nat → Option TState} {a : Acc} {bs : List Byte} (hg : g < l.threads)
    (cur : SchedulerWarpAt l X g 7807 (correctionFirstRouteFacts p l g) shuffles votes ends)
    (hFirst : tilePrefix p (min p.batch 31) * p.heads ≤ g / l.block) (hPc : pc = 9073 ∨ pc = 9082)
    (he : WarpFollowsEvent l X g cur.pos lane j ⟨pc, .wr a bs⟩) :
    AssignedLseFootprint p l (g / l.block) (warpLane l g lane) a := by
  rcases correctionFallbackGroupEvent hp hX hg cur hFirst
      (by change 7859 < pc; omega) he with
    ⟨_, _, done, hDone⟩ | ⟨first, batch, hBase, hGroup, hb, hLo, hHi, _, ready, hReady⟩
  · exact False.elim (exhaustedCannotWrite hp hPc done hDone)
  · exact correctionLseFootprintFromGroup hp hX hg hBase hGroup hb hLo hHi ready
      hPc hReady

/-- An actual correction writer in any launched CTA writes exactly one valid FP32 LSE element. -/
theorem correctionWarpLseStoreSpec (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane j pc : Nat} {a : Acc} {bs : List Byte} (hg : g < l.threads)
    (hLoWarp : 8 ≤ warpIndex l g) (hHiWarp : warpIndex l g < 12) (hl : lane < 32)
    (hPc : pc = 9073 ∨ pc = 9082) (he : X.get (warpLane l g lane, j) = some ⟨pc, .wr a bs⟩) :
    AssignedLseFootprint p l (g / l.block) (warpLane l g lane) a := by
  by_cases hFirst : g / l.block < tilePrefix p (min p.batch 31) * p.heads
  · exact correctionFirstGroupLseStoreSpec hp hX hg hLoWarp hHiWarp hl hFirst hPc he
  · have hRoute := correctionFirstRouteOfEvent hp hX hg hLoWarp hHiWarp hl
      (by change 7801 < pc; omega) he
    rw [ite_eq_right hFirst] at hRoute
    obtain ⟨ends, cur, hCur⟩ := hRoute
    exact correctionFallbackLseStoreSpec hp hX hg cur (Nat.le_of_not_gt hFirst) hPc hCur

/-- An actual correction event between selection and termination requires a scheduled tile. -/
theorem correctionWorkOfLateEvent (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane j : Nat} {target : Event} (hg : g < l.threads) (hLoWarp : 8 ≤ warpIndex l g)
    (hHiWarp : warpIndex l g < 12) (hl : lane < 32) (hLate : 7859 < target.pc)
    (hEarly : target.pc < 9201) (he : X.get (warpLane l g lane,j) = some target) :
    g / l.block < tilePrefix p p.batch * p.heads := by
  by_cases hFirst : g / l.block < tilePrefix p (min p.batch 31) * p.heads
  · exact hFirst.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (Nat.min_le_left ..)))
  · have hRoute := correctionFirstRouteOfEvent hp hX hg hLoWarp hHiWarp hl
      (by omega) he
    rw [ite_eq_right hFirst] at hRoute
    obtain ⟨ends, cur, hCur⟩ := hRoute
    rcases correctionFallbackGroupEvent hp hX hg cur (Nat.le_of_not_gt hFirst)
      hLate hCur with
      ⟨_, _, done, hDone⟩ | ⟨first, batch, _, _, hb, _, hHi, _⟩
    · exact (exhaustedCannotVisitEarlier hp hEarly done hDone).elim
    · exact hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))

end
end PTX.Kernels.TmlFa4Fwd.Correction
