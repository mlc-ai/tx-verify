-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncChain
public import Core.Assembly.Safety
public import Lemmas.MBarrier.MBarrierHistory
public import Lemmas.Async.AsyncMBarrier
public import Mathlib.Data.Fin.VecNotation

/-! Concrete input-slot reuse: the loader and MMA issuer are different threads.
Byte-level order between two asynchronous accesses relates operations performed by one
thread block (§8.9.5): the same chain of observed completions relates the load and the MMA
read when both threads share a CTA, and gives no `modelCausality` edge when they are in different
CTAs. The full/empty logs are real checked replays. No thread release carries the old TMA wait to
the new TMA issue; composition must go through the MMA read. -/
namespace PTX.Tests.AsyncReuse
open AsyncCopy
noncomputable section

private def launch : Launch := { grid := 1, block := 32, params := fun _ => none }
private def full : Loc := ⟨.shared, 0, 64⟩
private def empty : Loc := ⟨.shared, 0, 72⟩
private def byteLoc : Loc := ⟨.shared, 0, 0⟩
private def copy : TensorCopy.Spec :=
  ⟨⟨1, ⟨.f16, 4096, ![8, 1], ![16], ⟨![8, 1], ![1, 1]⟩, .b128, .zero, .small⟩,
    ![-16, 0], byteLoc, none⟩, full, false, .one⟩
private def observation : TensorCopy.Observation :=
  ⟨copy, { write := fun slot => some (.filled .zero .f16 slot.2.2.val), notified := true }⟩
private def smem : TcShared.Descriptor := ⟨0, 128, 256, 0, false, false, .none⟩
private def tcCopy : TcCopy.Spec := ⟨16, smem, .s128x256b, [0], none⟩
private def mma : TcMma.OperandSpec :=
  ⟨⟨.one, .i8 true true false, 128, 8, false, false, false, false, false⟩,
    smem, smem, 0, 0, none, {}⟩
private def commit : TcCommit.Spec := ⟨.one, empty, 1, 0, 1⟩
private def loader (waitAt : Loc) : List Event := [
  ⟨0, .mbInit full 1⟩, ⟨1, .arrive full 16 1 false .cta⟩,
  ⟨2, .tensorIssue 1024 copy⟩, ⟨3, .wait waitAt 0 true⟩,
  ⟨4, .tensorIssue 1024 copy⟩]
private def consumer : List Event := [
  ⟨0, .mbInit empty 1⟩, ⟨1, .wait full 0 true true .cluster⟩,
  ⟨2, .tc (.mma 0 mma false [0, 0, 0, 0])⟩,
  ⟨3, .tc (.commit (commit))⟩]
private def fullOps : List (Ref × MBarrier.Action) := [
  (.thread (0, 0), .init 1), (.thread (0, 1), .arrive 1 16),
  (.async (0, 2) (.notify .load), .completeTx 16), (.thread (1, 1), .pollParity 0 true)]
private def emptyOps : List (Ref × MBarrier.Action) := [
  (.thread (1, 0), .init 1), (.async (1, 3) (.tcNotify 0), .arrive 1 0),
  (.thread (0, 3), .pollParity 0 true)]
private def replayLog (ops : List (Ref × MBarrier.Action)) : List (MBarrier.Record Ref) :=
  match MBarrier.replay none ops with | .ok log => log | .error _ => []
private def execution (done : Bool) (waitAt : Loc) : Execution := {
  tr := fun g => if g = 0 then loader waitAt else if g = 1 then consumer else []
  rf := fun _ _ => none
  tensor := fun i => if i = (0, 2) then some observation else none
  async := {
    mmaOperands := fun i => if i = (1, 2) then
      some ⟨List.replicate 4096 (some ((.bits 8 0, 0))),
        List.replicate 256 (some ((.bits 8 0, 0)))⟩ else none
    mmaDone := fun i => decide (i = (1, 2)) && done }
  tcNotified := fun i => if i = (1, 3) ∧ done = true then {0} else ∅
  objects := fun l => if l = full then replayLog fullOps
    else if l = empty then replayLog emptyOps else [] }
private abbrev X := execution true empty

example : MBarrier.CheckedLog (replayLog fullOps) :=
  MBarrier.checkedLog_of_replay (ops := fullOps) rfl (by decide)
example : MBarrier.CheckedLog (replayLog emptyOps) :=
  MBarrier.checkedLog_of_replay (ops := emptyOps) rfl (by decide)

private theorem copy_observed :
    AsyncObserved X (0, 2) (.write (.load 0 0 0)) (1, 1) true .cluster := by
  refine ⟨.async (0, 2) (.notify .load), full, ⟨rfl, observation, 1024, rfl, ⟨2, rfl⟩, rfl, rfl⟩,
    ⟨⟨1, 0, rfl⟩, ?_⟩⟩
  exact ⟨2, 3, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      fun _ _ _ h2 _ => absurd h2 (by omega)⟩

private theorem mma_observed : AsyncObserved X (1, 2) (.mmaRead false 0) (0, 3) true .cta := by
  refine ⟨.async (1, 3) (.tcNotify 0), empty, ⟨(1, 3), commit, 0, rfl,
    ⟨rfl, by decide, .inl ⟨0, mma, false, [0, 0, 0, 0], 2, rfl⟩, commit, 3, rfl⟩, ⟨3, rfl⟩, rfl,
    Finset.mem_singleton.mpr rfl⟩, ⟨⟨3, 0, rfl⟩, ?_⟩⟩
  exact ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      fun _ _ _ h2 _ => absurd h2 (by omega)⟩

private theorem copy_covers (i : EvId) (hi : X.TensorIssue i 1024 copy) :
    AsyncCovers X i (.write (.load 0 0 0)) byteLoc := by
  refine ⟨{loc := byteLoc, size := 1}, true, ⟨rfl, copy, 1024, hi, rfl, rfl⟩, ?_⟩
  simp [Acc.Covers, Loc.InRange]
private theorem mma_covers : AsyncCovers X (1, 2) (.mmaRead false 0) byteLoc := by
  refine ⟨{loc := byteLoc, size := 1}, false,
    ⟨rfl, rfl, .inl ⟨0, mma, false, [0, 0, 0, 0], ⟨2, rfl⟩, rfl⟩⟩, ?_⟩
  simp [Acc.Covers, Loc.InRange]
private theorem mma_present : X.AsyncPresent (1, 2) (.mmaRead false 0) :=
  ⟨byteLoc, some ((.bits 8 0, 0)), .inl ⟨0, mma, false, [0, 0, 0, 0], ⟨2, rfl⟩, rfl⟩, _, rfl, rfl⟩

private theorem copy_to_mma : modelCausality launch X byteLoc
    (.async (0, 2) (.write (.load 0 0 0))) (.async (1, 2) (.mmaRead false 0)) :=
  ⟨.inl (by unfold SameCta Launch.threads launch; decide),
    .direct ⟨copy_covers _ ⟨2, rfl⟩, mma_covers,
    .inl ⟨(1, 1), .inr ⟨.cluster, copy_observed, by simp [ScopesMeet, MbarScopeIncludes,
      SameCluster, launch, Launch.threads, Launch.clusterOfCta]⟩,
      .single (.inl ⟨rfl, by decide, by decide⟩)⟩⟩⟩
private theorem mma_to_copy : modelCausality launch X byteLoc
    (.async (1, 2) (.mmaRead false 0)) (.async (0, 4) (.write (.load 0 0 0))) :=
  ⟨.inl (by unfold SameCta Launch.threads launch; decide),
    .direct ⟨mma_covers, copy_covers _ ⟨4, rfl⟩,
    .inl ⟨(0, 3), .inr ⟨.cta, mma_observed, by simp [ScopesMeet, MbarScopeIncludes, SameCta,
      SameCluster, launch, Launch.threads, Launch.clusterOfCta]⟩,
      .single (.inl ⟨rfl, by decide, by decide⟩)⟩⟩⟩

/-- Both generations use the same byte, through the actual intervening MMA read. -/
theorem reuse_ordered : modelCausality launch X byteLoc
    (.async (0, 2) (.write (.load 0 0 0))) (.async (0, 4) (.write (.load 0 0 0))) :=
  modelCausality_async_trans copy_to_mma mma_present mma_to_copy
    (.inl (by simp [SameCta, launch, Launch.threads]))

/-! ## An ordinary store reuses the completed MMA's shared operand. -/

private def narrow : Acc := { loc := byteLoc, size := 1 }
private def wide : Acc := { loc := byteLoc, size := 4 }
private def loadByte : Ref := .async (0, 2) (.write (.load 0 0 0))
private def storeWord : Ref := .thread (0, 4)

/-- The last tensor issue is replaced by an ordinary access to the same byte. -/
private def loaderWithAccess (acquire store : Bool) : List Event :=
  (loader empty).take 3 ++ [⟨3, .wait empty 0 true acquire .cluster⟩,
    ⟨4, if store then .wr wide (List.replicate 4 (.bits 8 0, 0))
      else .rd wide (List.replicate 4 (some (.bits 8 0, 0)))⟩]

private abbrev loaderWithStore := loaderWithAccess false true

private def operandConsumer (isCopy : Bool) : List Event :=
  if isCopy then consumer.set 2 ⟨2, .tc (.cp tcCopy)⟩ else consumer

private def handoffOperands (isCopy : Bool) (i : EvId) : Option MmaOperands :=
  if isCopy = true ∧ i = (1, 2) then
    some ⟨List.replicate 4096 (some (.bits 8 0, 0)), []⟩
  else X.async.mmaOperands i

private def operandHandoff (isCopy acquire store : Bool) : Execution :=
  { X with
    tr := fun g =>
      if g = 0 then loaderWithAccess acquire store
      else if g = 1 then operandConsumer isCopy else []
    async := { X.async with mmaOperands := handoffOperands isCopy } }

private abbrev handoff := operandHandoff false false true

private theorem handoff_written : handoff.Intent loadByte narrow true :=
  ⟨rfl, copy, 1024, ⟨2, rfl⟩, rfl, rfl⟩

private theorem handoff_word : handoff.Intent storeWord wide true :=
  .inr (.inl ⟨_, ⟨4, rfl⟩, rfl⟩)

private theorem handoff_prior {isCopy acquire store : Bool}
    (hread : (operandHandoff isCopy acquire store).MmaFootprint (1, 2) false 0 byteLoc) :
    modelCausality launch (operandHandoff isCopy acquire store) byteLoc loadByte
      (.async (1, 2) (.mmaRead false 0)) := by
  have hpo : po (operandHandoff isCopy acquire store) (1, 1) (1, 2) := by
    refine ⟨rfl, by decide, ?_, ?_⟩
    · cases isCopy <;> change 2 < 4 <;> decide
    · intro h
      have hn := h.1
      cases isCopy <;> change false = true at hn <;> cases hn
  have hcover : narrow.Covers byteLoc := by simp [narrow, Acc.Covers, Loc.InRange]
  refine ⟨.inl (by unfold SameCta Launch.threads launch; decide),
    .direct ⟨⟨narrow, true, ⟨rfl, copy, 1024, ⟨2, rfl⟩, rfl, rfl⟩, hcover⟩,
      ⟨narrow, false, ⟨rfl, rfl, hread⟩, hcover⟩,
      .inl ⟨(1, 1), .inr ⟨.cluster, ?_, ?_⟩, .single (.inl hpo)⟩⟩⟩
  · refine ⟨.async (0, 2) (.notify .load), full,
      ⟨rfl, observation, 1024, rfl, ⟨2, rfl⟩, rfl, rfl⟩, ⟨⟨1, 0, ?_⟩, ?_⟩⟩
    · cases isCopy <;> rfl
    · exact ⟨2, 3, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
        fun _ _ _ h2 _ => absurd h2 (by omega)⟩
  · simp [ScopesMeet, MbarScopeIncludes, SameCluster, launch, Launch.threads, Launch.clusterOfCta]

private theorem handoff_observed {isCopy acquire store : Bool}
    (htracks : TracksMma (operandHandoff isCopy acquire store) (1, 2) (1, 3)) :
    AsyncObserved (operandHandoff isCopy acquire store) (1, 2) .mmaDone
      (0, 3) acquire .cluster := by
  refine ⟨.async (1, 3) (.tcNotify 0), empty, ⟨(1, 3), commit, 0, rfl,
    htracks, ⟨3, ?_⟩, rfl, Finset.mem_singleton.mpr rfl⟩, ⟨⟨3, 0, rfl⟩, ?_⟩⟩
  · cases isCopy <;> rfl
  · exact ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      fun _ _ _ h _ => absurd h (by omega)⟩

private theorem handoff_order : ByteCausality launch handoff byteLoc loadByte storeWord := by
  refine .commitOperand rfl ⟨narrow, handoff_written, ?_⟩
    (.inl ⟨0, mma, false, [0, 0, 0, 0], 2, rfl⟩)
    ⟨some (.bits 8 0, 0), .inl ⟨0, mma, false, [0, 0, 0, 0], ⟨2, rfl⟩, rfl⟩, _, rfl, rfl⟩
    (.direct (handoff_prior (.inl ⟨0, mma, false, [0, 0, 0, 0], ⟨2, rfl⟩, rfl⟩)))
    ⟨.cluster, handoff_observed
      ⟨rfl, by decide, .inl ⟨0, mma, false, [0, 0, 0, 0], 2, rfl⟩, commit, 3, rfl⟩, ?_⟩
    ⟨rfl, by decide, by decide, ?_⟩ ⟨wide, .inl ⟨true, handoff_word⟩, ?_⟩
  · simp [narrow, Acc.Covers, Loc.InRange]
  · simp [ScopesMeet, MbarScopeIncludes, SameCluster, launch, Launch.threads,
      Launch.clusterOfCta]
  · intro h
    have hs := h.2 1 (by decide)
    change some wide = none at hs
    cases hs
  · simp [wide, Acc.Covers, Loc.InRange]

private theorem handoff_event {isCopy acquire store : Bool} {e : EvId} {ev : Event}
    (h : (operandHandoff isCopy acquire store).get e = some ev) :
    ev ∈ loaderWithAccess acquire store ∨ ev ∈ operandConsumer isCopy := by
  change (if e.1 = 0 then _ else if e.1 = 1 then operandConsumer isCopy else [])[e.2]? =
    some ev at h
  split_ifs at h
  · exact .inl (List.mem_of_getElem? h)
  · exact .inr (List.mem_of_getElem? h)
  · cases h

private theorem handoff_base_stays_in_thread {isCopy acquire store : Bool} {e f : EvId}
    (h : baseCausality launch (operandHandoff isCopy acquire store) e f) : e.1 = f.1 := by
  let handoff := operandHandoff isCopy acquire store
  have step : ∀ e f, (po handoff e f ∨ CtaBarSync launch handoff e f ∨ MSync launch handoff e f ∨
      ClusterSync launch handoff e f ∨ WarpBarSync launch handoff e f ∨
      synchronizesWith launch handoff e f ∨ FenceSync launch handoff e f) → e.1 = f.1 := by
    rintro e f (h | h | h | h | h | h | h)
    · exact h.1
    · obtain ⟨-, key, i, j, -, ⟨-, ⟨count, pc, hj⟩, -⟩, -⟩ := h
      rcases handoff_event hj with hc | hc
      · cases store <;> simp [loaderWithAccess, loader] at hc
      · cases isCopy <;> simp [operandConsumer, consumer] at hc
    · obtain ⟨x, w, m, rs, ws, ⟨tx, count, pc, hx⟩, -⟩ := h
      rcases handoff_event hx with hc | hc
      · cases store <;> simp [loaderWithAccess, loader] at hc
      · cases isCopy <;> simp [operandConsumer, consumer] at hc
    · obtain ⟨-, i, j, ⟨phase, ⟨idx, st, next, cta, warp, lanes, g, hi, -⟩, -⟩, -⟩ := h
      change [][idx]? = some _ at hi
      simp at hi
    · obtain ⟨i, j, ⟨-, mask, inst, ⟨pc, hi⟩, -⟩, -⟩ := h
      rcases handoff_event hi with hc | hc
      · cases store <;> simp [loaderWithAccess, loader] at hc
      · cases isCopy <;> simp [operandConsumer, consumer] at hc
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, hsize, _, _, hrf⟩ := h
      have hn := hrf 0 hsize
      change none = _ at hn
      cases hn
    · apply False.elim (not_fenceSync_of_noFence (X := handoff) ?_ _ _ h)
      rintro i sem sc ⟨pc, hi⟩
      rcases handoff_event hi with hc | hc
      · cases store <;> simp [loaderWithAccess, loader] at hc
      · cases isCopy <;> simp [operandConsumer, consumer] at hc
  induction h with
  | single h => exact step _ _ h
  | tail _ h ih => exact ih.trans (step _ _ h)

/-- The TMA completion has no path to the wider store in the base proxy rules. -/
private theorem handoff_no_direct {isCopy acquire store : Bool} :
    ¬ modelCausality launch (operandHandoff isCopy acquire store) byteLoc loadByte storeWord := by
  rintro ⟨-, w, h, hb⟩
  have hg : w.1 = 0 := handoff_base_stays_in_thread
    (by simpa only [ObservedCompletionBefore, CompletionBefore, TcReadReuseBefore, or_false]
      using hb)
  have htr : (operandHandoff isCopy acquire store).tr w.1 = loaderWithAccess acquire store :=
    congrArg (operandHandoff isCopy acquire store).tr hg
  rcases h with ⟨k, -, h, -⟩ | ⟨scope, ⟨n, m, hn, ⟨⟨pc, parity, hw⟩, _⟩⟩, -⟩
  · cases k <;> obtain ⟨pc, count, hi, -⟩ := h
    all_goals
      have he := List.mem_of_getElem? hi
      rw [htr] at he
      cases store <;> simp [loaderWithAccess, loader] at he
  · obtain ⟨-, o, addr, ho, -, hm, -⟩ := hn
    change some observation = some o at ho
    cases ho
    have hm' : m = full := hm.symm
    rw [hm'] at hw
    have he := List.mem_of_getElem? hw
    rw [htr] at he
    cases store <;> simp [loaderWithAccess, loader, full, empty] at he

/-- The store also cannot publish backwards to the TMA in the base proxy rules. -/
example : ¬ modelCausality launch handoff byteLoc storeWord loadByte := by
  have hn : ¬ GenericCopy handoff (0, 2) := by
    rintro ⟨s, ⟨pc, h⟩, -⟩
    change some (⟨2, .tensorIssue 1024 copy⟩ : Event) = _ at h
    cases h
  unfold storeWord loadByte
  rw [modelCausality_thread_async_of_not_generic launch hn]
  rintro ⟨-, f, sp, sc, ⟨pc, hf⟩, -⟩
  rcases handoff_event hf with h | h <;>
    simp [loaderWithAccess, loader, operandConsumer, consumer] at h

/-- The load and store are a genuine different-footprint conflict in this trace. -/
example : Conflict handoff loadByte storeWord narrow wide ∧ ¬ narrow.SameFootprint wide := by
  refine ⟨⟨by decide, true, true, handoff_written, handoff_word, .inl rfl, byteLoc, ?_, ?_⟩,
    fun h => absurd h.2 (by decide)⟩
  · simp [narrow, Acc.Covers, Loc.InRange]
  · simp [wide, Acc.Covers, Loc.InRange]

/-- A `Mixed` witness for this trace may not select the load byte and the post-wait store. -/
example (other : ∀ e f a b l, Conflict handoff e f a b → ¬ a.SameFootprint b →
    a.Covers l → b.Covers l →
    (e = loadByte ∧ f = storeWord ∧ l = byteLoc) ∨
    (f = loadByte ∧ e = storeWord ∧ l = byteLoc) ∨
    ByteCausality launch handoff l e f ∨ ByteCausality launch handoff l f e) :
    ¬ Mixed launch handoff := by
  rintro ⟨e, f, a, b, l, hc, hsize, ha, hb, hef, hfe⟩
  rcases other e f a b l hc hsize ha hb with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | h | h
  · exact hef handoff_order
  · exact hfe handoff_order
  · exact hef h
  · exact hfe h

/-- Two single-thread CTAs, each in its own cluster: no `cta_group::2` pair. The loader is
CTA 0 and the MMA issuer, which also observes the load's completion through the full barrier,
is CTA 1. -/
private def launch2 : Launch := { grid := 2, block := 1, params := fun _ => none }

/-- The same two single-thread CTAs as the two CTAs of one `cta_group::2` pair. -/
private def launchPair : Launch :=
  { grid := 2, block := 1, params := fun _ => none, clusterSize := ⟨2, by decide⟩ }

private theorem cross_chain {L : Launch} (hm : ScopesMeet L .cluster 0 .cluster 1) :
    AsyncChain L X byteLoc
    ((0, 2), .write (.load 0 0 0)) ((1, 2), .mmaRead false 0) :=
  .direct ⟨copy_covers _ ⟨2, rfl⟩, mma_covers,
    .inl ⟨(1, 1), .inr ⟨.cluster, copy_observed, hm⟩,
      .single (.inl ⟨rfl, by decide, by decide⟩)⟩⟩

/-- The two CTAs of `launchPair` and the byte form one `cta_group::2` pair. -/
example : PairAsync launchPair byteLoc 0 1 :=
  ⟨rfl, by
      simp only [SameCtaGroup, CtaInCluster, launchPair]
      decide,
    by
      simp only [SameCtaGroup, CtaInCluster, launchPair, byteLoc]
      decide⟩

/-- Inside one `cta_group::2` pair there is a chain of observed completions from the load of CTA 0
to the MMA read of CTA 1. -/
theorem pair_cta_chain : AsyncChain launchPair X byteLoc
    ((0, 2), .write (.load 0 0 0)) ((1, 2), .mmaRead false 0) :=
  cross_chain (by
    simp only [ScopesMeet, MbarScopeIncludes, SameCluster, launchPair, Launch.threads]
    decide)


/-- Outside a pair, the tensor write issued by CTA 0 is not byte-ordered before the MMA read of
CTA 1: the endpoints are not performed by one thread block. -/
theorem cross_cta_not_vis : ¬ modelCausality launch2 X byteLoc
    (.async (0, 2) (.write (.load 0 0 0))) (.async (1, 2) (.mmaRead false 0)) := by
  rintro ⟨h | h, -⟩
  · simp [SameCta, launch2] at h
  · obtain ⟨⟨-, h, -⟩, -⟩ := h
    simp only [SameCtaGroup, CtaInCluster, launch2] at h
    exact absurd h (by decide)

private theorem no_mma_handoff_to_consumer {i w : EvId} {acq : Bool} {scope : MbarScope}
    (h : AsyncObserved X i .mmaDone w acq scope) (hw : po X w (1, 2)) : False := by
  obtain ⟨n, m, ⟨c, s, rank, -, -, ⟨pc, hc⟩, ht, hn⟩, ⟨⟨q, parity, hq⟩, -⟩⟩ := h
  have hn' : c = (1, 3) ∧ rank = 0 := by
    change rank ∈ (if c = (1, 3) ∧ true = true then {0} else ∅ : Finset (Fin 16)) at hn
    by_cases h : c = (1, 3)
    · exact ⟨h, by simpa [h] using hn⟩
    · simp [h] at hn
  obtain ⟨rfl, rfl⟩ := hn'
  change some (⟨3, .tc (.commit commit)⟩ : Event) = _ at hc
  cases hc
  have hm : m = empty := by
    have htarget : TcCommit.target commit 0 = some empty := rfl
    exact Option.some.inj (ht.symm.trans htarget)
  subst m
  obtain ⟨g, j⟩ := w
  have hg : g = 1 := hw.1
  subst g
  have hj : j < 2 := hw.2.1
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · change some (⟨0, .mbInit empty 1⟩ : Event) = _ at hq
    cases hq
  · change some (⟨1, .wait full 0 true true .cluster⟩ : Event) = _ at hq
    have := congrArg (fun e : Option Event => e.map (·.kind)) hq
    simp [empty, full] at this

/-- Nor is it ordered the other way, so the load and the read are a data race. -/
theorem cross_cta_race : Race launch2 X := by
  refine ⟨.async (0, 2) (.write (.load 0 0 0)), .async (1, 2) (.mmaRead false 0),
    {loc := byteLoc, size := 1}, {loc := byteLoc, size := 1}, byteLoc, ⟨by simp, true, false,
      ⟨rfl, copy, 1024, ⟨2, rfl⟩, rfl, rfl⟩, ⟨rfl, rfl,
        .inl ⟨0, mma, false, [0, 0, 0, 0], ⟨2, rfl⟩, rfl⟩⟩,
      Or.inl rfl, byteLoc, by simp [Acc.Covers, Loc.InRange], by simp [Acc.Covers, Loc.InRange]⟩,
    ⟨rfl, rfl⟩, by simp [Acc.Covers, Loc.InRange],
    ?_, ?_, ?_, fun ⟨_, ⟨h, _⟩, _⟩ => nomatch h⟩
  · rintro ⟨⟨i, j, h, -⟩ | ⟨h, -⟩, -⟩
    · cases h
    · exact h
  · intro h
    cases h with
    | direct h => exact cross_cta_not_vis h
    | commitOperand _ _ _ _ _ observed next =>
      obtain ⟨scope, ho, -⟩ := observed
      exact no_mma_handoff_to_consumer ho next
  · rw [ByteCausality.direct_iff_of_not_write]
    · rintro ⟨h | h, -⟩
      · simp [SameCta, launch2] at h
      · obtain ⟨⟨-, -, ⟨-, h⟩, -⟩, -⟩ := h
        exact absurd h (by decide)
    · rintro a ⟨h, -⟩
      cases h

private theorem event_cases {done : Bool} {waitAt : Loc} {i : EvId} {ev : Event}
    (h : (execution done waitAt).get i = some ev) :
    ev ∈ loader waitAt ∨ ev ∈ consumer := by
  change (if i.1 = 0 then loader waitAt else if i.1 = 1 then consumer else [])[i.2]? = some ev at h
  split_ifs at h
  · exact .inl (List.mem_of_getElem? h)
  · exact .inr (List.mem_of_getElem? h)
  · cases h

/-- Neither the load nor the MMA is a `cta_group::2` operation (the MMA has `.cta_group::1`). -/
private theorem no_pairTc (i : EvId) : ¬ PairTc X i := by
  rintro (⟨d, s, acc, mask, ⟨pc, h⟩, hg⟩ | ⟨c, ⟨pc, h⟩, -⟩)
  · rcases event_cases h with h | h <;> simp [loader, consumer] at h
    obtain ⟨-, -, rfl, -⟩ := h
    simp [mma] at hg
  · rcases event_cases h with h | h <;> simp [loader, consumer] at h

/-- So the chain does not order them: the CTAs form a pair, but EXT-PAIR-ASYNC covers only an
order with a `cta_group::2` `tcgen05` operation at one end. -/
theorem pair_cta_one_unordered : ¬ modelCausality launchPair X byteLoc
    (.async (0, 2) (.write (.load 0 0 0))) (.async (1, 2) (.mmaRead false 0)) := by
  rintro ⟨h | ⟨-, h | h⟩, -⟩
  · simp [SameCta, launchPair] at h
  · exact no_pairTc _ h
  · exact no_pairTc _ h

private theorem baseCausality_same_thread {done : Bool} {waitAt : Loc} {e f : EvId}
    (h : baseCausality launch (execution done waitAt) e f) : e.1 = f.1 := by
  have noFence : ∀ e sem s, ¬ (execution done waitAt).ThreadFence e sem s := by
    intro e sem s hf
    obtain ⟨pc, he⟩ := hf
    have hmem := event_cases he
    simp [loader, consumer] at hmem
  have base {e f : EvId}
      (h : po (execution done waitAt) e f ∨ CtaBarSync launch (execution done waitAt) e f ∨
        MSync launch (execution done waitAt) e f ∨
        ClusterSync launch (execution done waitAt) e f ∨
        WarpBarSync launch (execution done waitAt) e f ∨
        synchronizesWith launch (execution done waitAt) e f ∨
        FenceSync launch (execution done waitAt) e f) : e.1 = f.1 := by
    rcases h with h | h | h | h | h | h | h
    · exact h.1
    · obtain ⟨-, key, i, j, ⟨-, ⟨count, pc, mode, hg⟩, -⟩, -, -, -, -⟩ := h
      have hmem := event_cases hg
      simp [loader, consumer] at hmem
    · obtain ⟨x, w, m, rs, as_, ⟨tx, count, pc, hg⟩, -, -, -, -, -, -, -⟩ := h
      have hmem := event_cases hg
      simp [loader, consumer] at hmem
    · obtain ⟨-, i, j, hs, -, -, -⟩ := h
      obtain ⟨phase, harr, -⟩ := hs
      obtain ⟨k, s, t, cta, warp, lanes, g, hnil, -⟩ := harr
      have hempty : (execution done waitAt).clusters
          (launch.clusterOfCta (e.1 / launch.block)) = [] := rfl
      rw [hempty] at hnil
      simp at hnil
    · obtain ⟨i, j, ⟨-, mask, inst, ⟨pc, hg⟩, -⟩, -, -, -⟩ := h
      have hmem := event_cases hg
      simp [loader, consumer] at hmem
    · obtain ⟨a, b, bs, cs, hw, -, -, -, -, -, -, -, -, -⟩ := h
      rcases hw with ⟨pc, hg⟩ | ⟨old, ⟨pc, hg⟩⟩
      · have hmem := event_cases hg
        simp [loader, consumer] at hmem
      · have hmem := event_cases hg
        simp [loader, consumer] at hmem
    · exact absurd h (not_fenceSync_of_noFence (L := launch) noFence e f)
  induction h with
  | single h => exact base h
  | tail _ h ih => exact ih.trans (base h)

private theorem full_wait_thread {done : Bool} {waitAt : Loc} {w : EvId}
    (hw : waitAt ≠ full) (h : (execution done waitAt).AcquireWait w full) : w.1 = 1 := by
  obtain ⟨pc, parity, scope, he⟩ := h
  change (if w.1 = 0 then loader waitAt else if w.1 = 1 then consumer else [])[w.2]? =
    some ⟨pc,.wait full parity true true scope⟩ at he
  split_ifs at he with hzero hone
  · have hm := List.mem_of_getElem? he
    simp [loader, Ne.symm hw] at hm
  · exact hone
  · cases he

/-- No bulk-group or `cp.async`-group wait occurs in either thread. -/
private theorem no_group_wait {done : Bool} {waitAt : Loc} {k : GroupWait} {i w : EvId} :
    ¬ GroupWaitsFor (execution done waitAt) k i w := by
  cases k with
  | bulk mode =>
    rintro ⟨pc, remaining, hw, -⟩
    have hcases := event_cases hw
    simp [loader, consumer] at hcases
  | cpAsync =>
    rintro ⟨pc, remaining, hw, -⟩
    have hcases := event_cases hw
    simp [loader, consumer] at hcases

/-- A wait that observes the load's notification is CTA 1's wait on the full barrier. -/
private theorem tensor_wait_thread {done : Bool} {waitAt : Loc} {i w : EvId}
    {o : TensorCopy.Observation} (hw : waitAt ≠ full)
    (ho : (execution done waitAt).tensor i = some o) {pc parity : Nat} {ws : MbarScope}
    (he : (execution done waitAt).get w = some ⟨pc, .wait o.spec.mbar parity true true ws⟩) :
    w.1 = 1 := by
  change (if i=(0,2) then some observation else none)=some o at ho
  have hi : i=(0,2) := by
    by_cases hn : i=(0,2)
    · exact hn
    · rw [ite_eq_right hn] at ho; cases ho
  subst i
  have hs : o = observation := Option.some.inj ho.symm
  subst hs
  exact full_wait_thread hw ⟨pc, parity, ws, he⟩

private theorem no_async_only {done : Bool} {waitAt : Loc} {i w : EvId} {p : Part} :
    ¬ AsyncOnlyFinished (execution done waitAt) i p w := by
  rintro ⟨-, hgw, -⟩
  exact no_group_wait hgw

/-- The new edge cannot be obtained by accidentally publishing the issuing thread. -/
example : ¬ AsyncBefore launch X byteLoc
    ((0, 2), .write (.load 0 0 0)) ((0, 4), .write (.load 0 0 0)) := by
  rintro ⟨-, -, ⟨w, ⟨k, -, hgw, -⟩ | ⟨ws, ⟨n, m, hn, hwo⟩, -⟩, hh⟩ | ⟨w, hf, -⟩⟩
  · exact absurd hgw no_group_wait
  · simp only [AsyncCopy.Notifies, AsyncCopy.Part.target] at hn
    obtain ⟨o, a, ho, -, rfl, -⟩ := hn.2
    obtain ⟨pc, parity, he⟩ := hwo.1
    have ht := tensor_wait_thread (by decide : empty ≠ full) ho he
    have hs := baseCausality_same_thread hh
    rw [ht] at hs
    contradiction
  · exact no_async_only hf

private def wrong : Loc := ⟨.shared, 0, 80⟩

private theorem no_mma_observation {done : Bool} {waitAt : Loc} {c w : EvId} {s : TcCommit.Spec}
    {rank : Fin 16} {m : Loc} (hmode : done=false ∨ waitAt=wrong)
    (hc : (execution done waitAt).Commit c s) (ht : TcCommit.target s rank = some m)
    (hn : rank ∈ (execution done waitAt).tcNotified c)
    (hw : (execution done waitAt).AcquireWait w m) : False := by
  change rank ∈ (if c=(1,3) ∧ done=true then {0} else ∅) at hn
  rcases hmode with rfl | rfl
  · simp at hn
  · have hci : c=(1,3) := by
      by_cases h : c=(1,3)
      · exact h
      · simp [h] at hn
    subst c
    have hs : s=commit := by
      obtain ⟨pc,he⟩ := hc
      cases he
      rfl
    subst s
    have hrank : rank=0 := by
      by_cases hd : done=true
      · simpa only [hd, and_self, ite_true, Finset.mem_singleton] using hn
      · simp [hd] at hn
    subst rank
    have hm : empty=m := Option.some.inj ht
    subst m
    obtain ⟨pc,parity,scope,he⟩ := hw
    have hcases := event_cases he
    simp [loader,consumer,wrong,full,empty] at hcases

private theorem finish_wait_thread {done : Bool} {waitAt : Loc} {i w : EvId} {p : Part}
    (hmode : done=false ∨ waitAt=wrong) (hw : waitAt≠full)
    (h : AsyncFinished L (execution done waitAt) i p w) : w.1=1 := by
  have noCopy {m : Loc} {bytes : Nat}
      (hn : Notification (issuedBy (execution done waitAt))
        (execution done waitAt).async i m bytes) : False := by
    obtain ⟨s, hi, -⟩ := hn
    obtain ⟨pc, he⟩ := issuedBy_some.mp hi
    have hcases := event_cases he
    simp [loader, consumer] at hcases
  have noNotifyCopy {m : Loc} (h2 : NotifyOn (execution done waitAt) i .copy m) : False := by
    obtain ⟨bytes, hn'⟩ := h2
    exact noCopy hn'
  rcases h with ⟨k, -, hgw, -⟩ | ⟨ws, ⟨n, m, hn, hwo⟩, -⟩
  · exact absurd hgw no_group_wait
  · obtain ⟨pc, parity, he⟩ := hwo.1
    cases p with
    | mmaRead isB byte =>
      obtain ⟨c, s, rank, -, ⟨-, -, -, -⟩, hcomm, htarget, hmem⟩ := hn
      exact (no_mma_observation hmode hcomm htarget hmem ⟨pc, parity, ws, he⟩).elim
    | mmaDone =>
      obtain ⟨c, s, rank, -, ⟨-, -, -, -⟩, hcomm, htarget, hmem⟩ := hn
      exact (no_mma_observation hmode hcomm htarget hmem ⟨pc, parity, ws, he⟩).elim
    | readCopy =>
      simp only [AsyncCopy.Notifies] at hn
      rcases hn with ⟨-, h2⟩ | ⟨j, noinc, -, htracks, -, -⟩
      · exact (noNotifyCopy h2).elim
      · obtain ⟨-, -, ⟨s', ⟨pc', he'⟩, -⟩, -, -, -⟩ := htracks
        have hcases := event_cases he'
        simp [loader, consumer] at hcases
    | readLoad =>
      simp only [AsyncCopy.Notifies, AsyncCopy.Part.target] at hn
      obtain ⟨-, o, a, ho, -, rfl, -⟩ := hn
      exact tensor_wait_thread hw ho he
    | readStore => exact hn.elim
    | readCta => exact hn.elim
    | readElem => exact hn.elim
    | readPrefetch => exact hn.elim
    | writeCopy =>
      simp only [AsyncCopy.Notifies] at hn
      rcases hn with ⟨-, h2⟩ | ⟨j, noinc, -, htracks, -, -⟩
      · exact (noNotifyCopy h2).elim
      · obtain ⟨-, -, ⟨s', ⟨pc', he'⟩, -⟩, -, -, -⟩ := htracks
        have hcases := event_cases he'
        simp [loader, consumer] at hcases
    | writeLoad =>
      simp only [AsyncCopy.Notifies, AsyncCopy.Part.target] at hn
      obtain ⟨-, o, a, ho, -, rfl, -⟩ := hn
      exact tensor_wait_thread hw ho he
    | writeStore => exact hn.elim
    | writeCta =>
      simp only [AsyncCopy.Notifies, AsyncCopy.Part.target] at hn
      obtain ⟨s, targets, hclc, -, -, -⟩ := hn.2
      obtain ⟨pc', he'⟩ := hclc
      have hcases := event_cases he'
      simp [loader, consumer] at hcases
    | writeElem =>
      simp only [AsyncCopy.Notifies, AsyncCopy.Part.target] at hn
      exact (noNotifyCopy hn.2).elim
    | writePrefetch => exact hn.elim
    | oldCopy => exact hn.elim
    | oldLoad => exact hn.elim
    | oldStore => exact hn.elim
    | oldCta => exact hn.elim
    | oldElem =>
      simp only [AsyncCopy.Notifies, AsyncCopy.Part.target] at hn
      exact (noNotifyCopy hn.2).elim
    | oldPrefetch => exact hn.elim
    | notifyCopy =>
      simp only [AsyncCopy.Notifies, AsyncCopy.Part.target] at hn
      exact (noNotifyCopy hn.2).elim
    | notifyLoad =>
      simp only [AsyncCopy.Notifies, AsyncCopy.Part.target] at hn
      obtain ⟨-, o, a, ho, -, rfl, -⟩ := hn
      exact tensor_wait_thread hw ho he
    | notifyCta =>
      simp only [AsyncCopy.Notifies, AsyncCopy.Part.target] at hn
      obtain ⟨s, targets, hclc, -, -, -⟩ := hn.2
      obtain ⟨pc', he'⟩ := hclc
      have hcases := event_cases he'
      simp [loader, consumer] at hcases
    | readsDone => exact hn.elim
    | fullDone => exact hn.elim
    | resolve => exact hn.elim
    | tcNotify rank => exact hn.elim
    | arriveOn => exact hn.elim

private theorem reuse_rejected {done : Bool} {waitAt : Loc}
    (hmode : done=false ∨ waitAt=wrong) (hw : waitAt≠full) :
    ¬ modelCausality launch (execution done waitAt) byteLoc
      (.async (0,2) (.write (.load 0 0 0))) (.async (0,4) (.write (.load 0 0 0))) := by
  have noEdge {a b : EvId × Part} (hb : b.1.1 = 0) :
      ¬ AsyncBefore launch (execution done waitAt) byteLoc a b := by
    rintro ⟨-, -, ⟨w, hf, hh⟩ | ⟨w, hf, -⟩⟩
    · have ht := finish_wait_thread hmode hw hf
      have hs := baseCausality_same_thread hh
      rw [ht, hb] at hs
      contradiction
    · exact no_async_only hf
  rintro ⟨_, h⟩
  obtain h | ⟨-, -, h⟩ := h
  · exact noEdge rfl h
  · exact noEdge rfl h

-- An actual MMA read without completion cannot authorize overwriting its byte.
example : ¬ modelCausality launch (execution false empty) byteLoc
    (.async (0,2) (.write (.load 0 0 0))) (.async (0,4) (.write (.load 0 0 0))) :=
  reuse_rejected (.inl rfl) (by decide)

-- Completion delivered to empty does not authorize a wait on a different barrier.
example : ¬ modelCausality launch (execution true wrong) byteLoc
    (.async (0,2) (.write (.load 0 0 0))) (.async (0,4) (.write (.load 0 0 0))) :=
  reuse_rejected (.inr rfl) (by decide)

-- Different byte paths cannot be stitched together by the closure.
example : ¬ modelCausality launch X ⟨.shared, 0, 1⟩
    (.async (0, 2) (.write (.load 0 0 0))) (.async (0, 4) (.write (.load 0 0 1))) := by
  intro h
  obtain ⟨a,w,hi,hcover⟩ := AsyncChain.left_cover h.2
  obtain ⟨_,spec,addr,⟨pc,hget⟩,hl,hs⟩ := hi
  have he : spec = copy := by cases hget; rfl
  subst spec
  have ha : a.loc = byteLoc := Option.some.inj (hl.symm.trans rfl)
  simp [ha, hs, Acc.Covers, Loc.InRange, byteLoc] at hcover

-- Async completion still cannot publish arbitrary generic stores without a proxy fence.
example (store : EvId) : ¬ modelCausality launch X byteLoc (.thread store)
    (.async (0, 4) (.write (.load 0 0 0))) := by
  rintro ⟨-, h | ⟨⟨s, hc, hg⟩, -⟩⟩
  · obtain ⟨fence, sp, scope, ⟨pc, hf⟩, -⟩ := h
    have := event_cases hf
    simp [loader, consumer] at this
  · obtain ⟨pc, hf⟩ := hc
    have := event_cases hf
    simp [loader, consumer] at this

-- A completion notification has no memory footprint and cannot be a junction.
example : ¬ AsyncCovers X (1,3) (.tcNotify 0) byteLoc := by
  rintro ⟨_,_,⟨_,h⟩,_⟩
  cases h

/-! ## Reusing a completed Tensor Memory copy's shared source -/

private def tcReuseTrace (isCopy completed : Bool) (dst : Acc) (acquire : Bool) : List Event := [
  ⟨0, .mbInit empty 1⟩,
  ⟨1, if isCopy then .tc (.cp tcCopy) else .tc (.mma 0 mma false [0, 0, 0, 0])⟩,
  ⟨2, .tc (.commit commit)⟩,
  ⟨3, .wait empty 0 completed acquire .cta⟩,
  ⟨4, .wr dst (List.replicate dst.size (.bits 8 0, 0))⟩]
private def tcReuseLog (completed : Bool) : List (Ref × MBarrier.Action) :=
  [(.thread (0, 0), .init 1)] ++
    (if completed then [(.async (0, 2) (.tcNotify 0), .arrive 1 0)] else []) ++
    [(.thread (0, 3), .pollParity 0 completed)]
private def tcReuse (isCopy completed : Bool) (dst : Acc) (acquire : Bool := true) : Execution := {
  tr := fun g => if g = 0 then tcReuseTrace isCopy completed dst acquire else []
  rf := fun _ _ => none
  async := {
    mmaOperands := fun i => if i = (0, 1) then
      some ⟨List.replicate 4096 (some (.bits 8 0, 0)),
        if isCopy then [] else List.replicate 256 (some (.bits 8 0, 0))⟩ else none
    mmaDone := fun i => decide (i = (0, 1)) && completed }
  tcNotified := fun i => if i = (0, 2) ∧ completed = true then {0} else ∅
  objects := fun l => if l = empty then replayLog (tcReuseLog completed) else [] }
private abbrev reuseRead : Ref := .async (0, 1) (.mmaRead false 0)

example : MBarrier.CheckedLog (replayLog (tcReuseLog true)) :=
  MBarrier.checkedLog_of_replay (ops := tcReuseLog true) rfl (by decide)
example : MBarrier.CheckedLog (replayLog (tcReuseLog false)) :=
  MBarrier.checkedLog_of_replay (ops := tcReuseLog false) rfl (by decide)

private theorem tcReuse_event {isCopy completed acquire : Bool} {dst : Acc} {e : EvId}
    {ev : Event} (h : (tcReuse isCopy completed dst acquire).get e = some ev) :
    ev ∈ tcReuseTrace isCopy completed dst acquire := by
  change (if e.1 = 0 then tcReuseTrace isCopy completed dst acquire else [])[e.2]? = some ev at h
  split at h
  · exact List.mem_of_getElem? h
  · cases h

private theorem tcReuse_no_proxy {isCopy completed : Bool} {dst : Acc} {l : Loc} {w e : EvId} :
    ¬ ProxyBefore launch (tcReuse isCopy completed dst) w e l := by
  rintro ⟨f, sp, sc, ⟨n, hf⟩, -⟩
  have h := tcReuse_event hf
  cases isCopy <;> simp [tcReuseTrace] at h

private theorem tcReuse_covered (completed : Bool) (dst : Acc) :
    AsyncCovers (tcReuse true completed dst) (0, 1) (.mmaRead false 0) byteLoc :=
  ⟨narrow, false, ⟨rfl, rfl, .inr ⟨tcCopy, 0, 0, ⟨1, rfl⟩, rfl, rfl, by decide, rfl⟩⟩,
    by simp [narrow, Acc.Covers, Loc.InRange]⟩

private theorem tcReuse_actual (isCopy : Bool) (dst : Acc) :
    ∃ v, (tcReuse isCopy true dst).MmaRead (0, 1) false 0 byteLoc v := by
  refine ⟨some (.bits 8 0, 0), ?_, _, rfl, rfl⟩
  cases isCopy
  · exact .inl ⟨0, mma, false, [0, 0, 0, 0], ⟨1, rfl⟩, rfl⟩
  · exact .inr ⟨tcCopy, 0, 0, ⟨1, rfl⟩, rfl, rfl, by decide, rfl⟩

example : (tcReuse true true wide).RefPresent reuseRead := ⟨byteLoc, tcReuse_actual true wide⟩
example : (tcReuse false true wide).RefPresent reuseRead := ⟨byteLoc, tcReuse_actual false wide⟩

private theorem tcReuse_finished (isCopy : Bool) (dst : Acc) :
    AsyncFinished launch (tcReuse isCopy true dst) (0, 1) (.mmaRead false 0) (0, 3) := by
  refine .inr ⟨.cta, ⟨.async (0, 2) (.tcNotify 0), empty, ?_, ?_⟩, ?_⟩
  · refine ⟨(0, 2), commit, 0, rfl, ?_, ⟨2, rfl⟩, rfl, Finset.mem_singleton.mpr rfl⟩
    refine ⟨rfl, by decide, ?_, commit, 2, rfl⟩
    cases isCopy
    · exact .inl ⟨0, mma, false, [0, 0, 0, 0], 1, rfl⟩
    · exact .inr (.inl ⟨tcCopy, 1, rfl⟩)
  · exact ⟨⟨3, 0, rfl⟩, 1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      by decide, rfl, rfl, fun _ _ _ h _ => absurd h (by omega)⟩
  · simp [ScopesMeet, MbarScopeIncludes, SameCta, SameCluster, launch, Launch.threads,
      Launch.clusterOfCta]

private theorem tcReuse_after (isCopy : Bool) (dst : Acc) :
    baseCausality launch (tcReuse isCopy true dst) (0, 3) (0, 4) := by
  refine .single (.inl ⟨rfl, by decide, ?_, ?_⟩)
  · change (4 : Nat) < 5
    decide
  · intro h
    have hn := h.2 1 (by decide)
    change some dst = none at hn
    cases hn

/-- The copy has read the shared byte and a real acquire has observed its commit.
The ordinary store can overwrite that byte without a proxy fence. -/
theorem tc_copy_source_reuse : modelCausality launch (tcReuse true true wide) byteLoc
    reuseRead (.thread (0, 4)) := by
  refine ⟨tcReuse_covered true wide, (0, 3), tcReuse_finished true wide, .inr
    ⟨rfl, .inl ⟨rfl, tcCopy, 1, rfl⟩, tcReuse_after true wide, wide, _, ⟨4, rfl⟩, ?_⟩⟩
  simp [wide, Acc.Covers, Loc.InRange]

/-- An unsuccessful poll supplies no completed read, even when it precedes the store. -/
example : ¬ modelCausality launch (tcReuse true false wide) byteLoc reuseRead (.thread (0, 4)) := by
  rintro ⟨-, w, h, -⟩
  rcases h with ⟨k, hv, -⟩ | ⟨ws, ho, -⟩
  · cases k with
    | cpAsync => contradiction
    | bulk mode => cases mode <;> contradiction
  · obtain ⟨n, m, -, ⟨p, parity, hw⟩, -⟩ := ho
    have h := tcReuse_event hw
    simp [tcReuseTrace] at h

/-- A successful but relaxed poll cannot supply an acquiring completion edge. -/
example (isCopy : Bool) : ¬ modelCausality launch (tcReuse isCopy true wide false) byteLoc reuseRead
    (.thread (0, 4)) := by
  rintro ⟨-, w, h, -⟩
  rcases h with ⟨k, hv, -⟩ | ⟨ws, ho, -⟩
  · cases k with
    | cpAsync => contradiction
    | bulk mode => cases mode <;> contradiction
  · obtain ⟨n, m, -, ⟨p, parity, hw⟩, -⟩ := ho
    have h := tcReuse_event hw
    cases isCopy <;> simp [tcReuseTrace] at h

/-- For the very same copy byte and completion, a disjoint store cannot use the rule. -/
example : ¬ modelCausality launch (tcReuse true true { loc := byteLoc.at 1, size := 4 }) byteLoc
    reuseRead (.thread (0, 4)) := by
  rintro ⟨-, w, -, h | ⟨-, -, -, a, bs, hw, hc⟩⟩
  · exact tcReuse_no_proxy h
  · obtain ⟨p, hw⟩ := hw
    have he : a = { loc := byteLoc.at 1, size := 4 } := by
      change some (⟨4, .wr _ _⟩ : Event) = some ⟨p, .wr a bs⟩ at hw
      cases hw
      rfl
    subst a
    have hb : (1 : Nat) ≤ 0 := hc.2.2.1
    omega

/-- The same covering store can overwrite a real MMA operand after its observing acquire. -/
theorem tc_mma_source_reuse :
    modelCausality launch (tcReuse false true wide) byteLoc reuseRead (.thread (0, 4)) := by
  have hcover : narrow.Covers byteLoc := by simp [narrow, Acc.Covers, Loc.InRange]
  have hstore : wide.Covers byteLoc := by simp [wide, Acc.Covers, Loc.InRange]
  refine ⟨⟨narrow, false, ⟨rfl, rfl, (tcReuse_actual false wide).choose_spec.1⟩, hcover⟩,
    (0, 3), tcReuse_finished false wide, .inr
      ⟨rfl, .inr ⟨rfl, by decide, 0, mma, false, [0, 0, 0, 0], 1, rfl⟩,
        tcReuse_after false wide, wide, _, ⟨4, rfl⟩, hstore⟩⟩

/-! ## A completed tcgen05.cp carries the TMA write order to a same-byte overwrite. -/

private theorem cpHandoff_read {acquire store : Bool} :
    (operandHandoff true acquire store).MmaFootprint (1, 2) false 0 byteLoc :=
  .inr ⟨tcCopy, 0, 0, ⟨2, rfl⟩, rfl, rfl, by decide, rfl⟩

private theorem cpHandoff_observed (acquire store : Bool) :
    AsyncObserved (operandHandoff true acquire store) (1, 2) .mmaDone (0, 3) acquire .cluster :=
  handoff_observed ⟨rfl, by decide, .inr (.inl ⟨tcCopy, 2, rfl⟩), commit, 3, rfl⟩

/-- The earlier write is a real TMA byte, and its order reaches the overlapping ordinary store
through an actual tcgen05.cp read and the acquiring wait for its commit. -/
theorem tc_copy_carries_tma_write :
    (∃ b, (operandHandoff true true true).MemWrites loadByte narrow [b]) ∧
      ¬ modelCausality launch (operandHandoff true true true) byteLoc loadByte storeWord ∧
      ByteCausality launch (operandHandoff true true true) byteLoc loadByte storeWord := by
  have hwide : wide.Covers byteLoc := by simp [wide, Acc.Covers, Loc.InRange]
  have hnarrow : narrow.Covers byteLoc := by simp [narrow, Acc.Covers, Loc.InRange]
  refine ⟨?_, handoff_no_direct, .commitOperand rfl
    ⟨narrow, ⟨rfl, copy, 1024, ⟨2, rfl⟩, rfl, rfl⟩, hnarrow⟩
    (.inr ⟨rfl, rfl, ⟨tcCopy, 2, rfl⟩, wide, _, ⟨4, rfl⟩, hwide⟩)
    ⟨some (.bits 8 0, 0), cpHandoff_read, _, rfl, rfl⟩
    (.direct (handoff_prior cpHandoff_read))
    ⟨.cluster, cpHandoff_observed true true, ?_⟩
    ⟨rfl, by decide, by decide, ?_⟩
    ⟨wide, .inl ⟨true, .inr (.inl ⟨_, ⟨4, rfl⟩, rfl⟩)⟩, hwide⟩⟩
  · exact ⟨_, observation, 1024, _, rfl, ⟨2, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [ScopesMeet, MbarScopeIncludes, SameCluster, launch, Launch.threads, Launch.clusterOfCta]
  · intro h
    have hs := h.2 1 (by decide)
    change some wide = none at hs
    cases hs

private theorem cpHandoff_no_mma {acquire store : Bool} {i : EvId} {d : Nat}
    {s : TcMma.OperandSpec} {a : Bool} {mask : List Nat} :
    ¬ (operandHandoff true acquire store).MmaIssue i d s a mask := by
  rintro ⟨pc, h⟩
  rcases handoff_event h with h | h
  · cases store <;> simp [loaderWithAccess, loader] at h
  · simp [operandConsumer, consumer] at h

/-- Replacing the destination store with an ordinary load cannot transport the TMA write's order. -/
theorem tc_copy_does_not_carry_to_load :
    ¬ ByteCausality launch (operandHandoff true true false) byteLoc loadByte storeWord := by
  intro h
  cases h with
  | direct h => exact handoff_no_direct h
  | commitOperand _ _ issue =>
    rcases issue with ⟨_, _, _, _, h⟩ | ⟨_, _, _, a, bs, ⟨pc, hw⟩, _⟩
    · exact cpHandoff_no_mma h
    · change some (⟨4, .rd _ _⟩ : Event) = _ at hw
      cases hw

/-- A successful relaxed observation of the copy's commit supplies no such write order. -/
theorem tc_copy_relaxed_does_not_carry_write :
    AsyncObserved (operandHandoff true false true) (1, 2) .mmaDone (0, 3) false .cluster ∧
      ¬ ByteCausality launch (operandHandoff true false true) byteLoc loadByte storeWord := by
  refine ⟨cpHandoff_observed false true, ?_⟩
  intro h
  cases h with
  | direct h => exact handoff_no_direct h
  | commitOperand _ _ issue _ _ observed next =>
    rcases issue with ⟨_, _, _, _, h⟩ | ⟨_, ha, _⟩
    · exact cpHandoff_no_mma h
    · cases ha
      obtain ⟨scope, ⟨n, m, hn, ⟨⟨pc, parity, hwait⟩, _⟩⟩, _⟩ := observed
      have hw := List.mem_of_getElem? hwait
      have hloader : (operandHandoff true false true).tr _ = loaderWithStore :=
        congrArg (operandHandoff true false true).tr next.1
      rw [hloader] at hw
      simp [loaderWithStore, loaderWithAccess, loader] at hw

open Lean Elab Command in
run_elab do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``PTX.modelCausality_async_trans, ``PTX.AsyncChain.trans,
      ``PTX.Tests.AsyncReuse.reuse_ordered, ``PTX.Tests.AsyncReuse.tc_copy_source_reuse,
      ``PTX.Tests.AsyncReuse.tc_mma_source_reuse, ``PTX.Tests.AsyncReuse.tc_copy_carries_tma_write,
      ``PTX.Tests.AsyncReuse.tc_copy_does_not_carry_to_load,
      ``PTX.Tests.AsyncReuse.tc_copy_relaxed_does_not_carry_write] do
    for ax in ← collectAxioms name do
      unless ax ∈ allowed do throwError "{name} uses unexpected axiom {ax}"

end
end PTX.Tests.AsyncReuse
