-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.LoaderEmpty

@[expose] public section

/-! # Progress at a loader's tail drain

A loader that has left its task loop polls, in a tail drain, the four input empty barriers in
turn, with parity 1: it waits for the MMA threads to return every slot it filled. This is the
loader's empty wait of `LoaderEmpty.lean` after its last task, and its blocker is the same: a failed
poll of a not-ready barrier leaves the slot outstanding (`DrainBlocked`), and one MMA consumer of
the cluster has left as many notifications as the barrier's phase. Its warp provides a blocker of
smaller rank:

* an undelivered commit (the `commit` obligation, of rank 2);
* a lane that has not elected yet (`mma_unelected`);
* the elected lane, still working: its commits to the slot are at most the notifications
  (`CommitsCounted`), so it committed at least four k-blocks before the loader's count, and its
  next event is earlier in the schedule (`ringAt_lt`).

The elected lane cannot have finished: it would have read, at its last response poll, a response
that claims nothing, while the loader read a response that claims a CTA at the poll of the same
index, since that poll is not its latest (`ThreadFacts.loader_claims_before`; `AllResponsesAgree`).
-/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow MBarrier AsyncCopy Classical

noncomputable section

/-- The protocol exports the loader's tail drain step uses, for every consistent execution. -/
structure DrainWaitFacts (L : Launch) (mem0 : Mem0) : Prop where
  ub : ∀ Y, Consistent L kernel Prod mem0 Y → ¬ HasUb Y
  thread : ∀ Y, Consistent L kernel Prod mem0 Y → ThreadFacts L Y
  blocked : ∀ Y, Consistent L kernel Prod mem0 Y → DrainBlocked L Y
  agree : ∀ Y, Consistent L kernel Prod mem0 Y → AllResponsesAgree L Y
  commits : ∀ Y, Consistent L kernel Prod mem0 Y → CommitsCounted L Y

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The blocker of a loader at its tail drain.** In a maximal execution where a loader stopped at
a failed poll of the not-ready empty barrier of slot `i`, some open obligation ranks below the
loader's next event. -/
theorem drain_blocker_rank (hF : DrainWaitFacts L mem0) (hpre : Pre P L mem0)
    {Y : Execution} (hY : Maximal L kernel Prod mem0 Y) {g : Nat} (hg : g < L.threads)
    {l : Loader.D} {i : Fin 4}
    (hσ : Frame.stateAt (code L) Y g (Y.tr g).length = some (some (.inr (.loader l))))
      (hs : l.site = .drain i)
    (hσp : Frame.stateAt (code L) Y g ((Y.tr g).length - 1) = some (some (.inr (.loader l))))
    {pc : Nat} {m : Loc} {p : Nat} {acq : Bool} {sc : MbarScope}
    (hlast : (Y.tr g).getLast? = some ⟨pc, .wait m p false acq sc⟩)
    (hm : m = InputRing.emptyLoc L (g / L.block) i) {before : State}
    (hstate : stateBefore (Y.objects (InputRing.emptyLoc L (g / L.block) i))
      (Y.objects (InputRing.emptyLoc L (g / L.block) i)).length = some before)
    (hpar : before.phase % 2 = 1) :
    ∃ o', Descent.Obl L Y o' ∧ rank L Y o' < Loader.vtime (loaderCount L g (Y.tr g)) l := by
  have hYc := hY.1
  have ht := hF.thread Y hYc
  have hblock := hpre.block
  obtain ⟨hout, b', hcnt⟩ :=
    hF.blocked Y hYc g l i pc m p acq sc before hg hσ hs hlast hm hstate hpar
  set cta := g / L.block with hcta
  set c := cta / 2 with hc
  set K := loaderCount L g (Y.tr g) with hK
  obtain ⟨hslots, -⟩ := ht.loader_rank hg hσ
  obtain ⟨hK128, hKi⟩ := by
    have h := ht.loader_site_count hg hσ
    rw [hs] at h
    exact h
  have hR' : okPolls (Bar.loc L cta ⟨.clc, 0, true⟩) (Y.tr g) = K / 128 :=
    (ht.loader_count_ok hg hσ).2.2.2.2.2 i hs
  have hKs : okPolls (InputRing.emptyLoc L cta i) (Y.tr g) = (K + 3 - i.val) / 4 := by
    rw [emptyLoc_eq]; exact hslots i
  have hphase : before.phase + 1 = (K + 3 - i.val) / 4 := hout.trans hKs
  have hi4 := i.isLt
  have hvt : Loader.vtime K l = blockAt (K / 128 - 1) + 4190 + 2 * i.val := by
    simp only [Loader.vtime, hs]
  rw [hvt]
  have hgrid : cta < L.grid := by
    have : g < L.grid * L.block := hg
    rw [hcta, Nat.div_lt_iff_lt_mul (by omega)]
    exact this
  -- the commit obligation
  by_cases hall : ∀ i sp (rank : Fin 16) m, Y.Commit i sp → TcCommit.target sp rank = some m →
      rank ∈ Y.tcNotified i
  swap
  · refine ⟨.commit, ?_, ?_⟩
    · simp only [Descent.Obl]
      exact hall
    · simp only [rank, blockAt]
      omega
  have hcc : ∀ {h : Nat}, h / L.block = 2 * c → h / L.block + (cta % 2) = cta := by
    intro h hh; omega
  -- the warp of MMA consumer `b'`
  by_cases hel : ∃ h j epc mask inst leader, h < L.threads ∧ h / L.block = 2 * c ∧
      h % L.block / 32 = 8 + b'.val ∧ Y.Elect (h, j) epc mask inst leader
  · obtain ⟨h, j, epc, mask, inst, ld, hh, hhc, hhw, hE⟩ := hel
    obtain ⟨h', j', _, hh', hcta', hwarp', hE'⟩ := elected_lane hpre hY.1 hh hE
    have hh'c : h' / L.block = 2 * c := by omega
    have hh'w : h' % L.block / 32 = 8 + b'.val := by omega
    have hb2 := b'.isLt
    have hsel : InputRing.consumerThread L (h' / L.block / 2) b' h' = true := by
      simp only [InputRing.consumerThread, decide_eq_true_eq]; omega
    have hall' : ∀ i sp (rank : Fin 16) m, Y.Commit i sp → TcCommit.target sp rank = some m →
        rank ∈ Y.tcNotified i := hall
    have hcom := hF.commits Y hYc hall' h' b' ⟨cta % 2, Nat.mod_lt _ (by decide)⟩ i hh' hsel
    have hcom' : (Y.tr h').countP (commitsTo (inputEmpty L (h' / L.block) i)) ≤ before.phase := by
      refine hcom.trans (le_of_eq ?_)
      rw [← hcnt]
      have h1 : h' / L.block + cta % 2 = cta := hcc hh'c
      have h2 : h' / L.block / 2 = cta / 2 := by omega
      simp only [h1, h2]
      rfl
    have hne' : Y.tr h' ≠ [] := by
      intro he
      have := len_of_get hE'
      rw [he] at this
      simp at this
    rcases ht.mma_leader hh' (by omega) (by omega) hE' with ⟨mm, hσh, hex, hsite⟩ |
      ⟨hper, j2, pc2, p2, acq2, sc2, pcr2, src2, bs2, rr2, hn2, hw2, hr2, hf2, hrr2, hnc⟩ | hdead
    · -- working: an earlier point of the schedule
      obtain ⟨hcs, hrel⟩ := ht.mma_rank hh' hσh
      set D := mmaCount L h' (Y.tr h')
      have hDs := hcs i
      have hDK : D + 4 ≤ K := by omega
      refine ⟨.thread h', ⟨hh', fun hcan => hne' hcan.1, fun pc' hl => ?_⟩, ?_⟩
      · rw [ht.exited_state hh' hl] at hσh
        cases hσh
      · calc rank L Y (.thread h') ≤ threadTime L Y h' + 1 := rank_thread_le
          _ = Mma.vtime D mm + 1 := by rw [threadTime_of hσh hex]; rfl
          _ ≤ ringAt D + 21 := by have := mma_vtime_le mm D hsite hex hrel; omega
          _ < blockAt (K / 128 - 1) + 4190 + 2 * i.val := by
            unfold ringAt blockAt blockSpan
            omega
    · -- finished: impossible, it read a response that the loader read as a claim
      exfalso
      set R := okPolls (Bar.loc L (h' / L.block) ⟨.clc, 0, true⟩) (Y.tr h')
      have hDs := hper i
      have hRK : R + 1 ≤ K / 128 := by omega
      have hR1 : R - 1 + 1 ≤ okPolls (Bar.loc L cta ⟨.clc, 0, true⟩) (Y.tr g) := by
        rw [hR']; omega
      obtain ⟨j1, ev1, hj1, hok1, hc1⟩ :=
        MbarRing.Slot.exists_nth_countP (okPoll (Bar.loc L cta ⟨.clc, 0, true⟩)) hR1
      obtain ⟨pc1, k1⟩ := ev1
      cases k1 with
      | wait m1 p1 ok1 acq1 sc1 =>
        have hok1' : ok1 = true ∧ m1 = Bar.loc L cta ⟨.clc, 0, true⟩ := by
          cases ok1 <;> simp_all [okPoll, sourceWaitSuccess]
        obtain ⟨rfl, rfl⟩ := hok1'
        have hw1 : Y.get (g, j1) =
            some ⟨pc1, .wait (Bar.loc L cta ⟨.clc, 0, true⟩) p1 true acq1 sc1⟩ :=
          hj1
        have hcount1 : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((Y.tr g).take j1) + 1 <
            okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (Y.tr g) := by
          have h1 : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((Y.tr g).take j1) =
            R - 1 := hc1
          rw [h1, hR']
          omega
        obtain ⟨pcr1, src1, bs1, rr1, hr1, hf1, hrr1, hcl1⟩ :=
          ht.loader_claims_before hg hσ j1 pc1 p1 acq1 sc1 hw1 hcount1
        have hrw := ht.role_warp hg (le_refl _) hσ
        simp only [roleWarp] at hrw
        have hbs := hF.agree Y hYc c g h' j1 j2 pc1 pc2 p1 p2 pcr1 pcr2 acq1 acq2 sc1 sc2 src1
          src2 bs1 bs2 (by omega) (by omega) hw1 hw2 (by
            have h1 : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((Y.tr g).take j1) =
              R - 1 := hc1
            omega) hr1 hf1 hr2 hf2
        subst hbs
        rw [hrr1] at hrr2
        cases hrr2
        exact hnc hcl1
      | _ => simp [okPoll, sourceWaitSuccess] at hok1
    · -- dead: no longer followed, so of rank 1
      refine ⟨.thread h', ⟨hh', fun hcan => hne' hcan.1, hdead.2⟩, ?_⟩
      · calc rank L Y (.thread h') ≤ threadTime L Y h' + 1 := rank_thread_le
          _ = 1 := by simp [threadTime, hdead.1]
          _ < blockAt (K / 128 - 1) + 4190 + 2 * i.val := by unfold blockAt blockSpan; omega
  · -- no lane has elected: lane 0 of the warp is before its election
    push Not at hel
    set h0 := 2 * c * L.block + 32 * (8 + b'.val) with hh0
    have hb2 := b'.isLt
    have hh0t : h0 < L.threads := by
      have : 2 * c < L.grid := by omega
      show h0 < L.grid * L.block
      rw [hh0, hblock]
      omega
    have hh0c : h0 / L.block = 2 * c := by rw [hh0, hblock]; omega
    have hh0w : h0 % L.block / 32 = 8 + b'.val := by rw [hh0, hblock]; omega
    have hh0e : h0 / L.block % 2 = 0 := by rw [hh0c]; omega
    have hh0w' : h0 % L.block / 32 = 8 ∨ h0 % L.block / 32 = 9 := by rw [hh0w]; omega
    obtain ⟨d, hσ0, hex0, hv0⟩ := ht.mma_unelected hh0t hh0e hh0w'
      (fun j epc mask inst leader => hel h0 j epc mask inst leader hh0t hh0c hh0w)
    have hlen : 0 < (Y.tr g).length := by
      have := List.getLast?_isSome.mp (by rw [hlast]; rfl)
      exact List.length_pos_of_ne_nil this
    obtain ⟨ev, hev⟩ : ∃ ev, Y.get (g, (Y.tr g).length - 1) = some ev :=
      ⟨_, List.getElem?_eq_getElem (Nat.sub_lt hlen Nat.one_pos)⟩
    have hne0 := ht.cluster_started hg hev hσp hh0t (by
      rw [clusterOfCta_eq hpre, clusterOfCta_eq hpre, hh0c, hc, hcta]
      omega)
    refine ⟨.thread h0, ⟨hh0t, fun hcan => hne0 hcan.1, fun pc' hl => ?_⟩, ?_⟩
    · rw [ht.exited_state hh0t hl] at hσ0
      cases hσ0
    · calc rank L Y (.thread h0) ≤ threadTime L Y h0 + 1 := rank_thread_le
        _ = d.vtime L h0 (Y.tr h0) + 1 := by rw [threadTime_of hσ0 hex0]
        _ ≤ 59 := by omega
        _ < blockAt (K / 128 - 1) + 4190 + 2 * i.val := by unfold blockAt blockSpan; omega

/-- **Progress at a loader's tail drain.** A pending loader at the drain poll of a slot's empty
barrier, whose last event is released, extends a maximal execution or passes to an obligation of
smaller rank. -/
theorem loader_drain_steps (hF : DrainWaitFacts L mem0) (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    {l : Loader.D} {i : Fin 4}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))))
      (hs : l.site = .drain i)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have ht := hF.thread X hX
  have hg := hp.1
  have hblock := hpre.block
  obtain ⟨t, hrun⟩ := Frame.run_some hX (hF.ub X hX) hp
  have hne := trace_ne_nil_of_role hσ
  set cta := g / L.block with hcta
  set m := InputRing.emptyLoc L cta i with hm
  -- the barrier is initialized, so it has a state
  have hgrid : cta < L.grid := by
    have : g < L.grid * L.block := hg
    rw [hcta, Nat.div_lt_iff_lt_mul (by omega)]
    exact this
  have hw11 : g % L.block / 32 = 11 := by
    have := ht.role_warp hg (le_refl _) hσ
    simpa [roleWarp] using this
  obtain ⟨ipc, hinit⟩ := ht.ring_init_exists (b := ⟨.input, i.val, false⟩) hg (by omega)
    (le_refl _) hσ
    (by simp only [Bar.Valid, Ring.slots]; exact i.isLt) hgrid rfl
  have hloc : Bar.loc L cta ⟨.input, i.val, false⟩ = m := (InputRing.emptyLoc_bar L cta i).symm
  rw [hloc] at hinit
  obtain ⟨i0, r, hr, -, hra, -, -⟩ := init_record_of_actual_get hX hinit
  obtain ⟨before, hstate⟩ := stateBefore_length_some (hX.tma.2.2.1 m).1 (objects_noInval hX ht m)
      (List.mem_of_getElem? hr)
    hra (by simp only [Bar.count]; decide)
  -- the rank of the loader
  have hrank : rank L X (.thread g) = Loader.vtime (loaderCount L g (X.tr g)) l := by
    rw [rank_released hrel, threadTime_of hσ (by simp [ThreadD.exitOff, Loader.exitOff, hs])]
    simp [ThreadD.vtime]
  refine Descent.mbar_wait_steps prod_wfFree (hF.ub X hX) hmax hp hrel hne
    (fun t hrun ok => ht.loader_drain_poll hg hσ hs hrun ok) hstate fun sc hafter hready hYmax => ?_
  set Y := Step.failedPoll X g (Loader.Site.drain i).pc 1 m true sc before with hY
  have htrY : Y.tr g = X.tr g ++ [⟨(Loader.Site.drain i).pc, .wait m 1 false true sc⟩] := by
    rw [hY, Step.failedPoll_tr]; simp
  have hσY : Frame.stateAt (code L) Y g (Y.tr g).length = some (some (.inr (.loader l))) := by
    simp only [Frame.stateAt, List.take_length]
    rw [htrY]
    exact hafter
  have hσpY : Frame.stateAt (code L) Y g ((Y.tr g).length - 1) = some (some (.inr (.loader l))) :=
    by
    simp only [Frame.stateAt]
    rw [htrY, List.length_append, List.length_singleton, Nat.add_sub_cancel,
      List.take_left' rfl]
    simpa [Frame.stateAt] using hσ
  have hlastY : (Y.tr g).getLast? = some ⟨(Loader.Site.drain i).pc, .wait m 1 false true sc⟩ := by
    rw [htrY]; simp
  have hstateY : stateBefore (Y.objects m) (Y.objects m).length = some before := by
    rw [hY, Step.failedPoll_objects]
    simp only [ite_true, List.length_append, List.length_singleton]
    simp [stateBefore, Step.failedRecord]
  obtain ⟨o', hobl, hlt⟩ := drain_blocker_rank hF hpre hYmax hg hσY hs hσpY hlastY rfl hstateY
    hready
  have hK : loaderCount L g (Y.tr g) = loaderCount L g (X.tr g) := by
    rw [htrY]
    simp [loaderCount, Flow.okPolls, List.countP_append, okPoll, sourceWaitSuccess]
  refine ⟨o', hobl, ?_⟩
  rw [hrank, ← hK]
  exact hlt

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
