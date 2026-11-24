-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.Descent
public import Lemmas.Protocol.MbarPending
public import Lemmas.MBarrier.MBarrierInitOrder
public import Lemmas.Protocol.CountNth
public import Lemmas.Order.ElectOrdinal

@[expose] public section

/-! # Progress at a loader's empty wait

The first wait class of the descent. A pending loader at a slot's empty wait, whose last event no
longer blocks, either polls the barrier successfully (a counted extension, when the barrier is
ready) or is blocked (`loader_empty_steps`). Then a failed poll is appended, which keeps the
execution maximal (`Step.failed_poll_maximal`), and the slot is outstanding: one MMA consumer of
the cluster left as many notifications on the barrier as its phase (`InputBlocked`). Its warp
provides a blocker of smaller rank:

* an undelivered commit (the `commit` obligation, of rank 0);
* a lane that has not elected yet, before every k-block in the schedule (`mma_unelected`);
* the elected lane, still working: its commits to the slot are at most the notifications
  (`CommitsCounted`), so it committed at most up to the k-block four before the loader's, and its
  next event is earlier in the schedule (`ringAt_lt`).

The elected lane cannot have finished: it would have committed every k-block of the task the
loader is in, since both read the same responses (`AllResponsesAgree`) and the loader read only
claims (`ThreadFacts.loader_tasks`, `ThreadFacts.mma_leader`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow MBarrier AsyncCopy Classical

noncomputable section

theorem ringAt_lt {D K : Nat} (h : D + 4 ≤ K) : ringAt D + 21 < ringAt K := by
  unfold ringAt blockAt blockSpan
  omega

theorem ringAt_pos (K : Nat) : 58 < ringAt K := by
  unfold ringAt blockAt
  omega

/-- A working MMA thread's next event is no later than its next commit. -/
theorem mma_vtime_le (m : Mma.D) (D : Nat) (hs : m.site ≠ .elect) (he : Mma.exitOff m = none)
    (hr : match m.site with
     | .full s | .mma s _ | .commit s => D % 128 = m.q + s.val ∧ m.q % 4 = 0
     | .clcWait | .clcLoad | .clcStatus | .clcFirst | .clcFence | .ack | .accWait => D % 128 = 0
     | .accCommit => 128 ≤ D ∧ D % 128 = 0
     | _ => True) :
    Mma.vtime D m ≤ ringAt D + 20 := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := m
  cases site <;> simp only [Mma.exitOff, reduceCtorEq] at he hs <;>
    simp only [Mma.vtime, ringAt, blockAt, blockSpan] at hr ⊢ <;> omega

/-- The protocol exports the loader's empty-wait step uses, for every consistent execution. -/
structure LoaderEmptyFacts (L : Launch) (mem0 : Mem0) : Prop where
  ub : ∀ Y, Consistent L kernel Prod mem0 Y → ¬ HasUb Y
  thread : ∀ Y, Consistent L kernel Prod mem0 Y → ThreadFacts L Y
  blocked : ∀ Y, Consistent L kernel Prod mem0 Y → InputBlocked L Y
  agree : ∀ Y, Consistent L kernel Prod mem0 Y → AllResponsesAgree L Y
  commits : ∀ Y, Consistent L kernel Prod mem0 Y → CommitsCounted L Y

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The thread's state after a trace that is not empty. -/
theorem trace_ne_nil_of_role {g : Nat} {r : Prologue.Role}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr r))) : X.tr g ≠ [] := by
  intro h
  simp only [Frame.stateAt, h, List.length_nil, List.take_zero] at hσ
  cases hσ

theorem emptyLoc_eq (L : Launch) (cta : Nat) (s : Fin 4) :
    InputRing.emptyLoc L cta s = inputEmpty L cta s := by
  simp only [InputRing.emptyLoc, inputEmpty, Bar.loc, Bar.off]
  congr 1
  omega

/-- **The elected lane of an election.** The lane that an election of thread `h` elects is a
thread of the same warp with an election of the same instance that elects itself: the election
returned, so the election of each lane of its mask is present (`elect_ready`), and the elections of
one instance in one warp agree on the leader. -/
theorem elected_lane {Y : Execution} (hpre : Pre P L mem0) (hY : Consistent L kernel Prod mem0 Y)
    {h j epc mask inst ld : Nat} (hh : h < L.threads) (hE : Y.Elect (h, j) epc mask inst ld) :
    ∃ h' j' epc', h' < L.threads ∧ h' / L.block = h / L.block ∧
      h' % L.block / 32 = h % L.block / 32 ∧ Y.Elect (h', j') epc' mask inst (laneOf L h') := by
  have hblock := hpre.block
  have hmem := (hY.elect.1 _ _ _ _ _ hE).2.2
  obtain ⟨-, -, j', epc', ld', rfl, hE'⟩ := elect_ready hY hE _ (elect_need_mem hE hmem)
  have hld := hmem.1
  have hh' : warpLane L h ld < L.threads := by
    have : h < L.grid * L.block := hh
    simp only [warpLane, laneOf, Launch.threads]
    rw [hblock] at this ⊢
    omega
  have hc : warpLane L h ld / L.block = h / L.block := by
    simp only [warpLane, laneOf]; rw [hblock]; omega
  have hw : warpLane L h ld % L.block / 32 = h % L.block / 32 := by
    simp only [warpLane, laneOf]; rw [hblock]; omega
  have hsw : SameWarp L h (warpLane L h ld) := ⟨⟨hh, hh', hc.symm⟩, hw.symm⟩
  obtain ⟨-, -, rfl, -⟩ := hY.elect.2.1 _ _ _ _ _ _ _ _ _ hE hE' hsw
  have hlane : laneOf L (warpLane L h ld) = ld := by
    simp only [warpLane, laneOf]; rw [hblock]; omega
  refine ⟨_, j', epc', hh', hc, hw, ?_⟩
  rw [hlane]
  exact hE'

/-- **The blocker of a loader at a slot's empty wait.** In a maximal execution where a loader
stopped at a failed poll of a not-ready empty barrier, some open obligation ranks below the
loader's next event. -/
theorem loader_blocker_rank (hF : LoaderEmptyFacts L mem0) (hpre : Pre P L mem0)
    {Y : Execution} (hY : Maximal L kernel Prod mem0 Y) {g : Nat} (hg : g < L.threads)
    {l : Loader.D} {b : Fin 8}
    (hσ : Frame.stateAt (code L) Y g (Y.tr g).length = some (some (.inr (.loader l))))
      (hs : l.site = .wait b)
    (hσp : Frame.stateAt (code L) Y g ((Y.tr g).length - 1) = some (some (.inr (.loader l))))
    {pc : Nat} {m : Loc} {p : Nat} {acq : Bool} {sc : MbarScope}
    (hlast : (Y.tr g).getLast? = some ⟨pc, .wait m p false acq sc⟩) {before : State}
    (hstate : stateBefore (Y.objects (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b)))
      (Y.objects (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b))).length = some before)
    (hpar : before.phase % 2 = InputRing.producerParity b % 2) :
    ∃ o', Descent.Obl L Y o' ∧ rank L Y o' < ringAt (loaderCount L g (Y.tr g)) := by
  have hYc := hY.1
  have ht := hF.thread Y hYc
  have hblock := hpre.block
  obtain ⟨hout, b', hcnt⟩ := hF.blocked Y hYc g l b pc m p acq sc before hg hσ hs hlast hstate hpar
  set cta := g / L.block with hcta
  set c := cta / 2 with hc
  set s := InputRing.slotOf b with hsdef
  set K := loaderCount L g (Y.tr g) with hK
  obtain ⟨hslots, hwait⟩ := ht.loader_rank hg hσ
  obtain ⟨hKq, hq8⟩ := hwait b hs
  have hsv : s.val = b.val % 4 := rfl
  have hKs : okPolls (InputRing.emptyLoc L cta s) (Y.tr g) = (K + 3 - s.val) / 4 := by
    rw [emptyLoc_eq]; exact hslots s
  have hphase : before.phase + 1 = (K + 3 - s.val) / 4 := hout.trans hKs
  have hb8 := b.isLt
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
    · simp only [rank]
      exact Nat.lt_of_lt_of_le (by decide) (ringAt_pos K).le
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
    have hcom := hF.commits Y hYc hall h' b' ⟨cta % 2, Nat.mod_lt _ (by decide)⟩ s hh' hsel
    have hcom' : (Y.tr h').countP (commitsTo (inputEmpty L (h' / L.block) s)) ≤ before.phase := by
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
      have hDs := hcs s
      have hDK : D + 4 ≤ K := by omega
      refine ⟨.thread h', ⟨hh', fun hcan => hne' hcan.1, fun pc' hl => ?_⟩, ?_⟩
      · rw [ht.exited_state hh' hl] at hσh
        cases hσh
      · calc rank L Y (.thread h') ≤ threadTime L Y h' + 1 := rank_thread_le
          _ = Mma.vtime D mm + 1 := by rw [threadTime_of hσh hex]; rfl
          _ ≤ ringAt D + 21 := by have := mma_vtime_le mm D hsite hex hrel; omega
          _ < ringAt K := ringAt_lt hDK
    · -- finished: impossible, it read a response the loader read as a claim
      exfalso
      set R := okPolls (Bar.loc L (h' / L.block) ⟨.clc, 0, true⟩) (Y.tr h')
      have hDs := hper s
      have hRK : 128 * R + 4 ≤ K := by omega
      obtain ⟨hRl, hreads⟩ := ht.loader_tasks hg hσ hs
      have hR1 : R - 1 + 1 ≤ okPolls (Bar.loc L cta ⟨.clc, 0, true⟩) (Y.tr g) := by
        rw [← hRl]; omega
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
        obtain ⟨pcr1, src1, bs1, rr1, hr1, hf1, hrr1, hcl1⟩ := hreads j1 pc1 p1 acq1 sc1 hw1
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
    · -- dead: no longer followed, so of rank 0
      refine ⟨.thread h', ⟨hh', fun hcan => hne' hcan.1, hdead.2⟩, ?_⟩
      · calc rank L Y (.thread h') ≤ threadTime L Y h' + 1 := rank_thread_le
          _ = 1 := by simp [threadTime, hdead.1]
          _ < ringAt K := by have := ringAt_pos K; unfold ringAt blockAt at *; omega
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
        _ < ringAt K := by have := ringAt_pos K; unfold ringAt blockAt at *; omega

/-- **Progress at a loader's empty wait.** A pending loader at a slot's empty wait, whose last
event is released, extends a maximal execution or passes to an obligation of smaller rank. -/
theorem loader_empty_steps (hF : LoaderEmptyFacts L mem0) (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    {l : Loader.D} {b : Fin 8}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))))
      (hs : l.site = .wait b)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have ht := hF.thread X hX
  have hg := hp.1
  have hblock := hpre.block
  obtain ⟨t, hrun⟩ := Frame.run_some hX (hF.ub X hX) hp
  have hne := trace_ne_nil_of_role hσ
  set cta := g / L.block with hcta
  set s := InputRing.slotOf b
  set m := InputRing.emptyLoc L cta s with hm
  -- the barrier is initialized, so it has a state
  have hgrid : cta < L.grid := by
    have : g < L.grid * L.block := hg
    rw [hcta, Nat.div_lt_iff_lt_mul (by omega)]
    exact this
  have hw11 : g % L.block / 32 = 11 := by
    have := ht.role_warp hg (le_refl _) hσ
    simpa [roleWarp] using this
  obtain ⟨ipc, hinit⟩ := ht.ring_init_exists (b := ⟨.input, s.val, false⟩) hg (by omega)
    (le_refl _) hσ
    (by simp only [Bar.Valid, Ring.slots]; exact s.isLt) hgrid rfl
  have hloc : Bar.loc L cta ⟨.input, s.val, false⟩ = m := (InputRing.emptyLoc_bar L cta s).symm
  rw [hloc] at hinit
  obtain ⟨i0, r, hr, -, hra, -, -⟩ := init_record_of_actual_get hX hinit
  obtain ⟨before, hstate⟩ := stateBefore_length_some (hX.tma.2.2.1 m).1 (objects_noInval hX ht m)
      (List.mem_of_getElem? hr)
    hra (by simp only [Bar.count]; decide)
  -- the rank of the loader
  have hrank : rank L X (.thread g) = ringAt (loaderCount L g (X.tr g)) := by
    rw [rank_released hrel, threadTime_of hσ (by simp [ThreadD.exitOff, Loader.exitOff, hs])]
    simp [ThreadD.vtime, Loader.vtime, hs]
  refine Descent.mbar_wait_steps prod_wfFree (hF.ub X hX) hmax hp hrel hne
    (fun t hrun ok => ht.loader_poll hg hσ hs hrun ok) hstate fun sc hafter hready hYmax => ?_
  set Y := Step.failedPoll X g (Loader.Site.wait b).pc (InputRing.producerParity b) m true sc
    before with hY
  have htrY : Y.tr g = X.tr g ++ [⟨(Loader.Site.wait b).pc,
      .wait m (InputRing.producerParity b) false true sc⟩] := by
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
  have hlastY : (Y.tr g).getLast? = some ⟨(Loader.Site.wait b).pc,
      .wait m (InputRing.producerParity b) false true sc⟩ := by
    rw [htrY]; simp
  have hstateY : stateBefore (Y.objects m) (Y.objects m).length = some before := by
    rw [hY, Step.failedPoll_objects]
    simp only [ite_true, List.length_append, List.length_singleton]
    simp [stateBefore, Step.failedRecord]
  obtain ⟨o', hobl, hlt⟩ := loader_blocker_rank hF hpre hYmax hg hσY hs hσpY hlastY hstateY
    hready
  have hK : loaderCount L g (Y.tr g) = loaderCount L g (X.tr g) := by
    rw [htrY]
    simp [loaderCount, Flow.okPolls, List.countP_append, okPoll, sourceWaitSuccess]
  refine ⟨o', hobl, ?_⟩
  rw [hrank, ← hK]
  exact hlt

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
