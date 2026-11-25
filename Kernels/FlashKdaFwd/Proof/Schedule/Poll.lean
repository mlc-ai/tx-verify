-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Schedule.Lag
public import Lemmas.Protocol.NamedBarReady
public import Lemmas.Protocol.UnitsTrace
public import Lemmas.Protocol.MbarUnitTx

@[expose] public section

/-!
# The premises about a thread at an `mbarrier.try_wait`: `pollState` and `pollBlk`

A thread at a poll state polls one of the eleven mbarriers of its block (`RefProgress.poll`:
the barrier `b`, the parity, an upper bound on the thread's successful polls of `b` by its
tile index).

**`prem_pollState`** (the polled barrier has a state, that is, it was initialized). The
barrier's owner initialized it before the `bar.sync 0` of ordinal `b.gen`. For the ten
pipeline barriers the poller is in a tile loop and has made six `bar.sync 0`, two more than
needed (`Facts.pollState_of_two`). For the state barrier (`b.gen = 2`) the poller has made
three; if its third `bar.sync 0` is not its last event, the barrier has released and the load
leader has arrived at it (`BarFacts.peer_bar0`); if it is the last event, the thread is
released, so that arrival is ready, and a ready `bar.sync` has every participant's arrival
(`NamedBar.Sources.ready_member_arrival`, `Lemmas/Protocol/NamedBarReady.lean`). Either way
the load leader has made three `bar.sync 0` (`Facts.pollState_of_owner`).

**`prem_pollBlk`** (when the poll would fail, the thread has a blocker: an unfinished
tensor load, or a pending thread at an earlier time). One case per kind of barrier, each from
the protocol layer's count-level blocker and the contract's lower bounds on what a thread at
tile `t` has delivered:

* `loadFull s`, polled by a compute thread at tile `t`. Protocol: the load leader has made at
  most `n` arrivals on it or fewer than `70 (n + 1)` loads, `n` being the poller's successful
  polls. Blocker: the load leader, at tile `t'`. From `uses 3 t' s ≤ n ≤ uses 3 t s` and
  `s = t % 3` (`pollStage`), `t' ≤ t`; in the same tile the leader is in its own loop
  (`region`), whose band of the time table is before the compute band.
* `loadEmpty s`, polled by the load leader at tile `t`. Protocol: some compute thread has made
  one arrival less than the poller's successful polls. Blocker: that compute thread;
  `uses 3 t' s < uses 3 t s`, so `t' < t`.
* `storeFull o`, polled by the store leader at tile `t`. Protocol: some compute thread has
  made exactly the poller's number of successful polls. Blocker: that compute thread; `t' ≤ t`
  as for `loadFull`; in the same tile it is in the compute loop, before the store band.
* `storeEmpty o`, polled by a compute thread at tile `t`. Protocol: the store leader has made
  one arrival less. Blocker: the store leader, `t' < t`.
* `state`, polled by every thread. Protocol: the barrier is in phase 0 (`state_phase_le`) and
  the load leader has not arrived on it or has issued fewer than 16 loads. Blocker: the load
  leader, which is then at or before its third `bar.sync 0` (`arrState`), before the poll.

A blocker that has exited is excluded by the same bounds at its exit state (tile index = tile
count), and one whose machine has stopped by `live_of_maximal`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Sched PTX.Flow PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Protocol
open PTX.Kernels.FlashKdaFwd.Proof.Thread (Site)
open MBarrier

noncomputable section

/-! ### The arithmetic of `uses` and of `bar0Of` -/

/-- A stage has at least as many uses in more tiles. -/
theorem uses_mono {n t t' s : Nat} (h : t ≤ t') : uses n t s ≤ uses n t' s :=
  Nat.div_le_div_right (by omega)

/-- Fewer uses of a stage: fewer tiles. -/
theorem tile_lt_of_uses {n t t' s : Nat} (h : uses n t' s < uses n t s) : t' < t := by
  by_contra hle
  have := uses_mono (n := n) (s := s) (Nat.le_of_not_lt hle)
  omega

/-- No more uses of the stage of tile `t` than before tile `t`: at most `t` tiles (three
stages). -/
theorem tile_le_of_uses3 {t t' s : Nat} (hs : s = t % 3) (h : uses 3 t' s ≤ uses 3 t s) :
    t' ≤ t := by
  unfold uses at h
  omega

/-- The same for two stages. -/
theorem tile_le_of_uses2 {t t' s : Nat} (hs : s = t % 2) (h : uses 2 t' s ≤ uses 2 t s) :
    t' ≤ t := by
  unfold uses at h
  omega

/-- A thread at a later instruction has made at least as many `bar.sync 0`. -/
theorem bar0Of_mono {pc pc' : Nat} (h : pc ≤ pc') : bar0Of pc ≤ bar0Of pc' := by
  unfold bar0Of
  refine List.Sublist.length_le (List.monotone_filter_right _ fun x hx => ?_)
  simp only [decide_eq_true_eq] at hx ⊢
  omega

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {I : Nums}

/-- The counts of a prefix of a trace are at most the counts of the trace. -/
theorem arrivals_take_le (m : Loc) (es : List Event) (k : Nat) :
    arrivals m (es.take k) ≤ arrivals m es :=
  (List.take_sublist k es).countP_le

theorem issues_take_le (m : Loc) (es : List Event) (k : Nat) :
    (es.take k).countP (issuesTo m) ≤ es.countP (issuesTo m) :=
  (List.take_sublist k es).countP_le

/-! ### `pollState` -/

set_option maxRecDepth 100000 in
/-- **`Premises2.pollState`**: the barrier a released thread at a poll state polls has a
state. -/
theorem prem_pollState (hpre : Pre P L mem0) (R : RefProgress L mem0 X I) (F : Facts P L X)
    (hX : Consistent L kernel Assumptions.all mem0 X) {g : Nat} {d : Thread.D}
    (hg : g < L.threads) (hrel : Step.Released L X g)
    (hσ : Frame.stateAt (Thread.code L) X g (X.tr g).length = some (some d))
    (hc : cls g d = .poll) (l : Loc) (q : Nat) (ok : Bool) (sc : MbarScope)
    (hev : pollEv L g d ⟨d.site.pc, .wait l q ok true sc⟩) :
    ∃ before, stateBefore (X.objects l) (X.objects l).length = some before := by
  have hb := hpre.block
  obtain ⟨b, -, -, hstart, hfire⟩ := R.poll hg hσ hc
  obtain ⟨t, ins, o, hat, hi, hf⟩ := hev
  obtain ⟨hl, -⟩ := hfire hat hi hf l q ok true sc rfl
  have hcnt := R.bar0 hg hσ
  rw [take_all] at hcnt
  by_cases h2 : b.gen + 2 ≤ bar0Of d.site.pc
  · exact F.pollState_of_two hpre hX hg b hl (by rw [hcnt]; exact h2)
  -- only the state barrier, polled after exactly three `bar.sync 0`, is left
  obtain ⟨j', hj'⟩ := site_of_poll hc
  have h384 : 384 ≤ d.site.pc := by rw [hj']; exact mbarWait_pc_ge j'
  have h3 : 3 ≤ bar0Of d.site.pc := (show bar0Of 384 = 3 by decide) ▸ bar0Of_mono h384
  have hbs : b = .state := by
    by_cases h1402 : d.site.pc ≤ 1402
    · exact hstart h1402
    · have h6 : 6 ≤ bar0Of d.site.pc :=
        (show bar0Of 1403 = 6 by decide) ▸ bar0Of_mono (by omega : 1403 ≤ d.site.pc)
      cases b <;> simp only [Bar.gen] at h2 <;> omega
  subst hbs
  have hc' := cta_lt hb hg
  refine F.pollState_of_owner hpre hX hc' .state hl ?_
  -- the poller's third `bar.sync 0`
  obtain ⟨j, pc, hjlt, hbar, hord⟩ := F.bars.nth_bar0 hX (g := g) (k := (X.tr g).length)
    (q := 2) (by rw [take_all, hcnt]; exact h3)
  have hown : Bar.state.owner L (g / L.block) < L.threads := Bar.owner_lt hb hc' .state
  have hodiv : Bar.state.owner L (g / L.block) / L.block = g / L.block := Bar.owner_div hb .state
  -- the owner's `bar.sync 0` of the same ordinal
  have hpeer : ∃ e pce, X.get (Bar.state.owner L (g / L.block), e) =
      some ⟨pce, .bar 0 none .sync⟩ ∧ bar0Before X (Bar.state.owner L (g / L.block), e) = 2 := by
    by_cases hlast : j + 1 < (X.tr g).length
    · have hsucc := countP_take_succ (p := Execution.isBarId 0) hbar
        (by simp [Execution.isBarId])
      obtain ⟨e, pce, md, he, heq⟩ := F.bars.peer_bar0 hX hb hown hodiv hlast
        (show 2 + 1 ≤ bar0Before X (g, j + 1) by
          unfold bar0Before at hord ⊢
          simp only at hord ⊢
          omega)
      obtain ⟨hmd, -⟩ := F.bars.shape hown he
      subst hmd
      exact ⟨e, pce, he, heq⟩
    · -- the barrier is the poller's last event: it is ready, the thread being released
      have hj : j = (X.tr g).length - 1 := by omega
      have hready : Ready L X (g, j) := by
        rw [hj]
        exact hrel.ready pc _ (hj ▸ hbar) rfl
      by_cases hex : ∃ k pcx, X.get (Bar.state.owner L (g / L.block), k) = some ⟨pcx, .exit⟩
      · obtain ⟨k, pcx, hx⟩ := hex
        have h9 := F.bars.bar0_exit hown hx
        obtain ⟨i, pci, -, hi', hio⟩ := F.bars.nth_bar0 hX
          (g := Bar.state.owner L (g / L.block))
          (k := (X.tr (Bar.state.owner L (g / L.block))).length) (q := 2)
          (by rw [take_all, h9]; decide)
        exact ⟨i, pci, hi', hio⟩
      · have hno : ∀ k pcx, X.get (Bar.state.owner L (g / L.block), k) ≠
            some ⟨pcx, .exit⟩ := fun k pcx h => hex ⟨k, pcx, h⟩
        obtain ⟨i, pci, hi', hio⟩ := (F.bars.sources0 hb).ready_member_arrival hX (shape0 hb)
          hbar hready (g := Bar.state.owner L (g / L.block)) hodiv
          (Bar.owner_warp hb .state) hno
        exact ⟨i, pci, hi', hio.trans hord⟩
  obtain ⟨e, pce, he, heq⟩ := hpeer
  have h1 := countP_take_succ (p := Execution.isBarId 0) he (by simp [Execution.isBarId])
  have h2' := (List.take_sublist (e + 1) (X.tr (Bar.state.owner L (g / L.block)))).countP_le
    (p := Execution.isBarId 0)
  unfold bar0Before at heq
  simp only at heq
  simp only [Bar.gen]
  omega

/-! ### `pollBlk` -/

/-- **The state barrier completes at most one phase**: its count is 1, every arrival on it is
the load leader's, and the load leader arrives once. -/
theorem state_phase_le (hpre : Pre P L mem0) (F : Facts P L X)
    (hX : Consistent L kernel Assumptions.all mem0 X) {c : Nat} (hc : c < L.grid) {st : State}
    (hst : stateBefore (X.objects (Bar.state.loc L c)) (X.objects (Bar.state.loc L c)).length =
      some st) : st.phase ≤ 1 := by
  have hb := hpre.block
  have o := F.state.stateObj F.init F.bars (noEvents hX) hX hb c
  have hff := F.state.faultFree F.init F.bars (noEvents hX) hX hb hc
  have hch := X.objects_checked hX (Bar.state.loc L c)
  have hexp := PairTmaRing.expected_of_init hX o.init o.noInval hst
  have hacc := (hch.accounted o.noInval le_rfl).2 st hst
  simp only [unitsBefore, List.take_length] at hacc
  rw [hexp, o.noInc] at hacc
  -- the units of the history are arrivals of the load leader
  have hunits : arrivalUnits (X.objects (Bar.state.loc L c)) ≤
      (X.objects (Bar.state.loc L c)).countP (MbarRing.Unit.unitsOf (loadLeader L c)) := by
    refine arrivalUnits_le_countP _ fun r hr hf cn tx ha => ?_
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨h1, -, j, pcj, rel, sc, hid, -⟩ := o.arrive hk ha
    refine ⟨h1, ?_⟩
    simp only [MbarRing.Unit.unitsOf, Bool.and_eq_true]
    exact ⟨countedArrive_iff.mpr ⟨hf, cn, tx, ha⟩, objectThreadSelected_iff.mpr ⟨j, hid⟩⟩
  rw [MbarRing.Unit.unitsOf_eq_arrivals hX hff] at hunits
  -- the load leader arrives once
  have hone : arrivals (Bar.state.loc L c) (X.tr (loadLeader L c)) ≤ 1 := by
    have hy : loadLeader L c < L.threads := thr_lt hb hc (by decide)
    by_contra hgt
    obtain ⟨i, ev, hi, hp, hcnt⟩ := MbarRing.Slot.exists_nth_countP
      (arrivesOn (Bar.state.loc L c)) (xs := X.tr (loadLeader L c)) (c := 1) (by
        unfold arrivals at hgt
        omega)
    obtain ⟨pce, kd⟩ := ev
    have hget : X.get (loadLeader L c, i) = some ⟨pce, kd⟩ := hi
    cases kd with
    | arrive m tx cn rel sc =>
      have hm : m = Bar.state.loc L c := by
        simpa [arrivesOn, sourceArrive] using hp
      subst hm
      have := (F.state.arrive hy hget).2.2.2.2
      unfold arrivals at this
      omega
    | _ => simp [arrivesOn, sourceArrive] at hp
  omega

/-- The state before the exit event of a thread: at the last instruction, at the tile count. -/
theorem exit_state (hsound : ∀ g < L.threads, (Thread.code L g).Sound)
    (hs : SafeGoal kernel Assumptions.all L mem0) (R : RefProgress L mem0 X I)
    (hX : Consistent L kernel Assumptions.all mem0 X) {h k pc : Nat} (hh : h < L.threads)
    (hx : X.get (h, k) = some ⟨pc, .exit⟩) :
    ∃ dk, Frame.stateAt (Thread.code L) X h k = some (some dk) ∧ dk.site.pc = 3835 ∧
      I.tile h dk = I.tiles h := by
  obtain ⟨dk, hdk⟩ := Frame.state_of_noUb hsound hX R.tracked (safe_noUb (hs.2 X hX)) hx
  have hpc := R.exitAt hh hdk hx
  exact ⟨dk, hdk, hpc, R.tile_end hh hdk (by omega)⟩

/-- **A thread of the block that has not exited and whose state is earlier in the time table
is a blocker.** -/
theorem blk_of_earlier (hsound : ∀ g < L.threads, (Thread.code L g).Sound)
    (hs : SafeGoal kernel Assumptions.all L mem0)
    (hT : ∀ g, I.tiles g = ctaTiles P (g / L.block)) (R : RefProgress L mem0 X I)
    (hmax : Maximal L kernel Assumptions.all mem0 X) {g h : Nat} {d : Thread.D}
    (hσ : Frame.stateAt (Thread.code L) X g (X.tr g).length = some (some d))
    (hh : h < L.threads) (hcta : h / L.block = g / L.block)
    (hne : ∀ k pc, X.get (h, k) ≠ some ⟨pc, .exit⟩)
    (hlt : ∀ dh, Frame.stateAt (Thread.code L) X h (X.tr h).length = some (some dh) →
      timeAt (I.tiles g) (I.tile h dh) dh.site.pc dh.site.sub <
        timeAt (I.tiles g) (I.tile g d) d.site.pc d.site.sub) :
    Blk (timed L I) X g := by
  have hp := pending_of_noExit hmax.1 hh hne
  obtain ⟨dh, hσh⟩ := live_of_maximal hsound hs R hmax hp
  refine .inr ⟨h, hp, ?_⟩
  rw [threadTime_eq hσh, threadTime_eq hσ]
  unfold time
  rw [show I.tiles h = I.tiles g by rw [hT, hT, hcta]]
  exact hlt dh hσh

/-- The time comparison of the "full" barriers: a blocker at the poller's tile or an earlier
one, and in the same tile at an earlier instruction, is earlier. -/
theorem time_lt_of_tile_le {T t th pc pch sub subh : Nat} (hsubh : subh ≤ 3) (htle : th ≤ t)
    (ht : t ≤ T) (hpc : 1402 < pc) (hpch : pch ≤ 3112) (hsame : th = t → pch < pc) :
    timeAt T th pch subh < timeAt T t pc sub := by
  rcases Nat.lt_or_eq_of_le htle with h | h
  · exact timeAt_lt_tile hpch hsubh h ht hpc
  · exact timeAt_lt_pc (hsame h) hsubh fun _ _ => h

set_option maxRecDepth 100000 in
/-- **`Premises2.pollBlk`**: when the polled barrier's phase has the poll's parity (the poll
would fail), the thread has a blocker: an unfinished tensor load, or a pending thread at an
earlier time. -/
theorem prem_pollBlk (hpre : Pre P L mem0)
    (hsound : ∀ g < L.threads, (Thread.code L g).Sound)
    (hs : SafeGoal kernel Assumptions.all L mem0)
    (hT : ∀ g, I.tiles g = ctaTiles P (g / L.block)) (R : RefProgress L mem0 X I)
    (F : Facts P L X) (hmax : Maximal L kernel Assumptions.all mem0 X) {g : Nat} {d : Thread.D}
    (hg : g < L.threads)
    (hσ : Frame.stateAt (Thread.code L) X g (X.tr g).length = some (some d))
    (hc : cls g d = .poll) (l : Loc) (q : Nat) (sc : MbarScope) (before : State)
    (hev : pollEv L g d ⟨d.site.pc, .wait l q false true sc⟩)
    (hst : stateBefore (X.objects l) (X.objects l).length = some before)
    (hpar : before.phase % 2 = q % 2) : Blk (timed L I) X g := by
  have hX := hmax.1
  have hb := hpre.block
  have hcg := cta_lt hb hg
  by_cases hno : Descent.Obl L X .tensor
  · exact .inl ⟨.tensor, .inr (.inr (.inl rfl)), hno⟩
  obtain ⟨b, hpoller, hround, hstart, hfire⟩ := R.poll hg hσ hc
  obtain ⟨t, ins, o, hat, hi, hf⟩ := hev
  obtain ⟨hl, hq⟩ := hfire hat hi hf l q false true sc rfl
  have hstage := R.pollStage hg hσ hc hat hi hf q false true sc
  subst hl
  rw [take_all] at hround hq
  rw [hq] at hpar
  have hgle := R.tile_le hg hσ
  obtain ⟨hreg1, hreg2, hreg3⟩ := R.region hg hσ
  have hTg : ∀ h, h / L.block = g / L.block → I.tiles h = I.tiles g := fun h hd => by
    rw [hT, hT, hd]
  -- the three threads with a job, and the facts of a blocker's state
  have hll : loadLeader L (g / L.block) < L.threads := thr_lt hb hcg (by decide)
  have hld : loadLeader L (g / L.block) / L.block = g / L.block := thr_div hb (by decide)
  have hlm : loadLeader L (g / L.block) % L.block = 128 := thr_mod hb (by decide)
  have hsl : storeLeader L (g / L.block) < L.threads := thr_lt hb hcg (by decide)
  have hsd : storeLeader L (g / L.block) / L.block = g / L.block := thr_div hb (by decide)
  have hsm : storeLeader L (g / L.block) % L.block = 160 := thr_mod hb (by decide)
  cases b with
  | loadFull s =>
    obtain ⟨-, hgc⟩ := hpoller
    simp only [Bar.delta, Nat.add_zero] at hpar
    simp only [roundOf] at hround
    obtain ⟨hstg, htlt⟩ := hstage.1 s rfl
    have hga : computeThread L (g / L.block) ⟨g % L.block, hgc⟩ = g := thr_eq hb g
    obtain ⟨hph, hshort⟩ := F.load.full_blocked F.init F.bars (noEvents hX) hX hb hcg s hno
      ⟨g % L.block, hgc⟩ hst (by rw [hga]; exact hpar)
    rw [hga] at hph
    have hbound : ∀ k dk,
        Frame.stateAt (Thread.code L) X (loadLeader L (g / L.block)) k = some (some dk) →
          I.tile (loadLeader L (g / L.block)) dk ≤ I.tile g d := by
      intro k dk hdk
      obtain ⟨ha1, ha2⟩ := R.arrLoadFull hll hdk (by rw [hld]) s
      rw [hld] at ha1 ha2
      have h1 := arrivals_take_le ((Bar.loadFull s).loc L (g / L.block))
        (X.tr (loadLeader L (g / L.block))) k
      have h2 := issues_take_le ((Bar.loadFull s).loc L (g / L.block))
        (X.tr (loadLeader L (g / L.block))) k
      refine tile_le_of_uses3 hstg ?_
      rcases hshort with h | h <;> omega
    have hpc : 2105 < d.site.pc := by
      by_contra hle
      by_cases h14 : d.site.pc ≤ 1402
      · cases hstart h14
      · have := hreg1 (by omega) (by omega)
        omega
    refine blk_of_earlier hsound hs hT R hmax hσ hll hld ?_ ?_
    · intro k pc hx
      obtain ⟨dk, hdk, -, htk⟩ := exit_state hsound hs R hX hll hx
      have := hbound k dk hdk
      rw [htk, hTg _ hld] at this
      omega
    · intro dh hσh
      have hle := hbound _ dh hσh
      obtain ⟨-, hr2, hr3⟩ := R.region hll hσh
      have hend : ¬ 3113 ≤ dh.site.pc := fun h3 => by
        have := R.tile_end hll hσh h3
        rw [hTg _ hld] at this
        omega
      refine time_lt_of_tile_le (sub_le _) hle hgle (by omega) (by omega) fun _ => ?_
      by_contra hge
      by_cases h29 : dh.site.pc ≤ 2944
      · have := hr2 (by omega) h29
        omega
      · have := hr3 (by omega) (by omega)
        omega
  | loadEmpty s =>
    simp only [Bar.delta] at hpar
    simp only [roundOf] at hround
    have hgl : g = loadLeader L (g / L.block) := hpoller
    obtain ⟨hph, a, hunits⟩ := F.load.empty_blocked F.init F.bars (noEvents hX) hX hb hcg s
      hst (by rw [← hgl]; exact hpar)
    rw [← hgl] at hph
    rw [MbarRing.Unit.unitsOf_eq_arrivals hX
      (F.load.empty_faultFree F.init F.bars (noEvents hX) hX hb hcg s)] at hunits
    have hh := computeThread_lt (L := L) hb hcg a
    have hhd := computeThread_div (L := L) (c := g / L.block) hb a
    have hhm : computeThread L (g / L.block) a % L.block < 128 := by
      unfold computeThread
      rw [thr_mod hb (by have := a.isLt; omega)]
      exact a.isLt
    have hbound : ∀ k dk,
        Frame.stateAt (Thread.code L) X (computeThread L (g / L.block) a) k = some (some dk) →
          I.tile (computeThread L (g / L.block) a) dk < I.tile g d := by
      intro k dk hdk
      have ha := R.arrLoadEmpty hh hdk hhm s
      rw [hhd] at ha
      have h1 := arrivals_take_le ((Bar.loadEmpty s).loc L (g / L.block))
        (X.tr (computeThread L (g / L.block) a)) k
      exact tile_lt_of_uses (n := 3) (s := s.val) (by omega)
    have hpc : 1402 < d.site.pc := by
      by_contra hle
      cases hstart (by omega)
    refine blk_of_earlier hsound hs hT R hmax hσ hh hhd ?_ ?_
    · intro k pc hx
      obtain ⟨dk, hdk, -, htk⟩ := exit_state hsound hs R hX hh hx
      have := hbound k dk hdk
      rw [htk, hTg _ hhd] at this
      omega
    · intro dh hσh
      have hlt := hbound _ dh hσh
      have hend : ¬ 3113 ≤ dh.site.pc := fun h3 => by
        have := R.tile_end hh hσh h3
        rw [hTg _ hhd] at this
        omega
      exact timeAt_lt_tile (by omega) (sub_le _) hlt hgle hpc
  | storeFull s =>
    simp only [Bar.delta, Nat.add_zero] at hpar
    simp only [roundOf] at hround
    have hgl : g = storeLeader L (g / L.block) := hpoller
    obtain ⟨hstg, htlt⟩ := hstage.2 s rfl
    obtain ⟨hph, a, hunits⟩ := F.store.full_blocked F.init F.bars (noEvents hX) hX hb hcg s
      hst (by rw [← hgl]; exact hpar)
    rw [← hgl] at hph
    rw [MbarRing.Unit.unitsOf_eq_arrivals hX
      (F.store.full_faultFree F.init F.bars (noEvents hX) hX hb hcg s)] at hunits
    have hh := computeThread_lt (L := L) hb hcg a
    have hhd := computeThread_div (L := L) (c := g / L.block) hb a
    have hhm : computeThread L (g / L.block) a % L.block < 128 := by
      unfold computeThread
      rw [thr_mod hb (by have := a.isLt; omega)]
      exact a.isLt
    have hbound : ∀ k dk,
        Frame.stateAt (Thread.code L) X (computeThread L (g / L.block) a) k = some (some dk) →
          I.tile (computeThread L (g / L.block) a) dk ≤ I.tile g d := by
      intro k dk hdk
      have ha := R.arrStoreFull hh hdk hhm s
      rw [hhd] at ha
      have h1 := arrivals_take_le ((Bar.storeFull s).loc L (g / L.block))
        (X.tr (computeThread L (g / L.block) a)) k
      exact tile_le_of_uses2 hstg (by omega)
    have hgm : g % L.block = 160 := by rw [hgl]; exact hsm
    have hpc : 2944 < d.site.pc := by
      by_contra hle
      by_cases h14 : d.site.pc ≤ 1402
      · cases hstart h14
      · by_cases h21 : d.site.pc ≤ 2105
        · have := hreg1 (by omega) h21
          omega
        · have := hreg2 (by omega) (by omega)
          omega
    refine blk_of_earlier hsound hs hT R hmax hσ hh hhd ?_ ?_
    · intro k pc hx
      obtain ⟨dk, hdk, -, htk⟩ := exit_state hsound hs R hX hh hx
      have := hbound k dk hdk
      rw [htk, hTg _ hhd] at this
      omega
    · intro dh hσh
      have hle := hbound _ dh hσh
      obtain ⟨hr1, -, hr3⟩ := R.region hh hσh
      have hend : ¬ 3113 ≤ dh.site.pc := fun h3 => by
        have := R.tile_end hh hσh h3
        rw [hTg _ hhd] at this
        omega
      refine time_lt_of_tile_le (sub_le _) hle hgle (by omega) (by omega) fun _ => ?_
      by_contra hge
      have := hr3 (by omega) (by omega)
      omega
  | storeEmpty s =>
    obtain ⟨-, hgc⟩ := hpoller
    simp only [Bar.delta] at hpar
    simp only [roundOf] at hround
    have hga : computeThread L (g / L.block) ⟨g % L.block, hgc⟩ = g := thr_eq hb g
    obtain ⟨hph, hunits⟩ := F.store.empty_blocked F.init F.bars (noEvents hX) hX hb hcg s
      ⟨g % L.block, hgc⟩ hst (by rw [hga]; exact hpar)
    rw [hga] at hph
    rw [MbarRing.Unit.unitsOf_eq_arrivals hX
      (F.store.empty_faultFree F.init F.bars (noEvents hX) hX hb hcg s)] at hunits
    have hbound : ∀ k dk,
        Frame.stateAt (Thread.code L) X (storeLeader L (g / L.block)) k = some (some dk) →
          I.tile (storeLeader L (g / L.block)) dk < I.tile g d := by
      intro k dk hdk
      have ha := R.arrStoreEmpty hsl hdk (by rw [hsd]) s
      rw [hsd] at ha
      have h1 := arrivals_take_le ((Bar.storeEmpty s).loc L (g / L.block))
        (X.tr (storeLeader L (g / L.block))) k
      exact tile_lt_of_uses (n := 2) (s := s.val) (by omega)
    have hpc : 1402 < d.site.pc := by
      by_contra hle
      cases hstart (by omega)
    refine blk_of_earlier hsound hs hT R hmax hσ hsl hsd ?_ ?_
    · intro k pc hx
      obtain ⟨dk, hdk, -, htk⟩ := exit_state hsound hs R hX hsl hx
      have := hbound k dk hdk
      rw [htk, hTg _ hsd] at this
      omega
    · intro dh hσh
      have hlt := hbound _ dh hσh
      have hend : ¬ 3113 ≤ dh.site.pc := fun h3 => by
        have := R.tile_end hsl hσh h3
        rw [hTg _ hsd] at this
        omega
      exact timeAt_lt_tile (by omega) (sub_le _) hlt hgle hpc
  | state =>
    simp only [Bar.delta, Nat.add_zero] at hpar
    simp only [roundOf] at hround
    have hph : before.phase = 0 := by
      have := state_phase_le hpre F hX hcg hst
      omega
    have hshort := F.state.short F.init F.bars (noEvents hX) hX hb hcg hno hst
    rw [hph] at hshort
    have hbound : ∀ k dk,
        Frame.stateAt (Thread.code L) X (loadLeader L (g / L.block)) k = some (some dk) →
          dk.site.pc ≤ 379 := by
      intro k dk hdk
      by_contra hgt
      obtain ⟨ha1, ha2⟩ := R.arrState hll hdk (by rw [hld]) (by omega)
      rw [hld] at ha1 ha2
      have h1 := arrivals_take_le (Bar.state.loc L (g / L.block))
        (X.tr (loadLeader L (g / L.block))) k
      have h2 := issues_take_le (Bar.state.loc L (g / L.block))
        (X.tr (loadLeader L (g / L.block))) k
      rcases hshort with h | h <;> omega
    obtain ⟨j', hj'⟩ := site_of_poll hc
    have h384 : 384 ≤ d.site.pc := by rw [hj']; exact mbarWait_pc_ge j'
    refine blk_of_earlier hsound hs hT R hmax hσ hll hld ?_ ?_
    · intro k pc hx
      obtain ⟨dk, hdk, hpk, -⟩ := exit_state hsound hs R hX hll hx
      have := hbound k dk hdk
      omega
    · intro dh hσh
      have := hbound _ dh hσh
      exact timeAt_lt_pc (by omega) (sub_le _) (by omega)

end

end PTX.Kernels.FlashKdaFwd.Proof.Progress
