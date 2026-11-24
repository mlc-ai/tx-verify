-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderTasks
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaCounts
public import Kernels.Fp16Gemm8192.Proof.Thread.ElectOnce
public import Kernels.Fp16Gemm8192.Proof.Thread.ExitSite
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerClc
public import Kernels.Fp16Gemm8192.Proof.Thread.AccExit
public import Kernels.Fp16Gemm8192.Proof.Thread.ReaderExitCons
public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # The tasks behind a load and before an exit arrival

Two projections of the roles' main invariants at any position of a run. A loader at a load has
polled each slot's empty barrier at most 32 times per task it is in, and every response it polled
before was read claiming a CTA (`LoaderTasks.Counts`: `rank`, `resp`, `rel`). An MMA thread at its
exit arrival has polled each slot's full barrier 32 times per successful response poll, its latest
response read claims no CTA, and without a response poll it is not on a leader CTA or lost its
warp's election (`Mma.Counts`: `commit`, `rank`, `task`, `held`, `exitPoll`); there its
accumulator commits are its successful response polls, and its reads after the earlier ones claim
(`accRound`, `claimsBefore`).

A consumer in its exit stage, at any position of its run, has polled its accumulator's full barrier
once per successful response poll, and its latest response read claims no CTA (`ClcPollInv`,
`Consumer.ConsRel`, `ConsInv`, `Consumer.ReadInv`: `cons_exit_stage_fact`).

Two projections at the exit of a thread whose trace ends with it, from the state the exit fires
at. An elected loader has drained: its successful empty polls are 32 per response poll plus the
drain's one on each slot, and its latest response read claims no CTA (`LoaderTasks.Counts`:
`rank`, `exitTasks`, `heldX`, `leaveX`, with `LoaderTasks.run`). A consumer is in its exit stage
(`cons_exit_tiles_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An event of a prefix `take k` is the trace's event. -/
theorem take_get {es : List Event} {k j : Nat} {e : Event} (h : (es.take k)[j]? = some e) :
    j < k ∧ es[j]? = some e := by
  have hj : j < (es.take k).length := (List.getElem?_eq_some_iff.mp h).1
  simp only [List.length_take] at hj
  rw [List.getElem?_take_of_lt (by omega)] at h
  exact ⟨by omega, h⟩

/-- **A loader at a load.** Its successful empty polls on each slot are at most 32 per task up to
the current one, and each response poll before is followed by a read of a response that claims a
CTA. -/
theorem loader_load_tasks_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {l : Loader.D} {b : Fin 8} {j : Fin 3} (hg : g < L.threads)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.loader l)))) (hs : l.site = .load b j) :
    (∀ s : Fin 4, okPolls (Loader.emptyOf L g s) ((X.tr g).take k) ≤
      32 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) + 32) ∧
    ∀ j' pc p acq sc, j' < k →
      X.get (g, j') =
        some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      ∃ pcr, ∃ src : Acc, ∃ bs rr, X.get (g, j' + 1) = some ⟨pcr, .rd src bs⟩ ∧
        src.SameFootprint
          ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0, false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have c : LoaderTasks.Counts L g l ((X.tr g).take k) := LoaderTasks.run hpre hg htr k _ hσ
  refine ⟨fun s => ?_, ?_⟩
  · have hr := c.rank s
    have hR := c.resp
    unfold LoaderTasks.CountOK at hR
    rw [hs] at hR
    change okPolls (clcResp L g) _ = _ at hR
    change _ ≤ 32 * okPolls (clcResp L g) _ + 32
    have := s.isLt
    omega
  · intro j' pc p acq sc hj hw
    have hw' : ((X.tr g).take k)[j']? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ := by
      rw [List.getElem?_take_of_lt hj]; exact hw
    have hj1 : j' + 1 < ((X.tr g).take k).length := by
      have hlt := (List.getElem?_eq_some_iff.mp hw').1
      by_contra hcon
      have hlast : ((X.tr g).take k).getLast? =
          some ⟨pc, .wait (clcResp L g) p true acq sc⟩ := by
        rw [List.getLast?_eq_getElem?, show ((X.tr g).take k).length - 1 = j' by omega]
        exact hw'
      have hcl := c.rel.2 pc p acq sc hlast
      rw [hs] at hcl
      cases hcl
    have hLive : LoaderTasks.Live l := by
      unfold LoaderTasks.Live
      rw [hs]
      trivial
    obtain ⟨pcr, src, bs, rr, hr, h1, h2, h3, h4⟩ := c.rel.1 j' pc p acq sc hj1 hw' hLive
    obtain ⟨-, hr'⟩ := take_get hr
    exact ⟨pcr, src, bs, rr, hr', ⟨h1, h2⟩, h3, h4⟩

/-- **An MMA thread at its exit arrival.** Its successful polls of each slot's full barrier are 32
per successful response poll; after a response poll, its latest one is followed by a read of a
response that claims no CTA; without one, it is not on a leader CTA or lost its warp's election;
its commits to each slot's empty barrier are its full polls. -/
theorem mma_exit_tasks_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {m : Mma.D} (hg : g < L.threads)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.mma m)))) (hs : m.site = .exitArrive) :
    (∀ s : Fin 4,
      okPolls ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩ ((X.tr g).take k) =
      32 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k)) ∧
    (0 < okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) →
      ∃ j pc p acq sc pcr, ∃ a : Acc, ∃ bs rr, j + 1 < k ∧
        X.get (g, j) =
          some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
        X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ ∧
        a.SameFootprint
          ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0, false⟩ ∧
        Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr ∧
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 =
          okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k)) ∧
    (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) = 0 →
      Loader.leader L g = false ∨
        ∃ j pc mask inst lane, j < k ∧ X.Elect (g, j) pc mask inst lane ∧
          lane ≠ laneOf L g) ∧
    (∀ s : Fin 4, ((X.tr g).take k).countP
        (commitsTo ⟨.shared, g / L.block, L.sharedBase + 40 + 8 * s.val⟩) =
      okPolls ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩ ((X.tr g).take k)) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have c : Mma.Counts L g m ((X.tr g).take k) := threadCounts_run hpre hg htr k _ hσ
  have hdone : m.site.done = true := by rw [hs]; rfl
  refine ⟨fun s => ?_, fun hpos => ?_, fun hzero => ?_, fun s => ?_⟩
  · have hc := c.commit s
    have hr := c.rank s
    have ht := c.task
    have hp : Mma.pendingCommit m s = false := by simp [Mma.pendingCommit, hs]
    rw [hp] at hc
    simp only [Mma.taskPos, Mma.taskStarted, hs] at ht
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc
    change okPolls (Mma.fullOf L g s) _ = 32 * okPolls (Mma.respBar L g) _
    have := s.isLt
    omega
  · obtain ⟨rr, -, hheld, hx, hxn⟩ := c.held (by rw [hs]; decide) hpos
    obtain ⟨j, pc, p, acq, sc, pcr, a, bs, h1, h2, ha, hsz, hresp, hcnt⟩ := hheld
    have hx' := hx (by rw [hs]; decide) (by rw [hs]; decide)
    have hxn' := hxn hdone
    obtain ⟨hj1, h2'⟩ := take_get h2
    obtain ⟨-, h1'⟩ := take_get h1
    refine ⟨j, pc, p, acq, sc, pcr, a, bs, rr, hj1, h1', h2', ⟨ha, hsz⟩, hresp, ?_, ?_⟩
    · intro hcl
      apply hcl
      change Mma.firstOf rr = Loader.none32
      rw [← hx', hxn']
    · rw [List.take_take, Nat.min_eq_left (by omega)] at hcnt
      exact hcnt
  · rcases c.exitPoll hdone with h | h | ⟨e, he, mask, inst, lane, hk, hne⟩
    · change 0 < okPolls (Mma.respBar L g) _ at h
      change okPolls (Mma.respBar L g) _ = 0 at hzero
      omega
    · exact .inl h
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem he
      obtain ⟨hjk, hj'⟩ := take_get hj
      obtain ⟨pc, kind⟩ := e
      simp only at hk
      subst hk
      exact .inr ⟨j, pc, mask, inst, lane, hjk, hj', hne⟩
  · have hc := c.commit s
    have hp : Mma.pendingCommit m s = false := by simp [Mma.pendingCommit, hs]
    rw [hp] at hc
    simpa using hc

/-- **An MMA thread's reads claim.** At an MMA state, a successful response poll that is not the
thread's latest is followed by a read of a response that claims a CTA (`Mma.Counts.claimsBefore`).
-/
theorem mma_reads_claim (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {m : Mma.D} (hg : g < L.threads)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.mma m)))) :
    ∀ j pc p acq sc, X.get (g, j) =
        some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 <
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) →
      ∃ pcr, ∃ a : Acc, ∃ bs rr, X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ ∧
        a.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr := by
  intro j pc p acq sc hj hcnt
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have c : Mma.Counts L g m ((X.tr g).take k) := threadCounts_run hpre hg htr k _ hσ
  have hjk : j < k := by
    by_contra hge
    have := ((List.take_prefix_take_left (l := X.tr g) (show k ≤ j by omega)).sublist).countP_le
      (p := okPoll (Mma.respBar L g))
    change okPolls _ _ ≤ okPolls _ _ at this
    change okPolls (Mma.respBar L g) _ + 1 < okPolls (Mma.respBar L g) _ at hcnt
    omega
  have hj' : ((X.tr g).take k)[j]? =
      some ⟨pc, .wait (Mma.respBar L g) p true acq sc⟩ := by
    rw [List.getElem?_take_of_lt hjk]; exact hj
  have hcnt' : okPolls (Mma.respBar L g) (((X.tr g).take k).take j) + 1 <
      okPolls (Mma.respBar L g) ((X.tr g).take k) := by
    rw [List.take_take, Nat.min_eq_left hjk.le]; exact hcnt
  obtain ⟨pcr, a, bs, rr, h1, h2, h3, h4, h5⟩ := c.claimsBefore j pc p acq sc hj' hcnt'
  obtain ⟨-, h1'⟩ := take_get h1
  exact ⟨pcr, a, bs, rr, h1', ⟨h2, h3⟩, h4, h5⟩

/-- **An MMA thread at its exit arrival: its reads and accumulator commits.** Its accumulator
commits are its successful response polls, and a response poll that is not its latest is followed
by a read of a response that claims a CTA. -/
theorem mma_exit_reads_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {m : Mma.D} (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.mma m)))) (hs : m.site = .exitArrive) :
    ((X.tr g).take k).countP
        (commitsTo (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩)) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) ∧
    ∀ j pc p acq sc, X.get (g, j) =
        some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 <
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) →
      ∃ pcr, ∃ a : Acc, ∃ bs rr, X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ ∧
        a.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have c : Mma.Counts L g m ((X.tr g).take k) := threadCounts_run hpre hg htr k _ hσ
  have hrw := role_warp hpre hX hg k hk _ hσ
  simp only [roleWarp, Prologue.warpOf] at hrw
  refine ⟨?_, mma_reads_claim hpre hX hg hσ⟩
  · have hacc := c.accRound
    have ht := c.task
    rw [hs] at hacc
    simp only [Mma.taskPos, Mma.taskStarted, hs] at ht
    simp only [show Mma.Site.exitArrive ≠ Mma.Site.accCommit from by simp, ↓reduceIte,
      add_zero] at hacc
    rw [hrw.1] at hacc
    change _ = okPolls (Mma.respBar L g) _
    change _ = mcount L g _ / 128 at hacc
    change 128 * okPolls (Mma.respBar L g) _ + 0 = mcount L g _ + 128 * 0 at ht
    rw [show Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩ =
      Mma.accBar L g (g % L.block / 32 % 2) true from rfl, hacc]
    rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero] at ht
    rw [← ht, Nat.mul_div_cancel_left _ (by decide)]

/-- The trace of a thread that ended with its exit: the exit is its last event, and the trace
before it has the same successful polls. -/
theorem exit_split {g pc : Nat} (hlast : (X.tr g).getLast? = some ⟨pc, .exit⟩) :
    ∃ ys, X.tr g = ys ++ [⟨pc, .exit⟩] ∧ X.get (g, ys.length) = some ⟨pc, .exit⟩ ∧
      (X.tr g).take ys.length = ys ∧ ∀ m, okPolls m (X.tr g) = okPolls m ys := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
  refine ⟨ys, hys, ?_, ?_, fun m => ?_⟩
  · change (X.tr g)[ys.length]? = _
    rw [hys]
    simp
  · rw [hys, List.take_left' rfl]
  · rw [hys, okPolls_snoc]
    simp [okPoll, sourceWaitSuccess]

/-- An event of the trace before a thread's exit is the trace's event. -/
theorem exit_get_lt {g pc : Nat} {ys : List Event} (hys : X.tr g = ys ++ [⟨pc, .exit⟩])
    {j : Nat} {e : Event} (h : ys[j]? = some e) : X.get (g, j) = some e := by
  change (X.tr g)[j]? = _
  rw [hys, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- **An elected loader that exited.** It polled the response; its successful empty polls on each
slot are 32 per successful response poll, plus the drain's one; its latest successful response
poll is followed by a read of a response that claims no CTA. -/
theorem loader_exit_drain_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g pc : Nat} (hg : g < L.threads) (hw : g % L.block / 32 = 11)
    (hel : ∃ j pce mask inst, X.Elect (g, j) pce mask inst (laneOf L g))
    (hlast : (X.tr g).getLast? = some ⟨pc, .exit⟩) :
    0 < okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) ∧
    (∀ s : Fin 4, okPolls (InputRing.emptyLoc L (g / L.block) s) (X.tr g) =
      32 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) + 1) ∧
    ∃ j pcw p acq sc pcr, ∃ a : Acc, ∃ bs rr,
      X.get (g, j) = some ⟨pcw, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ ∧
      a.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr ∧
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
  obtain ⟨ys, hys, hget, htake, hok⟩ := exit_split hlast
  obtain ⟨d, hσd, hoff⟩ := exit_event_state' hpre hX hg hget
  have hyl : ys.length ≤ (X.tr g).length := by rw [hys]; simp
  obtain ⟨l, rfl⟩ : ∃ l, d = .inr (.loader l) := by
    rcases d with p | (l | m | sd | c)
    · simp [ThreadD.exitOff] at hoff
    all_goals have hrw := role_warp hpre hX hg ys.length hyl _ hσd
    all_goals simp only [roleWarp, Prologue.warpOf] at hrw
    · exact ⟨l, rfl⟩
    all_goals omega
  have hd : l.site.done = true := by
    simp only [ThreadD.exitOff, Loader.exitOff] at hoff
    revert hoff
    cases l.site <;> simp [Loader.Site.done]
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have c : LoaderTasks.Counts L g l ((X.tr g).take ys.length) :=
    LoaderTasks.run hpre hg htr ys.length _ hσd
  rw [htake] at c
  have hpos := loader_elected_polled hpre hX hg hel hσd hd
  rw [htake] at hpos
  obtain ⟨hL, hR⟩ := hpos
  have hT := c.exitTasks hd hL
  have hleave : l.site.leaving = true := by
    revert hd
    cases l.site <;> simp [Loader.Site.done, Loader.Site.leaving]
  obtain ⟨rr, hrr, hx⟩ := c.heldX (Or.inr (Or.inr hleave)) hR
  have hnone := c.leaveX hleave hR
  obtain ⟨j, pcw, p, acq, sc, pcr, a, bs, h1, h2, ha, hsz, hr, hcnt⟩ := hrr
  simp only [hok]
  refine ⟨hR, fun s => ?_, j, pcw, p, acq, sc, pcr, a, bs, rr, exit_get_lt hys h1,
    exit_get_lt hys h2, ⟨ha, hsz⟩, hr, ?_, ?_⟩
  · have hr := c.rank s
    change okPolls (InputRing.emptyLoc L (g / L.block) s) ys = _ at hr
    change _ = 32 * okPolls (clcResp L g) ys + 1
    have := s.isLt
    omega
  · intro hcl
    have hfo : LoaderTasks.firstOfL rr = Loader.none32 := by rw [← hx]; exact hnone
    unfold LoaderTasks.firstOfL at hfo
    exact hcl hfo
  · have hjl : j ≤ ys.length := by
      have := (List.getElem?_eq_some_iff.mp h1).1
      omega
    rw [hys, List.take_append_of_le_length hjl]
    exact hcnt

/-- **A consumer in its exit stage.** Its successful polls of its accumulator's full barrier are its
successful response polls, and its latest successful response poll is followed by a read of a
response that claims no CTA. -/
theorem cons_exit_stage_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {c : Consumer.D} (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.cons c))))
    (hx : Consumer.exitOff c ≠ none) :
    okPolls (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩) ((X.tr g).take k) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) ∧
    ∃ j pcw p acq sc pcr, ∃ a : Acc, ∃ bs rr,
      X.get (g, j) = some ⟨pcw, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ ∧
      a.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr ∧
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hT := clcPoll_inv hpre hg htr k _ hσ
  have hA := Consumer.accInv hpre hg htr k _ hσ
  have hI := consInv hpre hg htr k _ hσ
  have hRd := Consumer.readInv_of hpre hX hg hσ
  obtain ⟨-, hT2, -⟩ := hT
  obtain ⟨hC, -, -⟩ := hA
  have hopen : Consumer.tileOpen c = 0 ∧ Consumer.holds c = 0 := by
    unfold Consumer.exitOff at hx
    unfold Consumer.tileOpen Consumer.holds
    cases hs : c.site <;> simp_all
  have hw := role_warp hpre hX hg k hk _ hσ
  simp only [roleWarp, Prologue.warpOf] at hw
  have hacc : Consumer.accIdx L g < 2 := by
    simp only [Consumer.accIdx, Consumer.tidOf]
    omega
  have hC1 := hC (Consumer.accIdx L g) hacc
  simp only [↓reduceIte] at hC1
  obtain ⟨j, pcw, p, acq, sc, pcr, a, bs, rr, h1, h2, ha, hsz, hr, hnc⟩ :=
    hI.2.2.1 (doomed_of_exitOff hx)
  have hlat := (hRd.1.1 j pcw p acq sc pcr a bs rr h1 h2 ha hsz hr hnc).1
  obtain ⟨hjk, h1'⟩ := take_get h1
  obtain ⟨-, h2'⟩ := take_get h2
  refine ⟨?_, j, pcw, p, acq, sc, pcr, a, bs, rr, h1', h2', ⟨ha, hsz⟩, hr, hnc, ?_⟩
  · change okPolls (Consumer.accFull L g (Consumer.accIdx L g)) _ = okPolls (clcResp L g) _
    omega
  · rw [List.take_take, Nat.min_eq_left hjk.le] at hlat
    exact hlat

/-- **A consumer that exited.** Its successful polls of its accumulator's full barrier are its
successful response polls, and its latest successful response poll is followed by a read of a
response that claims no CTA. -/
theorem cons_exit_tiles_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g pc : Nat} (hg : g < L.threads) (hw : g % L.block / 32 < 8)
    (hlast : (X.tr g).getLast? = some ⟨pc, .exit⟩) :
    okPolls (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩) (X.tr g) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) ∧
    ∃ j pcw p acq sc pcr, ∃ a : Acc, ∃ bs rr,
      X.get (g, j) = some ⟨pcw, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ ∧
      a.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr ∧
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
  obtain ⟨ys, hys, hget, htake, hok⟩ := exit_split hlast
  obtain ⟨d, hσ, hoff⟩ := exit_event_state' hpre hX hg hget
  have hyl : ys.length ≤ (X.tr g).length := by rw [hys]; simp
  obtain ⟨c, rfl⟩ : ∃ c, d = .inr (.cons c) := by
    rcases d with p | (l | m | sd | c)
    · simp [ThreadD.exitOff] at hoff
    all_goals have hrw := role_warp hpre hX hg ys.length hyl _ hσ
    all_goals simp only [roleWarp, Prologue.warpOf] at hrw
    · omega
    · omega
    · omega
    · exact ⟨c, rfl⟩
  have h := cons_exit_stage_fact hpre hX hg hyl hσ hoff
  rw [htake, ← hok, ← hok] at h
  exact h

/-- **A consumer's TMA stores along its run** (`Consumer.TmaRel`). -/
theorem cons_tmas_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat}
    {c : Consumer.D} (hg : g < L.threads) (hσ : Frame.stateAt (code L) X g k =
      some (some (.inr (.cons c)))) :
    Consumer.TmaRel L g c ((X.tr g).take k) :=
  (consInv hpre hg (Frame.trace (fun _ => sound hpre) hX hg) k _ hσ).2.2.2.2.2.2.2.2.2.2.1

/-- **A group's first consumer thread that exited** issued, on a trace without undefined behaviour,
eight TMA stores per successful response poll: one per slice of each of its tiles. -/
theorem cons_exit_tmas_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g pc : Nat} (hg : g < L.threads) (hw : g % L.block / 32 < 8) (hf : Consumer.first L g = true)
    (hub : ∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩)
    (hlast : (X.tr g).getLast? = some ⟨pc, .exit⟩) :
    storeIssues (X.tr g) = 8 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
  obtain ⟨ys, hys, hget, htake, hok⟩ := exit_split hlast
  obtain ⟨d, hσ, hoff⟩ := exit_event_state' hpre hX hg hget
  have hyl : ys.length ≤ (X.tr g).length := by rw [hys]; simp
  obtain ⟨c, rfl⟩ : ∃ c, d = .inr (.cons c) := by
    rcases d with p | (l | m | sd | c)
    · simp [ThreadD.exitOff] at hoff
    all_goals have hrw := role_warp hpre hX hg ys.length hyl _ hσ
    all_goals simp only [roleWarp, Prologue.warpOf] at hrw
    · omega
    · omega
    · omega
    · exact ⟨c, rfl⟩
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hI := consInv hpre hg htr ys.length _ hσ
  have hT := clcPoll_inv hpre hg htr ys.length _ hσ
  rw [htake] at hI hT
  obtain ⟨⟨-, hO⟩, -, -, -, -, ⟨hT1, -⟩, -, -, -, -, ⟨-, hM⟩, -⟩ := hI
  obtain ⟨-, hP, -⟩ := hT
  have hnu : ∀ e ∈ ys, ∀ f, e.kind ≠ .ub f := by
    intro e he f hk
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    have hjl : j < ys.length := (List.getElem?_eq_some_iff.mp hj).1
    apply hub j e.pc f
    change (X.tr g)[j]? = _
    rw [hys, List.getElem?_append_left hjl, hj, ← hk]
  have hM2 := hM hnu
  simp only [hf, ↓reduceIte] at hM2
  have hz : c.outLag = 0 ∧ c.inEpi = 0 ∧ c.outPhase = 0 ∧ c.tmaPend = 0 ∧
      Consumer.tileOpen c = 0 := by
    change Consumer.exitOff c ≠ none at hoff
    unfold Consumer.exitOff at hoff
    unfold Consumer.D.outLag Consumer.D.inEpi Consumer.D.outPhase Consumer.D.tmaPend
      Consumer.tileOpen
    cases hs : c.site <;> simp_all
  have hst : storeIssues (X.tr g) = storeIssues ys := by
    rw [hys, storeIssues_snoc]
    simp [isTensorStore]
  rw [hst, hok]
  change storeIssues ys = 8 * okPolls (clcResp L g) ys
  omega

end
end PTX.Kernels.Fp16Gemm8192.Proof
