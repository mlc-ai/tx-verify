-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.Waits
public import Kernels.FlashAttn4Fwd.Proof.Progress.NextFire
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Tmem
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Tc
public import Lemmas.Kernel.NextInOrder
public import Lemmas.Step.DrainInOrder
public import Lemmas.Tmem.AllocResult
public import Lemmas.Tmem.PairProtocol
public import Lemmas.Kernel.Progress.Bar

@[expose] public section

/-! # Progress at the paired Tensor Memory operations

Warp 12 of the two CTAs of a cluster makes the pair's three resource operations
(`TmemFacts.event`, `warpOps`): the allocation, the relinquishment and the deallocation,
`cta_group::2`.
An operation is covered when the two CTAs' allocators performed the two requests of its pair
and paired them (`Tmem.Pair.Covered`); a thread returns from an operation once it is performed
and, if its return waits for it, covered (`Tmem.Pair.ReturnReady`).

A covered allocation can still wait for its lane-0 address store. If the leader has issued
that event, it already publishes the result. Otherwise the leader can return from allocation by
issuing the store. For an uncovered operation, take the pair's first operation number `n` whose
operations are not all made and covered (`pair_dichotomy`, through `Tmem.Pair.PairDone`).
If every lane of the pair has made its
`n`-th operation, a step completing them is ready (`Tmem.Pair.pair_ready`), recorded by a
counted extension (`tmem_ready_steps`; recording performs no commit arrive-on, so FA4's
assumptions keep their constraints, `Assumption.WfStep.quiet`). Otherwise a lane of the pair
has made at most `n` operations; it has not exited (a lane of warp 12 exits after its three,
`TmemFacts.exit`), so it is pending, and it is no later than the blocked thread's state before
its operation (`TmemWaitFacts.lag`), which is earlier than the thread's state after it
(`TcWaitFacts.after`): the lane ranks below the blocked thread (`tmemWait_steps`). The same
dichotomy passes an open `.tmem` obligation to a pending lane (`tmem_obl_dichotomy`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX PTX.Tmem.Pair Classical

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The resource operations are warp 12's**, as `TmemAlloc.warpOps` in the protocol layer. -/
theorem warpOps (hpre : Pre P L mem0) (ht : TmemFacts L X) : TmemWarpOps L X 12 where
  launch := hpre.oneDimLaunch
  cluster := hpre.cluster
  warp_lt := by rw [hpre.block]; decide
  event hg he := by
    obtain ⟨h1, h2, h3, -⟩ := ht.event hg he
    exact ⟨h1, h2, h3⟩

/-- A safe execution has no aligned mismatch. -/
theorem safe_noAligned (hs : ¬ Unsafe L kernel asms mem0 X) : ¬ AlignedMismatch L kernel X :=
  fun h => hs (by simp [Unsafe, h])

/-- **A ready step steps**: recording a ready request or pairing is a counted extension of the
execution, which performs no commit arrive-on. -/
theorem tmem_ready_steps (hmax : Maximal L kernel asms mem0 X)
    (hR : (∃ c r, Step.EntryReady L X c r) ∨ ∃ q, Step.PairingReady L X q)
    {o : Descent.Obligation} :
    Sched.Steps (timed L) mem0 X o := by
  rcases hR with ⟨c, r, hR⟩ | ⟨q, hR⟩
  · obtain ⟨Y, hY, hle, hsize, -⟩ := Step.entry_counted hmax.1 hR
      (asms_wfInOrder _ _ hmax.1 le_recordEntry (Execution.notifiedInOrder_of_eq rfl))
    exact .inl ⟨Y, hY, hle, hsize⟩
  · obtain ⟨Y, hY, hle, hsize, -⟩ := Step.pairing_counted hmax.1 hR
      (asms_wfInOrder _ _ hmax.1 le_recordPairing (Execution.notifiedInOrder_of_eq rfl))
    exact .inl ⟨Y, hY, hle, hsize⟩

/-- The `n`-th operations of the pair of `key` are made and covered. -/
def PairDone (L : Launch) (X : Execution) (key n : Nat) : Prop :=
  ∀ s, s < 2 → ∀ ℓ : Fin 32, ∃ j, TmemOp X (pairLane L 12 key s ℓ) n j ∧
    Covered L X (pairLane L 12 key s ℓ, j)

/-- **The dichotomy at an uncovered operation**: a ready step of its pair, or a pending lane of
warp 12 of a CTA of the pair that has made no more operations than the uncovered one's. -/
theorem pair_dichotomy (hpre : Pre P L mem0) (htm : TmemFacts L X)
    (hX : Consistent L kernel asms mem0 X) (htc : ¬ AlignedMismatch L kernel X)
    {g j pc : Nat} {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request} (hg : g < L.threads)
    (he : X.get (g, j) = some ⟨pc, .tc (.resource grp dst act)⟩) (hn : ¬ Covered L X (g, j)) :
    ((∃ c r, Step.EntryReady L X c r) ∨ ∃ q, Step.PairingReady L X q) ∨
      ∃ h, Frame.Pending L X h ∧ warpOf L h = 12 ∧ ctaOf L h / 2 = ctaOf L g / 2 ∧
        tmemOps (X.tr h) ≤ tmemOps ((X.tr g).take j) := by
  have hb := hpre.block
  have hgr := hpre.grid
  have hcl := hpre.cluster
  have hto := warpOps hpre htm
  obtain ⟨h0, -, hsh⟩ := hto.event hg he
  have hm3 := lt_of_tmemShape hsh
  have hgc : g / L.block < L.grid :=
    (Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa [Launch.threads] using hg)
  generalize hq : g / L.block = q at hgc
  obtain ⟨key, hkd⟩ : ∃ key, key = q - q % 2 := ⟨_, rfl⟩
  have hkey : key % 2 = 0 := by omega
  have hk : key + 1 < L.grid := by omega
  obtain ⟨s0, ℓ0, hs0, hℓ0, hg0⟩ := pairLane_of (w := 12) hkey (by rw [hq]; omega) h0
  have hop0 : TmemOp X (pairLane L 12 key s0 ℓ0) (tmemOps ((X.tr g).take j)) j := by
    rw [← hg0]
    exact ⟨⟨_, _, _, _, he⟩, rfl⟩
  have hnd : ¬ PairDone L X key (tmemOps ((X.tr g).take j)) := by
    intro hd
    obtain ⟨j', hop', hc⟩ := hd s0 hs0 ⟨ℓ0, hℓ0⟩
    have hc' : Covered L X (pairLane L 12 key s0 ℓ0, j) := by
      rw [tmemOp_unique hop' hop0] at hc
      exact hc
    rw [← hg0] at hc'
    exact hn hc'
  have hex : ∃ n, ¬ PairDone L X key n := ⟨_, hnd⟩
  obtain ⟨n, hnd', hdone⟩ : ∃ n, ¬ PairDone L X key n ∧ ∀ m < n, PairDone L X key m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => not_not.mp (Nat.find_min hex hm)⟩
  have hnm : n ≤ tmemOps ((X.tr g).take j) := by
    by_contra hlt
    exact hnd (hdone _ (by omega))
  by_cases hiss : ∀ s, s < 2 → ∀ ℓ : Fin 32, n < tmemOps (X.tr (pairLane L 12 key s ℓ))
  · left
    simp only [PairDone, not_forall, not_exists, not_and] at hnd'
    obtain ⟨s1, hs1, ℓ1, hno⟩ := hnd'
    obtain ⟨j1, hop1⟩ := tmemOp_exists (hiss s1 hs1 ℓ1)
    refine pair_ready hX hto htc (n := n) hkey hk (fun s hs ℓ => ?_)
      (fun m hm s hs ℓ j hop => ?_)
    · obtain ⟨jj, hopj⟩ := tmemOp_exists (hiss s hs ℓ)
      exact ⟨jj, hopj, fun hc => hno j1 hop1
        (covered_all hX hto hkey hs ℓ.isLt hs1 ℓ1.isLt hopj hc hop1)⟩
    · obtain ⟨j', hop', hc⟩ := hdone m hm s hs ℓ
      rwa [tmemOp_unique hop hop']
  · right
    push Not at hiss
    obtain ⟨s, hs, ℓ, hle⟩ := hiss
    have hℓ := ℓ.isLt
    have hdm := pairLane_div_mod hto (key := key) (s := s) ℓ.isLt
    have hlt := pairLane_lt hto hk hs ℓ.isLt
    have hne : X.tr g ≠ [] := by
      intro h0'
      have := len_of_get he
      rw [h0'] at this
      simp at this
    refine ⟨_, Sched.pending_of_noExit hX hg hne hlt ?_ ?_, ?_, ?_, by omega⟩
    · rw [hdm.1]
      simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hcl]
      rw [hq]
      omega
    · intro jx pc' hx
      have h3 := htm.exit hlt (by simp only [warpOf]; rw [hdm.2]; omega) hx
      have h4 : tmemOps ((X.tr (pairLane L 12 key s ℓ)).take jx) ≤
          tmemOps (X.tr (pairLane L 12 key s ℓ)) :=
        (List.take_sublist _ _).countP_le
      omega
    · simp only [warpOf]
      rw [hdm.2]
      omega
    · simp only [ctaOf]
      rw [hdm.1, hq]
      omega

/-- **An open obligation of the pair**: an uncovered operation has a ready step, or a pending
lane of warp 12 of its pair. -/
theorem tmem_obl_dichotomy (hpre : Pre P L mem0) (htm : TmemFacts L X)
    (hX : Consistent L kernel asms mem0 X) (htc : ¬ AlignedMismatch L kernel X)
    (ho : Descent.Obl L X .tmem) :
    ((∃ c r, Step.EntryReady L X c r) ∨ ∃ q, Step.PairingReady L X q) ∨
      ∃ h, Frame.Pending L X h ∧ warpOf L h = 12 := by
  simp only [Descent.Obl, Drained, not_forall] at ho
  obtain ⟨i, pc, group, dst, action, hget, hn⟩ := ho
  rcases pair_dichotomy hpre htm hX htc (Frame.lt_of_get hX hget) hget hn with
    hR | ⟨h, hp, hw, -⟩
  · exact .inl hR
  · exact .inr ⟨h, hp, hw⟩

/-- A covered allocation already has a result store, or its released leader can issue one. -/
private theorem publication_steps (hpre : Pre P L mem0) (htr : Frame.Tracked (code L) X)
    (htm : TmemFacts L X) (hNext : NextCtx L mem0 X) {i : EvId}
    {site n : Nat} {group : CtaGroup} {dst : Option Loc}
    (he : X.get i = some ⟨site, .tc (.resource group dst (.alloc n))⟩)
    (hc : Covered L X i) (hMissing : ¬ ∃ store out, AllocResult L X store i out)
    {o : Descent.Obligation} :
    Sched.Steps (timed L) mem0 X o := by
  have hX := hNext.max.1
  obtain ⟨ws, hws, w, hw, lane, rfl⟩ := hc
  obtain ⟨grp, hv⟩ := hws.valid hX.tmemPair hw
  have hreq := (hv.2.2.1 lane).symm.trans he
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hreq
  have halloc := hreq.2.2.2
  let leader := w.event L 0
  have hLead := hv.2.2.1 0
  have hprop := WarpRequest.event_props hv 0
  have hbound : leader.1 < L.threads := hprop.2.2
  have hzero : laneOf L leader.1 = 0 := by
    have hlt : w.warp * 32 < L.block := by have := hv.2.1; omega
    simp only [leader, laneOf, WarpRequest.event, Fin.val_zero, Nat.add_zero]
    rw [Nat.mul_comm w.cta, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    simp
  have hLead' : X.get leader = some ⟨w.pc, .tc (.resource grp w.dst (.alloc n))⟩ := by
    simpa only [halloc] using hLead
  obtain ⟨-, -, -, hdst⟩ := htm.event hbound hLead'
  have hdst := hdst n rfl
  have hsound := (prologueFacts hpre hX).sound
  have hindex : leader.2 < (X.tr leader.1).length := len_of_get hLead'
  by_cases hLater : leader.2 + 1 < (X.tr leader.1).length
  · have hEvt : X.get (leader.1, leader.2 + 1) =
        some ((X.tr leader.1)[leader.2 + 1]'hLater) :=
      List.getElem?_eq_some_iff.mpr ⟨hLater, rfl⟩
    obtain ⟨bytes, hStore⟩ := hNext.facts.alloc_result_event hNext.noUb hLead' hEvt hzero
    exact (hMissing ⟨_, baseLoc L (ctaOf L leader.1),
      AllocResult.of_warpRequest hv halloc hdst rfl hprop.1 hStore lane⟩).elim
  · have hlast : (X.tr leader.1).length - 1 = leader.2 := by omega
    have hLeadLast :
        X.get (leader.1, (X.tr leader.1).length - 1) =
          some ⟨w.pc, .tc (.resource grp w.dst (.alloc n))⟩ := by
      rw [hlast]
      exact hLead'
    have hCover : Covered L X leader := ⟨ws, hws, w, hw, 0, rfl⟩
    have hReady := ReturnReady.ready hX.tmemPair hLead'
      ⟨hCover.performed hX.tmemPair, fun _ => hCover⟩
      (fun _ _ hl => (hl hzero).elim)
    have hRel : Step.Released L X leader.1 := ⟨fun _ _ _ _ => by
      rw [hlast]
      exact hReady⟩
    have hp : Frame.Pending L X leader.1 := by
      refine ⟨hbound, Sched.not_canceled_of_peer hX hbound ?_ rfl, fun _ hExit => ?_⟩
      · intro hnil
        simp [hnil] at hindex
      · have := (Sched.exit_get hExit).symm.trans hLeadLast
        cases this
    cases hσ : Frame.stateAt (code L) X leader.1 (X.tr leader.1).length with
    | none => exact Descent.dead_steps_inOrder asms_wfStep hNext.max hNext.noUb hsound hp hσ hRel
    | some σ =>
      cases σ with
      | none => exact (htr _ _ hbound hσ).elim
      | some d =>
        rcases hNext.facts.alloc_next hbound hLeadLast hσ with hk | hn
        · exact allocStore_next_steps hNext hp hσ hk hRel
        · exact (hn hzero).elim

/-- **Progress at a paired Tensor Memory operation.** A pending thread whose last event is a
paired operation that cannot return steps by publishing its allocation result or recording a ready
step of its pair. Otherwise a lane of the pair has made no more operations, is pending and ranks
earlier. -/
theorem tmemWait_steps (hpre : Pre P L mem0)
    (htr : Frame.Tracked (code L) X) (htm : TmemFacts L X) (hw : TmemWaitFacts L X)
    (htc : TcWaitFacts L X) (hNext : NextCtx L mem0 X) {g : Nat}
    (hp : Frame.Pending L X g) (hrel : ¬ Step.Released L X g) (htw : Sched.TmemWait L X g) :
    Sched.Steps (timed L) mem0 X (.thread g) := by
  have hmax := hNext.max
  have hX := hmax.1
  have hsafe := hNext.safe
  have hub := hNext.noUb
  obtain ⟨pc, group, dst, action, hlast, hnr⟩ := htw
  by_cases hnc : Covered L X (g, (X.tr g).length - 1)
  · have hm : ∃ n, action = .alloc n ∧
        ¬ ∃ store out, AllocResult L X store (g, (X.tr g).length - 1) out := by
      by_contra hn
      apply hnr
      refine ReturnReady.ready hX.tmemPair hlast ⟨hnc.performed hX.tmemPair, fun _ => hnc⟩ ?_
      intro n hnAlloc _
      by_contra hMissing
      exact hn ⟨n, hnAlloc, hMissing⟩
    obtain ⟨n, rfl, hMissing⟩ := hm
    exact publication_steps hpre htr htm hNext hlast hnc hMissing
  have hg := hp.1
  rcases pair_dichotomy hpre htm hX (safe_noAligned hsafe) hg hlast hnc with
    hR | ⟨h, hph, hh12, hhc, hle⟩
  · exact tmem_ready_steps hmax hR
  · have hlen : 0 < (X.tr g).length := by
      have : (X.tr g).length - 1 < (X.tr g).length := len_of_get hlast
      omega
    obtain ⟨d, hd⟩ := Frame.state_of_noUb (prologueFacts hpre hX).sound hX htr hub hlast
    have h1 : endTime L X h ≤ stateTime L g d :=
      hw.lag hg hph.1 hh12 hhc ⟨_, _, _, _, hlast⟩ rfl hd hle
    have h2 : stateTime L g d < endTime L X g :=
      Sched.threadTime_after (M := timed L) hlen hd (htc.after hg ⟨⟨_, hlast, rfl⟩, rfl⟩ hd)
    exact Sched.earlier_steps hmax hrel hph (by omega)

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
