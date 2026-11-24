-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.MemoryFacts
public import Kernels.TcGemm.Proof.Safety.Tmem
public import Lemmas.Kernel.SharedLifetime
public import Lemmas.Flow.SpinsAtLoop

@[expose] public section

/-! # The mbarrier, bulk-copy and commit branches of `Unsafe`

No record faults and every record follows its published initialization (`Protocol/Mbar.lean`).
Each copy follows the initialization of `bar0` through the proxy fence (`copy_initialized`). No
access touches an mbarrier, and every mbarrier is allocated. The commit targets `bar1`,
initialized and published before it (`no_commit_unsafe`). Together these are
`no_tma_unsafe`.

Every shared-memory use is in CTA 0, its issuer's CTA. Thread 0 exits only after its successful
polls of `bar0` and `bar1` (`exit0_of_exited`), which observe the copies' notifications
(`copy_finished`), the MMA's completion (`mma_finished`) and the commit's arrival
(`tcNotify_finished`); the copies' writes and the MMA's operand reads precede these stages, and
every thread instruction precedes its thread's exit (`no_sharedLifetimeUnsafe`). -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier
noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}
variable (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre hX hW

/-- **Every mbarrier operand follows the initialization of its object**: thread 0's operations
by program order, and every other thread's polls of `bar1` by the history of `bar1`
(`table1`). -/
theorem no_mbarUninit : ¬ MbarUninit L X := by
  have h0 : hd 0 = 9 := rfl
  have get_init : ∀ k, (k = 2 ∨ k = 3) → k < m 0 →
      X.get (0, k) = some (if k = 2 then init0E L.sharedBase else init1E L.sharedBase) :=
    fun k hk hm => by
      have hl := hW.length 0 (by decide)
      obtain ⟨ev, he⟩ : ∃ ev, X.get (0, k) = some ev :=
        ⟨_, show (X.tr 0)[k]? = _ from List.getElem?_eq_getElem (by omega)⟩
      rw [he, init_get hW hk he]
  -- an operation of thread 0 after its initialization of `mb`
  have po_init : ∀ {k j pc kd}, (k = 2 ∨ k = 3) → k < j →
      X.get (0, j) = some ⟨pc, kd⟩ → (∀ f, kd ≠ .ub f) →
      ∃ i count, X.MbInit i (if k = 2 then bar0 L.sharedBase else bar1 L.sharedBase) count ∧
        InitPublished L X i (0, j) (if k = 2 then bar0 L.sharedBase else bar1 L.sharedBase) :=
    fun {k j pc kd} hk hkj hp hkd => by
      have hjm : j < m 0 := by
        obtain ⟨-, ⟨hjm, -⟩ | ⟨-, pc', f, hev, -⟩⟩ := hW.get hp
        · exact hjm
        · cases hev
          exact (hkd f rfl).elim
      have hi := get_init k hk (by omega)
      rcases hk with rfl | rfl <;> simp only [↓reduceIte, show (3 : Nat) ≠ 2 by decide] at hi ⊢ <;>
        exact ⟨(0, _), 1, ⟨_, hi⟩, .inl (po_baseCausality hkj (len_of_get hp) (by rw [hi]; rfl))⟩
  rintro ⟨⟨g, j⟩, mb, hu, hni, hnp⟩
  rcases hu with ⟨tx, count, rel, sc, pc, hp⟩ | ⟨s, ⟨pc, hp⟩, hm⟩ | ⟨noinc, pc, hp⟩ |
    ⟨s, rank, ⟨pc, hp⟩, htg⟩ | ⟨pc, q, ok, acq, sc, hp⟩ | ⟨pc, hp⟩ | ⟨_, _, ⟨pc, hi⟩, _⟩ |
    ⟨_, _, _, ⟨pc, hi⟩, _⟩ | ⟨c, hi⟩
  · obtain ⟨-, -, rfl, rfl, rfl, -⟩ := hW.arrive hp
    exact hnp (po_init (.inl rfl) (by decide) hp (fun _ h => by cases h))
  · obtain ⟨-, -, rfl, hc⟩ := hW.bulk hp
    rw [(hW.copy_spec ⟨pc, hp⟩).1] at hm
    obtain rfl := (AsyncCopy.Completion.mbarrier.inj hm).symm
    exact hnp (po_init (.inl rfl) (by rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide) hp
      (fun _ h => by cases h))
  · exact (hW.no_asyncArrive hp).elim
  · obtain ⟨-, -, rfl, rfl, rfl⟩ := hW.commit hp
    obtain ⟨-, rfl⟩ := commitSpec_target htg
    exact hnp (po_init (.inr rfl) (by omega) hp (fun _ h => by cases h))
  · obtain ⟨hg, -, rfl, hc⟩ := hW.wait hp
    rcases hc with ⟨rfl, hlo, -, rfl, -⟩ | ⟨hlo, -, rfl, -⟩
    · exact hnp (po_init (.inl rfl) (by omega) hp (fun _ h => by cases h))
    · have ha : objectAction X X.async (bar1 L.sharedBase) (.thread (g, j)) =
          some (.pollParity 0 ok) := by simp [objectAction, hp]
      obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 _).2.2 _ _ ha
      have htl := tl_ge (g := g) (P g)
      have hne : r.id ≠ .thread (0, 3) := by
        rw [hid]; intro h; cases h; omega
      have hb := (table1 hpre hX hW).init_hb r hr hne
      rw [hid] at hb
      have h3 := get_init 3 (.inr rfl)
        (lt_m_of_get hW (show X.get (0, 3) = _ from
          List.getElem?_eq_getElem (baseCausality_events hb).1) (by decide))
      exact hnp ⟨(0, 3), 1, ⟨_, h3⟩, .inl hb⟩
  · exact (hW.no_inval hp).elim
  · exact (hW.no_tensor ⟨pc, hi⟩).elim
  · exact (hW.no_clc ⟨pc, hi⟩).elim
  · exact (hni c hi).elim

omit hpre hX in
/-- **Every poll is a canonical spin** (`spins`). -/
theorem no_pollShapeUnsafe : ¬ PollShapeUnsafe kernel X := by
  rintro ⟨⟨g, j⟩, pc, m', q, ok, acq, sc, he, hs, -⟩
  exact hs (spins (hW.wait_pc he))

omit hpre hX in
/-- The linear copies are not reductions. -/
theorem no_copyReduce : ¬ TensorStore.CopyReduceNoRule [] X :=
  TensorStore.not_copyReduceNoRule_of_none fun _ _ hc r => by
    rw [(hW.copy_spec hc).2.1]; simp

theorem exit0_observations {j pc : Nat} (he : X.get (0, j) = some ⟨pc, .exit⟩) :
    (∃ ws, AsyncObserved X (0, 6) (.notify .copy) (0, hd 0 + 1 + (P 0).n0) true ws ∧
      AsyncObserved X (0, 7) (.notify .copy) (0, hd 0 + 1 + (P 0).n0) true ws) ∧
    ∃ ws, AsyncObserved X (0, hd 0 + 2 + (P 0).n0) .mmaDone (0, tl 0 (P 0) + (P 0).n1) true ws ∧
      X.get (0, tl 0 (P 0) + (P 0).n1) = some (wait1E L.sharedBase true) := by
  have hm := (trace_full hX hW he).2.1
  rw [fullE_length] at hm
  have htl := tl_zero (P 0)
  have hld := ldIdx_eq (g := 0) (P 0)
  have hw0 : X.get (0, hd 0 + 1 + (P 0).n0) = some (wait0E L.sharedBase true) := by
    rw [hW.get_of_lt (by decide) (by simp at hm; omega), fullAt_w0t]
  have hw1 : X.get (0, tl 0 (P 0) + (P 0).n1) = some (wait1E L.sharedBase true) := by
    rw [hW.get_of_lt (by decide) (by simp at hm; omega), fullAt_w1t]
  exact ⟨⟨.cta, wait_observes_copies hX hW hw0⟩, .cta, wait_observes_mma hpre hX hW hw1, hw1⟩

omit hX in
/-- The commit's CTA group is CTA 0's single-CTA cluster; its target `bar1` is initialized
before it (`no_mbarUninit`). -/
theorem no_commit_unsafe : ¬ TcCommitUnsafe L X := by
  have ht := threads_eq hpre
  rintro ⟨⟨g, j⟩, s, ⟨pc, hc⟩, hn⟩
  · obtain ⟨_, hj, rfl, rfl, rfl⟩ := hW.commit hc
    have hone := Launch.oneDimLaunch_clusterGridValid hpre.oneDimLaunch
    have hcs := clusterSize_eq hpre
    have hr := Launch.oneDim_rankOfCta hpre.oneDimLaunch.1 0
    have hsz := Launch.oneDim_clusterSizeOf hpre.oneDimLaunch.1 0
    have hco := Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1 0
    refine hn ⟨by omega, ?_, ?_⟩
    · simp [TcCommit.resolve, commitSpec, TcCommit.unicast, bar1, Launch.clusterStart, hcs,
        hsz, hco, hpre.grid, hone, hpre.block]
    · simp [commitSpec, TcCommit.unicast, Launch.ctaGroup_one, Launch.peerCta, Launch.clusterStart,
        hcs, hr, hsz, hco, hpre.grid, hpre.block]

/-- Once CTA 0 has exited, thread 0's last event is its exit, after both its successful
polls. -/
theorem exit0_of_exited (hx : CtaExited L X 0) :
    ∃ pc, X.get (0, (X.tr 0).length - 1) = some ⟨pc, .exit⟩ ∧
      tl 0 (P 0) + (P 0).n1 < (X.tr 0).length - 1 ∧ (X.tr 0).length = m 0 := by
  have hT := threads_eq hpre
  obtain ⟨pc, hlast⟩ := hx 0 (by rw [hT]; decide) (Nat.zero_div _)
  rw [List.getLast?_eq_getElem?] at hlast
  have he : X.get (0, (X.tr 0).length - 1) = some ⟨pc, .exit⟩ := hlast
  obtain ⟨-, hfull, htr⟩ := trace_full hX hW he
  have hld := ldIdx_eq (g := 0) (P 0)
  rw [fullE_length] at hfull
  simp only [show (0 : Nat) / 32 = 0 from rfl, ↓reduceIte] at hfull
  have hxlen : (X.tr 0).length = m 0 := by
    rw [htr, fullE_length]; simp only [show (0 : Nat) / 32 = 0 from rfl, ↓reduceIte]; omega
  exact ⟨pc, he, by omega, hxlen⟩

/-- Once CTA 0 has exited, each copy's notification completed before thread 0's exit: its
release complete-tx is observed by thread 0's successful acquire poll of `bar0`. -/
theorem copy_finished {copy : EvId} (hc : copy = (0, 6) ∨ copy = (0, 7))
    (hx : CtaExited L X 0) : SharedFinished L kernel [] X (.async copy (.notify .copy)) 0 := by
  have hT := threads_eq hpre
  obtain ⟨pc, he, hlt, hxlen⟩ := exit0_of_exited hpre hX hW hx
  have htl := tl_zero (P 0)
  have hw0 : X.get (0, hd 0 + 1 + (P 0).n0) = some (wait0E L.sharedBase true) := by
    rw [hW.get_of_lt (by decide) (by omega), fullAt_w0t]
  obtain ⟨hA, hB⟩ := wait_observes_copies hX hW hw0
  have ho : AsyncObserved X copy (.notify .copy) (0, hd 0 + 1 + (P 0).n0) true .cta := by
    rcases hc with rfl | rfl
    · exact hA
    · exact hB
  obtain ⟨-, -, ⟨-, -, hn, -⟩, -⟩ := ho.copy
  refine ⟨hn, (0, (X.tr 0).length - 1), pc, by omega, Nat.zero_div _, he,
    CompletedBefore.of_copyRelease (.inl rfl) ho ?_
      ⟨rfl, by simp only; omega, by simp only; omega, ?_⟩⟩
  · rcases hc with rfl | rfl <;> simp [ScopesMeet, MbarScopeIncludes, SameCluster, SameCta, hT]
  · rintro ⟨hs, -⟩
    simp [he, Event.acc] at hs

/-- Once CTA 0 has exited, the MMA completed before thread 0's exit: thread 0's successful poll
of `bar1` observes it through the commit and guards the exit. -/
theorem mma_finished (hx : CtaExited L X 0) :
    SharedFinished L kernel [] X (.async (0, hd 0 + 2 + (P 0).n0) .mmaDone) 0 := by
  have hT := threads_eq hpre
  obtain ⟨pc, he, hlt, hxlen⟩ := exit0_of_exited hpre hX hW hx
  have htl := tl_zero (P 0)
  have hwget : X.get (0, tl 0 (P 0) + (P 0).n1) = some (wait1E L.sharedBase true) := by
    rw [hW.get_of_lt (by decide) (by omega), fullAt_w1t]
  have ho := wait_observes_mma hpre hX hW hwget
  have hguard : DepStep L kernel X (.thread (0, tl 0 (P 0) + (P 0).n1), true)
      (.thread (0, (X.tr 0).length - 1), false) :=
    GuardSource.guard (.inl ⟨Flow.mbarWait_1, _, 0, true, .cta, hwget, spins (.inr rfl)⟩)
      ⟨rfl, hlt, by simp only; omega⟩
  obtain ⟨hdone, hcb⟩ := CompletedBefore.of_observesMma hX.tcCommit ho (.single hguard)
  exact ⟨hdone, (0, (X.tr 0).length - 1), pc, by omega, Nat.zero_div _, he, hcb⟩

/-- Once CTA 0 has exited, the commit's arrival on `bar1` completed before thread 0's exit:
it precedes the successful poll of `bar1` in that object's history, and the poll guards the
exit. -/
theorem tcNotify_finished (hx : CtaExited L X 0) :
    SharedFinished L kernel [] X (.async (0, hd 0 + 3 + (P 0).n0) (.tcNotify 0)) 0 := by
  have ht := threads_eq hpre
  obtain ⟨pcx, hx', hlt, hxlen⟩ := exit0_of_exited hpre hX hW hx
  obtain ⟨wsx, hobx, -⟩ := (exit0_observations hpre hX hW hx').2
  obtain ⟨c, s', r', m', _, ⟨pc', hc'⟩, htg', hmem, hwox⟩ := hobx.mma
  have hphase := hwox.2
  obtain ⟨cg, cj⟩ := c
  obtain ⟨_, _, rfl, rfl, rfl⟩ := hW.commit hc'
  obtain ⟨rfl, rfl⟩ := commitSpec_target htg'
  refine ⟨hmem, (0, (X.tr 0).length - 1), pcx, by omega, Nat.zero_div _, hx', ?_⟩
  obtain ⟨a, z, r, t, phase, hra, hr, _, htz, htw, _, _, haz, _⟩ := hphase
  have htl := tl_zero (P 0)
  have hwget : X.get (0, tl 0 (P 0) + (P 0).n1) =
      some ⟨Flow.mbarWait_1, .wait (bar1 L.sharedBase) 0 true true .cta⟩ := by
    rw [hW.get_of_lt (by decide) (by omega), fullAt_w1t]; rfl
  exact CompletedBefore.of_before ⟨a, z, r, t, hra, hr, htz, htw, haz⟩
    (.single (GuardSource.guard (.inl ⟨Flow.mbarWait_1, _, 0, true, .cta, hwget,
      spins (.inr rfl)⟩) ⟨rfl, hlt, by simp only; omega⟩))

/-- **Every shared-memory use completes in time**: every use is in CTA 0, its issuer's CTA, and
once CTA 0 has exited, a thread instruction finished before its thread's exit, and the copies'
writes and notifications, the MMA's operand reads and completion and the commit's arrival
before thread 0's exit. -/
theorem no_sharedLifetimeUnsafe : ¬ SharedLifetimeUnsafe L kernel [] X := by
  have hT := threads_eq hpre
  have bad : ∀ {v pc k}, X.get v = some ⟨pc, k⟩ → k.isTcBulk = false → False :=
    fun he hk => by rw [hW.tcBulk _ _ _ he] at hk; cases hk
  rintro ⟨e, owner, hu, hbad⟩
  suffices h : owner = e.issuer.1 / L.block ∧
      (CtaExited L X owner → SharedFinished L kernel [] X e owner) by
    rcases hbad with ⟨hne, -⟩ | ⟨hx, hfin⟩
    · exact hne h.1
    · exact hfin (h.2 hx)
  rcases hu with ⟨hp, ⟨acc, w, ha, hs, hcta⟩ | ⟨addr, action, ha⟩⟩ |
    ⟨⟨g, j⟩, s, rfl, ⟨pc, hi⟩, hgrp⟩ |
    ⟨i, address, s, x, y, k, -, ⟨pc, hi⟩, -⟩ | ⟨i, address, s, -, ⟨pc, hi⟩, -⟩ |
    ⟨⟨g, j⟩, p, rfl, hfs, hst⟩
  · have hown : owner = e.issuer.1 / L.block := hcta.symm.trans (intent_local hpre hX hW ha hs)
    have hi0 : e.issuer.1 / L.block = 0 := cta_zero hpre (intent_index hpre hX hW ha).1
    refine ⟨hown, fun hx => ?_⟩
    cases e with
    | thread i => exact SharedFinished.of_access hX.outside ha hown.symm hx
    | async i p =>
      rw [hi0] at hown
      subst hown
      cases w with
      | true =>
        rcases hW.write_intent ha with ⟨h, -⟩ | ⟨g, hg, k, hk, h, -⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;>
          cases h
        · have hf := copy_finished hpre hX hW (.inl rfl) hx
          exact SharedFinished.of_stage (j := (0, 6)) (q := .notify .copy) hp
            (.inr ⟨rfl, rfl, rfl, rfl, hp, hf.1⟩) hf
        · have hf := copy_finished hpre hX hW (.inr rfl) hx
          exact SharedFinished.of_stage (j := (0, 7)) (q := .notify .copy) hp
            (.inr ⟨rfl, rfl, rfl, rfl, hp, hf.1⟩) hf
      | false =>
        rcases hW.read_intent ha with ⟨g, hg, h, -⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ |
          ⟨k, hk, q, hq, h, -⟩ | ⟨k, hk, q, hq, h, -⟩ <;> cases h
        · simp [gA] at hs
        · simp [gB] at hs
        · have hf := mma_finished hpre hX hW hx
          exact SharedFinished.of_stage (j := (0, hd 0 + 2 + (P 0).n0)) (q := .mmaDone) hp
            (.inr ⟨rfl, rfl, rfl, hp, hf.1⟩) hf
        · have hf := mma_finished hpre hX hW hx
          exact SharedFinished.of_stage (j := (0, hd 0 + 2 + (P 0).n0)) (q := .mmaDone) hp
            (.inr ⟨rfl, rfl, rfl, hp, hf.1⟩) hf
  · have hown : owner = e.issuer.1 / L.block := object_local hpre hX hW ha
    refine ⟨hown, fun hx => ?_⟩
    cases e with
    | thread i =>
      obtain ⟨ev, he, hne⟩ := objectAction_thread ha
      exact SharedFinished.of_thread hX.outside he hne hown.symm hx
    | async i p =>
      rcases object_action_cases hW ha with ⟨-, h⟩ | ⟨-, h⟩
      · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨j, ok, hj, hj', h, -⟩ <;> cases h
        · rw [Ref.issuer, Nat.zero_div] at hown
          subst hown
          exact copy_finished hpre hX hW (.inl rfl) hx
        · rw [Ref.issuer, Nat.zero_div] at hown
          subst hown
          exact copy_finished hpre hX hW (.inr rfl) hx
      · rcases h with ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨g, hg, j, ok, hj, hj', h, -⟩ <;> cases h
        rw [Ref.issuer, Nat.zero_div] at hown
        subst hown
        exact tcNotify_finished hpre hX hW hx
  · obtain ⟨hg, -, rfl, -, -⟩ := hW.commit hi
    have hown : owner = 0 := by
      have h := hgrp.1.2.1
      rw [hpre.grid] at h
      omega
    have hi0 : (0 : Nat) / L.block = 0 := Nat.zero_div _
    subst hown
    obtain ⟨ev, he⟩ : ∃ ev, X.get (0, j) = some ev := ⟨_, hi⟩
    exact ⟨hi0.symm, fun hx => SharedFinished.of_thread hX.outside he (fun _ h => by
      rw [he] at hi; rw [h] at hi; cases hi) hi0 hx⟩
  · exact (bad hi rfl).elim
  · exact (bad hi rfl).elim
  · rcases hfs with ⟨s, mb, ⟨pc, hi⟩, -, rfl⟩ | ⟨s, hc, hm, rfl⟩ | ⟨mb, noinc, ⟨pc, hi⟩, rfl⟩ |
      ⟨hta, rfl⟩ | ⟨s, targets, c, ⟨pc, hi⟩, -, rfl⟩ | ⟨a', s, ⟨pc, hi⟩, rfl⟩ |
      ⟨a', s, ⟨pc, hi⟩, rfl⟩ | ⟨s, rank, mb, ⟨pc, hi⟩, htg, rfl⟩
    · obtain ⟨-, -, rfl, hcase⟩ := hW.bulk hi
      obtain ⟨s', mb', hc', hm', hor⟩ := hst
      obtain ⟨-, -, -, hcase'⟩ := hW.bulk hc'.choose_spec
      rw [(hW.copy_spec hc').1] at hm'
      obtain rfl := (AsyncCopy.Completion.mbarrier.inj hm').symm
      have hown : owner = 0 := by
        rcases hor with ⟨-, h⟩ | ⟨h, -⟩ | h <;>
          rcases hcase' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
          simp [specA, specB, bulkSpec, sA, sB, gA, gB, bar0] at h <;> omega
      subst hown
      refine ⟨(Nat.zero_div _).symm, fun hx => ?_⟩
      rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact copy_finished hpre hX hW (.inl rfl) hx
      · exact copy_finished hpre hX hW (.inr rfl) hx
    · exact (hm _ (hW.copy_spec hc).1).elim
    · exact (hW.no_asyncArrive hi).elim
    · rcases hst with ⟨d, s, accum, mask, hi, hlow⟩ | ⟨cp, ⟨pc, hcp⟩, -⟩
      · obtain ⟨hgj, -, rfl, -, -⟩ := hW.mmaIssue hi
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hgj
        have hown : owner = 0 := by rcases hlow with rfl | rfl <;> rfl
        subst hown
        exact ⟨(Nat.zero_div _).symm, mma_finished hpre hX hW⟩
      · exact (hW.no_cp hcp).elim
    · exact (bad hi rfl).elim
    · exact (bad hi rfl).elim
    · exact (bad hi rfl).elim
    · obtain ⟨-, -, rfl, rfl, rfl⟩ := hW.commit hi
      obtain ⟨rfl, rfl⟩ := commitSpec_target htg
      obtain ⟨s', mb', ⟨pc', hc'⟩, htg', hcta⟩ := hst
      obtain ⟨-, -, -, -, rfl⟩ := hW.commit hc'
      obtain ⟨-, rfl⟩ := commitSpec_target htg'
      subst hcta
      exact ⟨by simp [bar1, Ref.issuer], tcNotify_finished hpre hX hW⟩

theorem no_tma_unsafe : ¬ TmaUnsafe L mem0 X := by
  rintro (⟨mb, r, hr, hf⟩ | ⟨mb, r, hr, hn⟩ | ⟨e, acc, w, i, mb, count, l, he, hi, ha, hm, -⟩ | h |
    h)
  · rw [object_fault_free hpre hX hW hr] at hf
    cases hf
  · exact hn (object_published hpre hX hW hr)
  · exact intent_mbar_disjoint hW he ha (hW.uses_mbar (.of_init hi)) hm
  · exact not_cpAsyncOverlap_of_none (fun i s hc => by rw [(hW.copy_spec hc).1]; simp) h
  · exact not_maskedRangeUnalloc_of_none (fun i s m hc => by rw [(hW.copy_spec hc).2.1]; simp) h

end
end PTX.Kernels.TcGemm.Proof
