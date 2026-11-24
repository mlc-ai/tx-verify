-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.MemoryAccess
public import Kernels.Fp16Gemm8192.Proof.Safety.TmaSource
public import Kernels.Fp16Gemm8192.Proof.Safety.TcCommit
public import Kernels.Fp16Gemm8192.Proof.Safety.TensorStore

@[expose] public section

/-! # Shared memory lifetimes, from the interface

Every use of a CTA's shared memory (`SharedUse`) is safe (`no_sharedLifetimeUnsafe`). A use of
another CTA's shared memory is one of: an arrival on a barrier of the cluster's leader CTA, a
tensor load's or a commit's or a cancellation request's completion on a barrier of a CTA of the
cluster, a commit issued for its CTA pair, an MMA's read of the peer CTA's input stage and its
completion, a cancellation response written to a target CTA. Every other use is in the issuer's own
CTA: a thread's reads and writes (`ThreadFacts.access_region`, `cons_out`), a poll, an
initialization, a tensor store's reads and their completion, a tensor load's writes.

* **Started.** The issuer is a role event, and the owner's CTA thread 0 initialized the barriers of
  the ring before it (`ThreadFacts.ring_initialized`): an event of the owner waits before it
  (`started_of_published`).
* **Finished.** A thread instruction of the owner CTA comes before that thread's exit
  (`SharedFinished.of_thread`); an arrival or a commit comes before its thread's exit arrival
  (`ThreadFacts.arrive_phase`), so before the exits of its cluster (`ExitOrder`); a completion of a
  tensor load (each data write and its notification), a commit or a request finished before an exit
  of the CTA it notifies (`TensorExitFinished`, `CommitNotified`, `ExitNotified`), and a response
  write before its notification; an MMA's completion and its operand reads by the input ring's
  `MmaExitDone` and `ReadsFinished`; a tensor store's read completion before its issuer's final
  drain (`store_reads_finished`), and its reads before their completion. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety.Memory

open PTX AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An event of a role, in a CTA of its cluster: an event of that CTA waits before it. -/
theorem started_of_role (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (hpre : Pre P L mem0) {g j : Nat} {ev : Event} {ρ : Prologue.Role} {cta : Nat}
    (hg : g < L.threads) (he : X.get (g, j) = some ev)
    (hσ : Frame.stateAt (code L) X g j = some (some (.inr ρ))) (hcta : cta < L.grid)
    (hcl : L.clusterOfCta cta = L.clusterOfCta (g / L.block)) :
    ∃ start ev', start.1 < L.threads ∧ start.1 / L.block = cta ∧ X.get start = some ev' ∧
      LifetimeOrder L kernel Prod X (.thread start, true) (.thread (g, j), false) := by
  obtain ⟨pci, hinit, hpub⟩ := ht.ring_initialized (b := ⟨.clc, 0, true⟩) hg he hσ Nat.one_pos
    hcta hcl
  obtain ⟨start, sev, hsc, hse, hsw⟩ := started_of_published ⟨_, hinit⟩ hpub
  have hb : cta * L.block / L.block = cta := Nat.mul_div_cancel _ (by rw [hpre.block]; decide)
  exact ⟨start, sev, Frame.lt_of_get hX hse, by rw [hsc, hb], hse, hsw⟩

/-- A classified object's CTA started before its user. -/
theorem started_of_classified (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g j : Nat} {m : Loc} (hc : Classified L X g j m) :
    ∃ start ev', start.1 < L.threads ∧ start.1 / L.block = m.cta ∧ X.get start = some ev' ∧
      LifetimeOrder L kernel Prod X (.thread start, true) (.thread (g, j), false) := by
  obtain ⟨ρ, b, cta, hg, ⟨ev, he⟩, hσ, -, hcta, hcl, rfl, -⟩ := hc
  exact started_of_role hX ht hpre hg he hσ hcta hcl

/-- An exited CTA's thread 0 has its exit as its last event. -/
theorem exit_of_exited (hpre : Pre P L mem0) {cta : Nat} (hcta : cta < L.grid)
    (hex : CtaExited L X cta) :
    ∃ pc, cta * L.block < L.threads ∧ X.get (cta * L.block, (X.tr (cta * L.block)).length - 1) =
      some ⟨pc, .exit⟩ := by
  have hblock := hpre.block
  have hb : cta * L.block / L.block = cta := Nat.mul_div_cancel _ (by rw [hblock]; decide)
  have hgp : cta * L.block < L.threads := by
    simp only [Launch.threads]
    rw [hblock] at hb ⊢
    nlinarith
  obtain ⟨pc, hlast⟩ := hex _ hgp hb
  rw [List.getLast?_eq_getElem?] at hlast
  exact ⟨pc, hgp, hlast⟩

/-- A tensor load writes its loader's CTA. -/
theorem tensor_base_cta (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {i : EvId}
    {address : Nat} {s : TensorCopy.Spec} (hi : X.TensorIssue i address s) :
    s.sharedBase.cta = i.1 / L.block := by
  obtain ⟨pc, hel⟩ := hi
  have hg := Frame.lt_of_get hX hel
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hel (by simp)
  obtain ⟨l, b, j, -, -, -, ⟨base, cls, origin, hsp, -⟩, -⟩ := ht.tensor_issue hg hel hσ rfl
  rw [hsp]
  rfl

/-- A tensor store reads its issuer's CTA. -/
theorem store_base_cta (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {i : EvId}
    {address : Nat} {s : TensorStore.Spec} (hi : X.TensorStoreIssue i address s) :
    s.sharedBase.cta = i.1 / L.block := by
  obtain ⟨pc, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  exact (ht.store_box hg he hσ rfl).1

/-- **An arrival on a barrier is safe.** -/
theorem arrive_safe (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hex : ExitOrder L X) {g j pc tx c : Nat} {m : Loc} {rel : Bool}
    {sc : MbarScope} (he : X.get (g, j) = some ⟨pc, .arrive m tx c rel sc⟩) :
    PeerSharedStarted L kernel Prod X (.thread (g, j)) m.cta ∧
      (CtaExited L X m.cta → SharedFinished L kernel Prod X (.thread (g, j)) m.cta) := by
  have hcls := arrive_classified hpre hX ht he
  refine ⟨started_of_classified hpre hX ht hcls, fun hexit => ?_⟩
  obtain ⟨ρ, b, cta, hg, -, hσ, -, hcta, hcl, rfl, -⟩ := hcls
  have hb : cta * L.block / L.block = cta := Nat.mul_div_cancel _ (by rw [hpre.block]; decide)
  obtain ⟨fpc, hgp, hlast⟩ := exit_of_exited hpre hcta hexit
  have hph := ht.arrive_phase hg he hσ rfl
  have hhb := hex (g, j) _ _ _ fpc he hσ hph (fun rel al h => by cases h) hlast
    ⟨hg, hgp, by rw [hb]; exact hcl.symm⟩
  exact ⟨⟨_, he⟩, _, fpc, hgp, by rw [hb]; rfl, hlast, CompletedBefore.of_baseCausality hhb⟩

/-- A response written to a CTA finished before an exit of that CTA, once it has exited: its
notification did (`ExitNotified`), and follows the write. -/
theorem clc_write_finished (hcl : ClcOk L X) (hen : ExitNotified L X) {i : EvId} {s : Clc.Spec}
    {tg : List Nat} {c : Nat} (hi : X.ClcIssue i s tg) (hc : c ∈ tg) (hexit : CtaExited L X c) :
    SharedFinished L kernel Prod X (.async i (.write (.cta c))) c := by
  have hf := hen i s tg c hi hc hexit
  have hn : X.AsyncPresent i (.notify (.cta c)) := hf.1
  have hwp : X.AsyncPresent i (.write (.cta c)) := (hcl.2.2.2.1 i s tg hi).1.notified c hn
  exact SharedFinished.of_stage (j := i) (q := .notify (.cta c)) hwp
    (.inr ⟨rfl, rfl, rfl, rfl, hwp, hn⟩) hf

/-- An MMA's operand CTAs started before it. -/
theorem mma_started (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {i : EvId} {d : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hi : X.MmaIssue i d s acc mask) {owner : Nat}
    (ho : owner = s.lowCta ∨ owner = s.highCta) :
    PeerSharedStarted L kernel Prod X (.async i .mmaDone) owner := by
  obtain ⟨pc, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  obtain ⟨m, sl, j, rfl, -, hlead, hsp, -⟩ := ht.mma_issue hg he hσ rfl
  rw [hsp] at ho
  simp only [InputRing.mmaSpec] at ho
  have hgc : i.1 / L.block < L.grid := by
    simp only [Launch.threads] at hg
    exact (Nat.div_lt_iff_lt_mul (by rw [hpre.block]; decide)).mpr hg
  have hgrid := hpre.grid
  obtain ⟨start, ev, h1, h2, h3, h4⟩ := started_of_role hX ht hpre hg he hσ (cta := owner)
    (by rcases ho with rfl | rfl <;> omega)
    (by simp only [clusterOfCta_eq hpre]; rcases ho with rfl | rfl <;> omega)
  exact ⟨start, ev, h1, h2, h3, h4⟩

/-- **No shared memory use is unsafe.** -/
theorem no_sharedLifetimeUnsafe (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hex : ExitOrder L X) (hen : ExitNotified L X)
    (hcn : CommitNotified L X) (htf : TensorExitFinished L X) (hmx : MmaExitDone L X)
    (hrf : ReadsFinished L X) : ¬ SharedLifetimeUnsafe L kernel Prod X := by
  rintro ⟨e, owner, huse, hbad⟩
  suffices h : (owner ≠ e.issuer.1 / L.block → PeerSharedStarted L kernel Prod X e owner) ∧
      (CtaExited L X owner → SharedFinished L kernel Prod X e owner) by
    rcases hbad with ⟨h1, h2⟩ | ⟨h3, h4⟩
    · exact h2 (h.1 h1)
    · exact h4 (h.2 h3)
  have hblock := hpre.block
  -- the uses at a tensor load's, a commit's and a request's completion
  have tensor_case : ∀ {i : EvId} {address : Nat} {s : TensorCopy.Spec}, X.TensorIssue i address s →
      s.mbar.cta = owner → PeerSharedStarted L kernel Prod X (.async i (.notify .load)) owner ∧
        (CtaExited L X owner → SharedFinished L kernel Prod X (.async i (.notify .load)) owner) :=
          by
    intro i address s hi hcta
    subst hcta
    exact ⟨started_of_classified hpre hX ht (tensor_classified hpre hX ht hi),
      fun hexit => htf.2 i address s hi hexit⟩
  have commit_case : ∀ {i : EvId} {s : TcCommit.Spec} {rank : Fin 16} {m : Loc}, X.Commit i s →
      TcCommit.target s rank = some m → m.cta = owner →
      PeerSharedStarted L kernel Prod X (.async i (.tcNotify rank)) owner ∧
        (CtaExited L X owner → SharedFinished L kernel Prod X (.async i (.tcNotify rank)) owner) :=
          by
    intro i s rank m hc htg hcta
    subst hcta
    obtain ⟨pc, he⟩ := hc
    exact ⟨started_of_classified hpre hX ht (commit_classified hpre hX ht he htg),
      fun hexit => hcn i s rank m ⟨pc, he⟩ htg hexit⟩
  have clc_case : ∀ {i : EvId} {s : Clc.Spec} {tg : List Nat} {c : Nat}, X.ClcIssue i s tg →
      c ∈ tg → c = owner → PeerSharedStarted L kernel Prod X (.async i (.notify (.cta c))) owner ∧
        (CtaExited L X owner →
          SharedFinished L kernel Prod X (.async i (.notify (.cta c))) owner) := by
    intro i s tg c hi hc hcta
    subst hcta
    exact ⟨started_of_classified hpre hX ht (clc_classified hpre hX ht hi hc),
      fun hexit => hen i s tg c hi hc hexit⟩
  rcases huse with ⟨hpres, ⟨a, w, hint, hsp, hcta⟩ | ⟨addr, act, hact⟩⟩ |
      ⟨i, s, rfl, hc, hgrp⟩ | ⟨i, address, s, x, y, k, rfl, hi, hsl, hcta⟩ |
      ⟨i, address, s, rfl, hi, hcta⟩ | ⟨i, p, rfl, hfin, hsu⟩
  · -- an access of the owner's shared memory
    rcases e with ⟨g, k⟩ | ⟨i, p⟩
    · -- a thread's access, in its own CTA
      have hacc : X.Access (g, k) a w := hint
      have hown : owner = g / L.block := by
        rcases hint with ⟨bs, ⟨pc, hget⟩, rfl⟩ | ⟨bs, ⟨pc, hget⟩, rfl⟩ | ⟨o, n, pc, hget⟩
        rotate_left 2
        · exact (no_rmw hX ht hget).elim
        · obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
          rcases (ht.access_region (Frame.lt_of_get hX hget) hget hσ).1 a bs rfl with
            ⟨hl, -⟩ | ⟨hl, -⟩ <;> rw [hl] at hcta <;> exact hcta.symm
        · obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
          rcases (ht.access_region (Frame.lt_of_get hX hget) hget hσ).2.1 a bs rfl with
            ⟨c, rfl⟩ | ⟨hl, -⟩
          · obtain ⟨-, hst, -⟩ := ht.cons_out (Frame.lt_of_get hX hget) hget hσ
            obtain ⟨s0, i0, el0, -, hl, -⟩ := hst a bs rfl
            rw [hl] at hcta
            exact hcta.symm
          · rw [hl] at hcta
            exact hcta.symm
      exact ⟨fun h => absurd hown h,
        fun hx => SharedFinished.of_access hX.outside hacc hown.symm hx⟩
    · cases p with
      | mmaRead isB idx =>
        obtain ⟨-, -, hfp⟩ := hint
        rcases id hfp with ⟨dst, sp, acc, mask, ⟨pc, hget⟩, hbl⟩ | ⟨a', src, cta, ⟨pc, hget⟩, -, -⟩
        · have hg := Frame.lt_of_get hX hget
          obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
          obtain ⟨m, s0, j, rfl, -, hlead, hsp', -⟩ := ht.mma_issue hg hget hσ rfl
          have hc := TcMma.OperandSpec.byteLoc_cta hbl
          rw [hsp'] at hc
          simp only [InputRing.mmaSpec] at hc
          have hgc := cta_lt_grid hpre hg
          have hgrid := hpre.grid
          refine ⟨fun _ => ?_, fun hexit => ?_⟩
          · obtain ⟨start, ev', hs1, hs2, hs3, hs4⟩ := started_of_role hX ht hpre hg hget hσ
              (cta := owner) (by omega) (by simp only [clusterOfCta_eq hpre]; omega)
            exact ⟨start, ev', hs1, hs2, hs3, hs4⟩
          · rw [← hcta] at hexit ⊢
            exact hrf i isB idx a.loc hfp hexit
        · exfalso
          have hg := Frame.lt_of_get hX hget
          obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
          exact ht.no_tc_cp hg hget hσ rfl
      | readStore x y z =>
        -- a tensor store's read of its own CTA, before the reads' completion
        obtain ⟨-, sp, addr, ⟨pc, hget⟩, hl, -⟩ := hint
        have hg := Frame.lt_of_get hX hget
        obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
        obtain ⟨c, rfl⟩ := (ht.access_region hg hget hσ).2.2 addr sp rfl
        obtain ⟨-, -, hr, -⟩ := ht.cons_out hg hget hσ
        obtain ⟨s0, hs0, hrd, -⟩ := hr addr sp rfl
        have hown : owner = i.1 / L.block := by
          rw [← hcta]
          exact (hrd x y z a.loc hl).2.1
        refine ⟨fun h => absurd hown h, fun hexit => ?_⟩
        have hb := store_base_cta hX ht ⟨pc, hget⟩
        have hf := store_reads_finished hX ht ⟨pc, hget⟩ (by rw [hb, ← hown]; exact hexit)
        rw [hb, ← hown] at hf
        exact SharedFinished.of_stage (j := i) (q := .readsDone) hpres
          (.inr ⟨rfl, rfl, rfl, hpres, hf.1⟩) hf
      | writeStore x y z =>
        exfalso
        obtain ⟨-, sp, addr, -, hl, -⟩ := hint
        rw [Execution.store_writeLoc_global hl] at hsp
        cases hsp
      | oldStore x y z =>
        exfalso
        obtain ⟨-, sp, addr, -, -, hl, -⟩ := hint
        rw [Execution.store_writeLoc_global hl] at hsp
        cases hsp
      | readLoad x y z =>
        exfalso
        obtain ⟨-, sp, addr, -, hl, -⟩ := hint
        rw [Execution.tensor_readLoc_global hl] at hsp
        cases hsp
      | readPrefetch x y z =>
        exfalso
        obtain ⟨-, sp, addr, -, hl, -⟩ := hint
        rw [TensorTransfer.sourceLoc_global hl] at hsp
        cases hsp
      | writeLoad x y z =>
        -- a tensor load's write of its loader's CTA
        obtain ⟨-, sp, addr, hti, hl, -⟩ := hint
        have hb := tensor_base_cta hX ht hti
        simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at hl
        obtain ⟨slot, hslot, hl⟩ := hl
        have hloc : (sp.sharedLoc slot).cta = sp.sharedBase.cta := rfl
        have hown : owner = i.1 / L.block := by rw [← hcta, ← hl, hloc, hb]
        have hsl : (TensorTransfer.slotAt sp.descriptor x y z).isSome := by simp [hslot]
        refine ⟨fun h => absurd hown h, fun hexit => ?_⟩
        rw [hown, ← hb] at hexit ⊢
        exact htf.1 i addr sp hti hexit x y z hsl
      | writeCta c =>
        obtain ⟨-, s, tg, hi, hc, rfl⟩ := hint
        simp only at hcta
        subst hcta
        exact ⟨fun _ => started_of_classified hpre hX ht (clc_classified hpre hX ht hi hc),
          fun hexit => clc_write_finished hX.clc hen hi hc hexit⟩
      | readCopy =>
        exfalso
        obtain ⟨-, ⟨s, hc, -⟩ | hp⟩ := hint
        · exact no_copy hX ht hc
        · exact no_bulkPrefetch hX ht hp
      | writeCopy =>
        exfalso
        obtain ⟨-, s, hc, -⟩ := hint
        exact no_copy hX ht hc
      | writeElem j =>
        exfalso
        obtain ⟨-, s, hc, -⟩ := hint
        exact no_copy hX ht hc
      | oldElem j =>
        exfalso
        obtain ⟨-, s, r, hc, -⟩ := hint
        exact no_copy hX ht hc
      | _ => exact hint.2.elim
  · -- an action on the owner's barrier
    rcases e with ⟨g, k⟩ | ⟨i, p⟩
    · simp only [objectAction] at hact
      split at hact
      · rename_i pc m' count hget
        split_ifs at hact with hm
        subst hm
        have hg := Frame.lt_of_get hX hget
        obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
        have hown : owner = g / L.block := ((ht.ring_event hg hget hσ).init_site _ _ rfl).2.1
        exact ⟨fun h => absurd hown h, fun hx =>
          SharedFinished.of_thread hX.outside hget (fun _ h => by cases h) hown.symm hx⟩
      · rename_i pc m' hget
        exact (no_inval hX ht ⟨pc, hget⟩).elim
      · rename_i pc m' tx count rel sc hget
        split_ifs at hact with hm
        subst hm
        have h := arrive_safe hpre hX ht hex hget
        exact ⟨fun _ => h.1, h.2⟩
      · rename_i pc m' par ok acq sc hget
        split_ifs at hact with hm
        subst hm
        have hg := Frame.lt_of_get hX hget
        obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
        have hown : owner = g / L.block := (ht.wait_local hg hget hσ rfl).2
        exact ⟨fun h => absurd hown h, fun hx =>
          SharedFinished.of_thread hX.outside hget (fun _ h => by cases h) hown.symm hx⟩
      · rename_i pc m' hget
        exact (no_asyncArrive hX ht ⟨pc, hget⟩).elim
      · cases hact
    · cases p with
      | notifyLoad =>
        simp only [objectAction] at hact
        split at hact
        · rename_i pc a' s0 hget
          cases ho : X.tensor i with
          | none => simp [ho] at hact
          | some o =>
            simp only [ho, bind, Option.bind] at hact
            split_ifs at hact with hc
            have h := tensor_case ⟨pc, hget⟩ (by rw [hc.1])
            exact ⟨fun _ => h.1, h.2⟩
        · cases hact
      | notifyCopy =>
        exfalso
        simp only [objectAction, issuedBy] at hact
        split at hact
        · rename_i pc s0 hget
          exact no_copy hX ht ⟨_, hget⟩
        · simp at hact
      | tcNotify rank =>
        simp only [objectAction] at hact
        split at hact
        · rename_i pc s0 hget
          split_ifs at hact with hc
          have h := commit_case ⟨pc, hget⟩ hc.1 rfl
          exact ⟨fun _ => h.1, h.2⟩
        · cases hact
      | notifyCta c =>
        simp only [objectAction] at hact
        split at hact
        · rename_i pc s0 tg hget
          split_ifs at hact with hc
          obtain ⟨hct, -, hm⟩ := hc
          have h := clc_case ⟨pc, hget⟩ hct (congrArg Loc.cta hm).symm
          exact ⟨fun _ => h.1, h.2⟩
        · cases hact
      | arriveOn =>
        exfalso
        simp only [objectAction] at hact
        split at hact
        · rename_i pc m' noinc hget
          exact no_asyncArrive hX ht ⟨pc, hget⟩
        · cases hact
      | _ => simp [objectAction] at hact
  · -- a commit's use of its CTA pair
    have h := commit_group_lifetime hpre hX ht hex hc hgrp
    exact ⟨fun _ => h.1, h.2⟩
  · -- a tensor load's write of its loader's CTA
    refine ⟨fun h => absurd (hcta.symm.trans (tensor_base_cta hX ht hi)) h, fun hexit => ?_⟩
    subst hcta
    exact htf.1 i address s hi hexit x y k hsl
  · -- a tensor store's read completion, in its issuer's CTA
    refine ⟨fun h => absurd (hcta.symm.trans (store_base_cta hX ht hi)) h, fun hexit => ?_⟩
    subst hcta
    exact store_reads_finished hX ht hi hexit
  · -- the stage that completes an operation
    rcases hfin with ⟨s, m, hc, -, rfl⟩ | ⟨s, hc, -, rfl⟩ | ⟨m, noinc, ha, rfl⟩ | ⟨-, rfl⟩ |
        ⟨s, tg, c, hi, hc, rfl⟩ | ⟨a, s, -, rfl⟩ | ⟨a, s, -, rfl⟩ | ⟨s, rank, m, -, -, rfl⟩
    · exact (no_copy hX ht hc).elim
    · exact (no_copy hX ht hc).elim
    · exact (no_asyncArrive hX ht ha).elim
    · rcases hsu with ⟨d, s, acc, mask, hi, ho⟩ | ⟨cp, ⟨pc, hget⟩, -⟩
      · exact ⟨fun _ => mma_started hpre hX ht hi ho,
          fun hexit => hmx i d s acc mask hi owner ho hexit⟩
      · exfalso
        have hg := Frame.lt_of_get hX hget
        obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
        exact ht.no_tc_cp hg hget hσ rfl
    · have h := clc_case hi hc hsu
      exact ⟨fun _ => h.1, h.2⟩
    · obtain ⟨address, s', hi, -, hcta⟩ := hsu
      have h := tensor_case hi hcta
      exact ⟨fun _ => h.1, h.2⟩
    · exact hsu.elim
    · obtain ⟨s', m', hc, htg, hcta⟩ := hsu
      have h := commit_case hc htg hcta
      exact ⟨fun _ => h.1, h.2⟩

end PTX.Kernels.Fp16Gemm8192.Proof.Safety.Memory
