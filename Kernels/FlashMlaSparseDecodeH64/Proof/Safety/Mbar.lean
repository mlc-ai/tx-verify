-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.InitCtaPublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingTensorEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RingObjects

@[expose] public section

/-! # Every mbarrier operand is covered by the prologue initialization table -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private def InTable (L : Launch) (g : Nat) (m : Loc) : Prop :=
  ∃ j : Fin 23, m = ⟨.shared, ctaOf L g, L.sharedBase + initOff j⟩

private theorem table_offsets : ∀ n : Fin 23, ∃ j : Fin 23, initOff j = 222768 + 8 * n.val := by
  decide +kernel

private theorem table_offset {g off : Nat}
    (hlo : 222768 ≤ off) (hhi : off ≤ 222944) (ha : off % 8 = 0) :
    InTable L g ⟨.shared, ctaOf L g, L.sharedBase + off⟩ := by
  let n : Fin 23 := ⟨(off - 222768) / 8, by omega⟩
  obtain ⟨j, hj⟩ := table_offsets n
  refine ⟨j, ?_⟩
  rw [hj]
  have hn : 222768 + 8 * n.val = off := by
    dsimp only [n]
    omega
  rw [hn]

local macro "in_init_table" : tactic =>
  `(tactic| apply table_offset <;> (try simp only [Wg0.lastStoreOff, Wg0.validFreeOff,
    Wg0.soReadyOff, Wg0.validReadyOff, Wg0.qkDoneOff, Wg0.svDoneOff, Wg1Tma.rawReadyOff,
    Wg1Tma.rawFreeOff, Wg1Tma.coordFreeOff, Wg1Tma.readyOff, Wg1Tma.qUtccpOff,
    Wg1Tma.lastStoreOff, Wg1Index.readyOff, Wg1Index.freeOff, Wg2.dequantReadyOff,
    Wg2.rawReadyOff, Wg2.rawFreeOff, Wg2.qUtccpOff, Wg2.svDoneOff]) <;> omega)

private theorem arrive_table {g : Nat} {d : Machine.ThreadD} {e : Event} {u : Option TState}
    {m : Loc} {tx count : Nat} {release : Bool} {scope : MbarScope}
    (hpre : Pre P L mem0) (hf : (Machine.machine P L g).Fired (some d) e u)
    (hk : e.kind = .arrive m tx count release scope) :
    InTable L g m ∧ ∀ s, d ≠ .prologue s := by
  have hSite := RingSourceSites.arrive_site hf hk
  refine ⟨?_, fun s h => by subst d; exact hSite⟩
  have addr {m' : Loc} {tx' count' : Nat} {rel' : Bool} {sc' : MbarScope}
      (h : e.kind = .arrive m' tx' count' rel' sc') (ht : InTable L g m') : InTable L g m :=
    (Kind.arrive.inj (hk.symm.trans h)).1.symm ▸ ht
  cases d
  case wg0 d =>
    rcases hSite with hd | hd | hd
    · exact addr (RingEvents.lastStore_arrive hpre hd hf) (by in_init_table)
    · exact addr (RingEvents.maskFree_arrive hpre hd hf) (by in_init_table)
    · exact addr (RingEvents.scores_arrive hpre hd hf) (by in_init_table)
  case mma d => exact addr (RingEvents.query_expectTx hpre hSite hf) (by in_init_table)
  case tma d =>
    rcases hSite with hd | hd
    · exact addr (RingEvents.rawReady_expectTx hpre hd hf) (by in_init_table)
    · exact addr (RingEvents.validFree_arrive hpre hd hf) (by in_init_table)
  case index d =>
    obtain ⟨extra, hd⟩ := hSite
    exact addr (RingEvents.validReady_arrive hpre hd hf) (by in_init_table)
  case wg2 d =>
    rcases hSite with hd | hd
    · exact addr (RingEvents.dequantReady_arrive hpre hd hf) (by in_init_table)
    · exact addr (RingEvents.rawFree_arrive hpre hd hf) (by in_init_table)
  all_goals exact hSite.elim

private theorem wait_table {g : Nat} {d : Machine.ThreadD} {e : Event} {u : Option TState}
    {m : Loc} {parity : Nat} {ok acquire : Bool} {scope : MbarScope}
    (hpre : Pre P L mem0) (hf : (Machine.machine P L g).Fired (some d) e u)
    (hk : e.kind = .wait m parity ok acquire scope) :
    InTable L g m ∧ ∀ s, d ≠ .prologue s := by
  have hSite := RingSourceSites.poll_site hf hk
  refine ⟨?_, fun s h => by subst d; exact hSite⟩
  have addr {m' : Loc} {par' : Nat} {ok' acq' : Bool} {sc' : MbarScope}
      (h : e.kind = .wait m' par' ok' acq' sc') (ht : InTable L g m') : InTable L g m :=
    (Kind.wait.inj (hk.symm.trans h)).1.symm ▸ ht
  cases d
  case wg0 d =>
    rcases hSite with hd | hd | hd
    · obtain ⟨_, h⟩ := RingEvents.maskReady_wait hpre hd hf
      exact addr h (by in_init_table)
    · obtain ⟨off, _, _, _, ho, h⟩ := RingEvents.gemmDone_wait hpre (.inl hd) hf
      rcases ho with rfl | rfl <;> exact addr h (by in_init_table)
    · obtain ⟨off, _, _, _, ho, h⟩ := RingEvents.gemmDone_wait hpre (.inr hd) hf
      rcases ho with rfl | rfl <;> exact addr h (by in_init_table)
  case mma d =>
    obtain ⟨_, _, _, rfl | rfl | rfl | rfl, h⟩ := RingEvents.mma_wait_object hpre hSite hf
    all_goals exact addr h (by in_init_table)
  case tma d =>
    rcases hSite with hd | hd | hd | hd
    · obtain ⟨_, _, rfl | rfl, h⟩ := RingEvents.tmaEntry_wait hpre (.inl hd) hf
      all_goals exact addr h (by in_init_table)
    · obtain ⟨_, _, rfl | rfl, h⟩ := RingEvents.tmaEntry_wait hpre (.inr hd) hf
      all_goals exact addr h (by in_init_table)
    · obtain ⟨_, h⟩ := RingEvents.validReady_wait hpre hd hf
      exact addr h (by in_init_table)
    · obtain ⟨_, h⟩ := RingEvents.rawFree_wait hpre hd hf
      exact addr h (by in_init_table)
  case index d =>
    obtain ⟨extra, hd⟩ := hSite
    obtain ⟨_, h⟩ := RingEvents.validFree_wait hpre hd hf
    exact addr h (by in_init_table)
  case wg2 d =>
    rcases hSite with hd | hd | hd
    · obtain ⟨_, _, _, rfl | rfl, h⟩ := RingEvents.dequant_wait_object hpre (.inl hd) hf
      all_goals exact addr h (by in_init_table)
    · obtain ⟨_, h⟩ := RingEvents.rawReady_wait hpre hd hf
      exact addr h (by in_init_table)
    · obtain ⟨_, _, _, rfl | rfl, h⟩ := RingEvents.dequant_wait_object hpre (.inr hd) hf
      all_goals exact addr h (by in_init_table)
  all_goals exact hSite.elim

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

private theorem mbar_source_of_use {g i : Nat} {m : Loc} (hUse : X.UsesMbar (g, i) m) :
    (∃ count, X.MbInit (g, i) m count) ∨
      ∃ (e : Event) (d : Machine.ThreadD),
        X.get (g, i) = some e ∧ Frame.stateAt (Machine.code P L) X g i = some (some d) ∧
          InTable L g m ∧ ∀ s, d ≠ .prologue s := by
  have published {e : Event} (he : X.get (g, i) = some e)
      (hClass : ∀ d o, (Machine.machine P L g).Fired (some d) e o →
        InTable L g m ∧ ∀ s, d ≠ .prologue s) (hKind : ∀ f, e.kind ≠ .ub f) :
      (∃ count, X.MbInit (g, i) m count) ∨
        ∃ (e : Event) (d : Machine.ThreadD),
          X.get (g, i) = some e ∧ Frame.stateAt (Machine.code P L) X g i = some (some d) ∧
            InTable L g m ∧ ∀ s, d ≠ .prologue s := by
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, o, hst, hf⟩ := RingSourceSites.fired_from_trace hX (hs g hg).machine ht he hKind
    exact Or.inr ⟨e, d, he, hst, hClass d o hf⟩
  rcases hUse with h | h | h | h | h | h | h | h | h
  · obtain ⟨tx, count, release, scope, _, he⟩ := h
    exact published he (fun _ _ hf => arrive_table hpre hf rfl) (by simp)
  · obtain ⟨s, hc, _⟩ := h
    exact (GlobalWrites.no_copy hX hc).elim
  · obtain ⟨noinc, _, he⟩ := h
    exact (Protocol.no_async_arrive hX he rfl).elim
  · obtain ⟨spec, rank, ⟨_, he⟩, hTarget⟩ := h
    have hg := Frame.lt_of_get hX he
    refine published he (fun d o hf => ?_) (by simp)
    obtain ⟨_, q, rfl, hp | hq | hv⟩ := RingCommitEvents.commit_source hpre hg hf rfl hTarget
    · exact ⟨by rw [hp.2]; in_init_table, by intro s heq; cases heq⟩
    · exact ⟨by rw [hq.2]; in_init_table, by intro s heq; cases heq⟩
    · exact ⟨by rw [hv.2]; in_init_table, by intro s heq; cases heq⟩
  · obtain ⟨_, q, ok, acq, scope, he⟩ := h
    exact published he (fun _ _ hf => wait_table hpre hf rfl) (by simp)
  · exact (Protocol.no_inval hX h).elim
  · obtain ⟨address, spec, ⟨_, he⟩, rfl⟩ := h
    refine published he (fun d o hf => ?_) (by simp)
    have hsite := RingTensorEvents.issue_site hf rfl
    refine ⟨?_, fun s heq => by subst d; exact hsite⟩
    rcases RingTensorEvents.issue_source hpre hf rfl with hm | ⟨q, k, _, _, _, _, hm, _⟩
    all_goals rw [hm]; in_init_table
  · obtain ⟨s, targets, c, hc, _, _⟩ := h
    exact (GlobalWrites.no_clc hX hc).elim
  · obtain ⟨count, hi⟩ := h
    exact .inl ⟨count, hi⟩

/-- All barrier operands name a shared location in their issuing CTA. -/
theorem mbar_own {g i : Nat} {m : Loc} (hUse : X.UsesMbar (g, i) m) :
    m.space = .shared ∧ m.cta = ctaOf L g := by
  rcases mbar_source_of_use hpre hX hs ht hUse with ⟨count, _, he⟩ | ⟨_, _, _, _, ⟨j, rfl⟩, _⟩
  · have hg := Frame.lt_of_get hX he
    obtain ⟨j, _, rfl, _⟩ := RingInitSources.init_from_trace hpre hX (hs g hg).machine ht he rfl
    exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- The full CTA gate has published the actual initialization before any non-initializing
mbarrier operand is used, including pending tensor loads and undelivered commits. -/
theorem no_mbar_uninit :
    ¬ MbarUninit L X := by
  rintro ⟨⟨g, i⟩, m, hUse, hNotInit, hbad⟩
  rcases mbar_source_of_use hpre hX hs ht hUse with
    ⟨count, hInit⟩ | ⟨e, d, he, hst, ⟨j, rfl⟩, hRole⟩
  · exact hNotInit count hInit
  · obtain ⟨init, hInit, hBefore⟩ := InitCtaPublication.completed_init_before_role hpre hX
      (fun h hh => (hs h hh).machine) ht he hst hRole j
    exact hbad ⟨init, _, hInit, .inl hBefore⟩

omit hpre hX hs ht in
/-- Each non-initializing operation refers to a table initializer published before its issue. -/
theorem published_init_of_use {e : EvId} {m : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hu : X.UsesMbar e m) (hn : ∀ n, ¬ X.MbInit e m n) :
    ∃ j : Fin 23, m = ⟨.shared, ctaOf L e.1, L.sharedBase + initOff j⟩ ∧
      ∃ i, X.MbInit i m (initCount j) ∧ InitPublished L X i e m := by
  obtain ⟨g, k⟩ := e
  rcases mbar_source_of_use hpre hX hs ht hu with ⟨count, hInit⟩ |
    ⟨e, d, he, hst, ⟨j, rfl⟩, hRole⟩
  · exact (hn count hInit).elim
  · obtain ⟨i, hi, hBefore⟩ := InitCtaPublication.completed_init_before_role hpre hX
      (fun a ha => (hs a ha).machine) ht he hst hRole j
    exact ⟨j, rfl, i, hi, .inl hBefore⟩

/-- Every byte of every used barrier object lies in the launch's allocated shared window. -/
theorem mbar_allocated {e : EvId} {m l : Loc} (hu : X.UsesMbar e m)
    (hc : Acc.Covers { loc := m, size := 8 } l) :
    mem0 l ≠ none := by
  classical
  have hInit : ∃ init count, X.MbInit init m count := by
    by_contra hn
    exact no_mbar_uninit hpre hX hs ht ⟨e, m, hu,
      fun count h => hn ⟨e, count, h⟩,
      fun ⟨init, count, h, _⟩ => hn ⟨init, count, h⟩⟩
  obtain ⟨⟨g, i⟩, count, _, he⟩ := hInit
  have hg := Frame.lt_of_get hX he
  obtain ⟨j, _, rfl, _⟩ :=
    RingInitSources.init_from_trace hpre hX (hs g hg).machine ht he rfl
  have hOff : ∀ j : Fin 23, initOff j + 8 ≤ sharedBytes := by decide +kernel
  obtain ⟨hSpace, hCTA, hLo, hHi⟩ := hc
  let offset := l.addr - L.sharedBase
  have hWindow : offset < sharedBytes := by
    have := hOff j
    change L.sharedBase + initOff j ≤ l.addr at hLo
    change l.addr < L.sharedBase + initOff j + 8 at hHi
    dsimp only [offset]
    omega
  have hAddr : l.addr = L.sharedBase + offset := by
    change L.sharedBase + initOff j ≤ l.addr at hLo
    dsimp only [offset]
    omega
  have hLoc : l = ⟨.shared, ctaOf L g, L.sharedBase + offset⟩ := by
    cases l
    simp only [Loc.mk.injEq]
    exact ⟨hSpace, hCTA, hAddr⟩
  rw [hLoc, hpre.sharedBase]
  exact hpre.sharedAllocated (ctaOf L g) (NamedBar.cta_lt hg) offset hWindow

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
