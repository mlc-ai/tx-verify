-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReturnOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents

@[expose] public section

/-! # The actual softmax probability arrival uses the scores ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

set_option maxRecDepth 100000 in
private theorem probability_window : stableRegisterWindow 478 271 1122 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem probability_no_branch : kernel.branchTarget 1122 = false := by
  decide +kernel

private theorem probability_base_after_mask {block total : Nat} {t : TState}
    (hpre : Pre P L mem0)
    (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all L g)
      (PTX.next (setReg t 4075 (.pred true))) u ∧
      AtVector u 271 [(478, b32 (L.sharedBase + 8 * (block % 2)))] t.sub t.acc := by
  have hExtra := hAt.2.2.2.2.2.2.2
  have h2953 : t.regs 2953 = some (b32 (block % 2)) := by
    exact holds_mem hExtra.2 (by
      simp [softmaxLoopFacts, softmaxLoopRegs, factsFrom, softmaxLoopWord])
  have h452 : t.regs 452 = some (.bits 16 (BitVec.ofNat 64 (block / 2 % 2))) := by
    exact holds_mem hExtra.2 (by
      simp [softmaxLoopFacts, softmaxLoopRegs, factsFrom, softmaxLoopWord])
  let v := PTX.next (setReg t 4075 (.pred true))
  have hv : AtVector v 265
      [(4075, .pred true), (981, b32 L.sharedBase), (2953, b32 (block % 2)),
        (452, .bits 16 (BitVec.ofNat 64 (block / 2 % 2)))] t.sub t.acc := by
    refine ⟨by change t.pc + 1 = 265; rw [hAt.1], rfl, rfl, hAt.2.2.2.1,
      rfl, hExtra.1, h2953, h452, trivial⟩
  have hShared := sharedBase_lt hpre
  have hRun : ∃ u, run kernel Assumptions.all L g 5 v = some u ∧
      AtVector u 271 [(478, b32 (L.sharedBase + 8 * (block % 2)))] t.sub t.acc := by
    seg_fp hv using
      (try unfold b32)
      (try norm_bits [Wg0.land255, Nat.add_zero, Nat.add_assoc])
  obtain ⟨u, hu, hResult⟩ := hRun
  exact ⟨u, run_rtg hu, hResult⟩

theorem probability_arrival_in_round {block total : Nat} {t : TState} {e : Event}
    {before tail : List Event} {o : Option TState}
    (hpre : Pre P L mem0)
    (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc)
    (hTag : e.pc = Wg0.Site.soReady.pc)
    (hPrefix : ∀ f ∈ before, f.pc ≠ Wg0.Site.soReady.pc)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    e.kind = .arrive
      ⟨.shared, ctaOf L g, L.sharedBase + (222920 + 8 * (block % 2))⟩ 0 1 true .cta := by
  induction before generalizing t with
  | nil =>
    change Run kernel Assumptions.all L g t (e :: tail) o at hRun
    have hTemplate := mask_poll_template (g := g) hpre hAt
    have hImpossible {v : TState} {q : Option TState}
        (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t v)
        (hStep : EStep kernel Assumptions.all L g v e q) : False := by
      rw [stop_unique hLocal .refl (stops_of_estep hStep) ⟨_, hTemplate⟩] at hStep
      have h := estep_source_pc hStep
      rw [hAt.1, hTag] at h
      cases h
    cases hRun with
    | step hLocal hStep _ => exact (hImpossible hLocal hStep).elim
    | last hLocal hStep => exact (hImpossible hLocal hStep).elim
  | cons front rest ih =>
    have hRestNonempty : rest ++ e :: tail ≠ [] := by simp
    obtain ⟨ok, _, hRest⟩ := softmax_mask_poll_from_run hpre hAt hRun hRestNonempty
    have hEarlier : ∀ f ∈ rest, f.pc ≠ Wg0.Site.soReady.pc :=
      fun f hf => hPrefix f (List.mem_cons_of_mem _ hf)
    cases ok
    · obtain ⟨u, hLocal, huAt⟩ := retry_mask_poll hAt
      obtain ⟨f, after, hList⟩ := List.exists_cons_of_ne_nil hRestNonempty
      exact ih huAt hEarlier (hList ▸ after_softmax_local_prefix hLocal (hList ▸ hRest))
    · obtain ⟨u, hLocal, huAt⟩ := probability_base_after_mask (g := g) hpre hAt
      obtain ⟨f, after, hList⟩ := List.exists_cons_of_ne_nil hRestNonempty
      have hRun' : Run kernel Assumptions.all L g u (rest ++ e :: tail) o :=
        hList ▸ after_softmax_local_prefix hLocal (hList ▸ hRest)
      have hBase := sharedBase_lt hpre
      have hAddr : L.sharedBase + 8 * (block % 2) + 222920 =
          L.sharedBase + (222920 + 8 * (block % 2)) := by omega
      rw [← hAddr]
      exact arrival_in_register_window probability_window Flow.code_1121 Flow.code_1122
        (by decide) (by decide) (by decide) probability_no_branch
        (by rw [huAt.1]) (by rw [huAt.1]; decide) huAt.2.2.2.2.1 (by omega)
        (by rw [hAddr]; exact Wg0.ringAddr_mod8 hpre (off := 222920) (by decide))
        hTag hEarlier hRun'

private theorem probability_arrival_in_trace {block total : Nat} {t : TState} {e : Event}
    {events : List Event} {o : Option TState}
    (hpre : Pre P L mem0) (hBlock : block < total) (hLimit : total < 2 ^ 31)
    (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc)
    (he : e ∈ events) (hTag : e.pc = Wg0.Site.soReady.pc)
    (hRun : Run kernel Assumptions.all L g t events o) :
    ∃ buf : Fin 2, e.kind = .arrive
      ⟨.shared, ctaOf L g, L.sharedBase + (222920 + 8 * buf.val)⟩ 0 1 true .cta := by
  let seen := events.takeWhile (!isProbabilityPublication ·)
  let later := events.dropWhile (!isProbabilityPublication ·)
  have hSplit : events = seen ++ later := List.takeWhile_append_dropWhile.symm
  have hPrefix : ∀ f ∈ seen, f.pc ≠ Wg0.Site.soReady.pc := by
    intro f hf
    have h := List.all_eq_true.mp List.all_takeWhile f hf
    simpa [isProbabilityPublication, Bool.not_eq_true'] using h
  have hLater : e ∈ later := by
    rw [hSplit] at he
    exact (List.mem_append.mp he).resolve_left (fun h => hPrefix e h hTag)
  obtain ⟨pub, tail, hTail⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hLater)
  have hPub : pub.pc = Wg0.Site.soReady.pc := by
    have hHead := List.head?_dropWhile_not (!isProbabilityPublication ·) events
    have hCut : events.dropWhile (!isProbabilityPublication ·) = pub :: tail := hTail
    rw [hCut] at hHead
    simpa [isProbabilityPublication] using hHead
  rw [hTail] at hSplit hLater
  rw [hSplit] at hRun
  rcases List.mem_cons.mp hLater with rfl | hAfter
  · exact ⟨⟨block % 2, Nat.mod_lt _ (by decide)⟩,
      probability_arrival_in_round hpre hAt hPub hPrefix hRun⟩
  · have hFacts : Holds t.regs (softmaxLoopFacts block total) := hAt.2.2.2.2.2.2.2.2
    obtain ⟨u, hu, hRegs, hPublication⟩ :=
      softmax_loop_facts_at_publication (by rw [hAt.1]; decide) (by rw [hAt.1]; decide)
        hFacts hPub hPrefix hRun
    by_cases hMore : block + 1 < total
    · obtain ⟨opening, rest, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hAfter)
      have hOpen : opening.pc ≤ 256 := by
        obtain ⟨start, hLocal, hAt', hRun'⟩ :=
          softmax_next_head_after_publication hMore hLimit hu hRegs hPublication (by simp)
        exact softmax_opening_event_bound hAt'.1 (after_softmax_local_prefix hLocal hRun')
      have hRest : e ∈ rest := by
        apply (List.mem_cons.mp hAfter).resolve_left
        intro hEq
        rw [← hEq, hTag] at hOpen
        exact (by decide : ¬ Wg0.Site.soReady.pc ≤ 256) hOpen
      obtain ⟨poll, rest, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hRest)
      obtain ⟨v, hv, hRun'⟩ :=
        softmax_next_mask_after_publication hpre hMore hLimit hu hRegs hPublication
      exact probability_arrival_in_trace hpre hMore hLimit hv hRest hTag hRun'
    · have hFinal : total = block + 1 := by omega
      subst total
      have hNo := event_after_final_publication_lower hLimit hu hRegs hPublication hAfter
      rw [hTag] at hNo
      exact (by decide : ¬ 1147 ≤ Wg0.Site.soReady.pc) hNo |>.elim
termination_by events.length
decreasing_by
  simp only [hSplit, List.length_append, List.length_cons]
  omega

/-- A softmax probability publication still names its scores-ring slot after dismissal. -/
theorem actual_softmax_publication {i : Nat} {e : Event} {m : Loc}
    {tx count : Nat} {release : Bool} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hWg : wgOf L g = 0)
    (hTag : e.pc = Wg0.Site.soReady.pc) (hKind : e.kind = .arrive m tx count release scope) :
    ∃ buf : Fin 2, e.kind = .arrive
      ⟨.shared, ctaOf L g, L.sharedBase + (222920 + 8 * buf.val)⟩ 0 1 true .cta := by
  have hg := Frame.lt_of_get hX he
  rcases Frame.fired hs hX he with ⟨state, _, hd, hFire⟩ | ⟨_, _, _, hUb⟩
  · cases state with
    | some state =>
      have hSite := RingSourceSites.arrive_site hFire hKind
      have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
      cases state with
      | wg0 d =>
        have hp := Frame.event_pc hs hX he hd
        change e.pc = d.site.pc at hp
        have hPub : d.site = .soReady := by
          rcases hSite with h | h | h
          · rw [h, hTag] at hp
            cases hp
          · rw [h, hTag] at hp
            cases hp
          · exact h
        exact ⟨⟨d.block % 2, Nat.mod_lt _ (by decide)⟩, RingEvents.scores_arrive hpre hPub hFire⟩
      | wg2 d => change wgOf L g = 2 at hRole; omega
      | mma _ => change warpOf L g = 4 at hRole; unfold wgOf warpOf at *; omega
      | tma _ => change warpOf L g = 5 at hRole; unfold wgOf warpOf at *; omega
      | index _ => change warpOf L g = 7 at hRole; unfold wgOf warpOf at *; omega
      | prologue _ | head | idle _ | done => exact hSite.elim
    | none =>
      obtain ⟨j, hj, d, f, hf, hState, hn⟩ := prior_dismissal (PTX.len_of_get he).le hd
      have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
      cases dismissal_is_consumer hpre hX hs hf hState hn with
      | wg0 d =>
        obtain ⟨start, hBefore, initial, hSite, _, hAnchor⟩ :=
          dismissed_wg0_first_mask_ready hpre hX hs hf hState hn
        let events := (X.tr g).drop start
        have hGet : events[i - start]? = some e := by
          change ((X.tr g).drop start)[i - start]? = _
          rw [List.getElem?_drop, Nat.add_sub_of_le (show start ≤ i by omega)]
          exact he
        have hMem := List.mem_of_getElem? hGet
        obtain ⟨t, o, hGood, hRun⟩ := actual_suffix_from_followed hX hg (hs g hg) hAnchor
          (List.ne_nil_of_mem hMem)
        have hAt := softmax_mask_entry_facts hSite
          (show (Wg0.code P L g).AtD initial t from hGood.1)
        have hBlock : initial.block < Wg0.blocksOf P L g :=
          (show Wg0.Inv P L g initial from hGood.2).blockLt
        have hTotal : Wg0.blocksOf P L g < 2 ^ 31 := by
          have h := (Wg0.blocksOf_word_bounds hpre (Wg1Mma.batchOf_lt hpre hg)).2
          omega
        exact probability_arrival_in_trace hpre hBlock hTotal hAt hMem hTag hRun
      | wg2 d => change wgOf L g = 2 at hRole; omega
  · rw [hUb] at hKind
    cases hKind

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
