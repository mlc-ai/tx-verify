-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2GemmTrace
public import Lemmas.Flow.Final
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingGateEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Lemmas.Clc.ClcExecution

@[expose] public section

/-! # Query acquire and first dequantizer write in the role history -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2ReuseHistory

open PTX PTX.Flow

private def passedQuery : Wg2.Site → Bool
  | .lenOrig | .lenExtra | .qUtccp => false
  | _ => true

private def passedStore : Wg2.Site → Bool
  | .scale r _ => decide (0 < r.val)
  | .raw r k => decide (0 < r.val ∨ 1 < k.val)
  | .store r k => decide (0 < r.val ∨ 0 < k.val)
  | .fence | .ready | .free | .barrier => true
  | _ => false

private def queried (L : Launch) (g : Nat) (e : Event) : Prop :=
  e.kind = .wait ⟨.shared, ctaOf L g, L.sharedBase + Wg2.qUtccpOff⟩ 0 true true .cta

/-- The actual event fired by a dequantizer's first store site. -/
def FirstStore (P : Params) (L : Launch) (g : Nat) (e : Event) : Prop :=
  ∃ d u, d.site = .store 0 0 ∧
    (Machine.machine P L g).Fired (some (.wg2 d)) e (some u)

private def history (P : Params) (L : Launch) (g : Nat) :
    Option Machine.ThreadD → List Event → Prop
  | some (.wg2 d), es =>
    (passedQuery d.site = true → ∃ e ∈ es, queried L g e) ∧
    (passedStore d.site = true → ∃ e ∈ es, FirstStore P L g e)
  | some .done, es => wgOf L g = 2 → ∃ e ∈ es, FirstStore P L g e
  | some (.prologue _), _ | none, _ => True
  | _, _ => wgOf L g ≠ 2

private theorem reached_first_store {P : Params} {L : Launch} {g : Nat} {d d' : Wg2.D}
    {e : Event} (hn : Wg2.next P L g d e = some (some d'))
    (h : passedStore d'.site = true) :
    passedStore d.site = true ∨ (d.site = .store 0 0 ∧ ∃ a bs, e.kind = .wr a bs) := by

  cases hd : d.site <;> simp only [Wg2.next, Wg2.nextSite, hd] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    try simp only [Wg2.lenOrigNext, Wg2.lenExtraNext, Wg2.afterScale, Wg2.afterRaw,
      Wg2.afterStore, Wg2.afterFree] at h
    repeat' split_ifs at h
    all_goals simp only [passedStore, decide_eq_true_eq] at h ⊢
    all_goals try (left; omega)
    all_goals try (simp_all; done)
    all_goals by_cases hzero : d.site = .store 0 0
    all_goals first
      | (right; exact ⟨hd.symm.trans hzero, ⟨_, _, by assumption⟩⟩)
      | (left; rw [hd, Wg2.Site.store.injEq] at hzero
         simp only [Fin.ext_iff, Fin.val_zero] at hzero
         omega)

private theorem reached_query {P : Params} {L : Launch} {g : Nat} {d d' : Wg2.D} {e : Event}
    (hn : Wg2.next P L g d e = some (some d')) (h : passedQuery d'.site = true) :
    passedQuery d.site = true ∨ (d.site = .qUtccp ∧
      ∃ m p a sc, e.kind = .wait m p true a sc) := by
  cases hd : d.site <;> simp only [Wg2.next, Wg2.nextSite, hd] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp_all [passedQuery, Wg2.lenOrigNext, Wg2.lenExtraNext]
  all_goals repeat' split at h
  all_goals simp_all

private theorem store_witness {P : Params} {L : Launch} {g : Nat}
    {d : Wg2.D} {e : Event} {o : Option TState}
    (hd : d.site = .store 0 0) (he : ∃ a bs, e.kind = .wr a bs)
    (hf : (Machine.machine P L g).Fired (some (.wg2 d)) e o) :
    FirstStore P L g e := by
  cases o with
  | some u => exact ⟨d, u, hd, hf⟩
  | none =>
    obtain ⟨t, _, hf⟩ := hf
    have hend : Ends e := fires_none_ends hf
    obtain ⟨_, _, hk⟩ := he
    obtain ⟨tag, kind⟩ := e
    change kind = _ at hk
    subst kind
    rcases hend with ⟨f, h⟩ | h <;> cases h

section
variable {P : Params} {L : Launch} {mem0 : Mem0}

private theorem query_witness {g : Nat} {d : Wg2.D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hd : d.site = .qUtccp) (he : ∃ m p a sc, e.kind = .wait m p true a sc)
    (hf : (Machine.machine P L g).Fired (some (.wg2 d)) e o) : queried L g e := by
  obtain ⟨ok, h⟩ := RingEvents.dequant_wait_exact hpre (.inl hd) hf
  obtain ⟨_, _, _, _, he⟩ := he
  have hok := (Kind.wait.inj (h.symm.trans he)).2.2.1
  obtain ⟨t, hi, _⟩ := hf
  have hInv : Wg2.Inv P L g d := hi.2
  have hb := hInv.qUtccpBlock hd
  simpa [queried, ctaOf, hd, hb, hok] using h

private theorem history_step {g : Nat} {d d' : Option Machine.ThreadD} {es : List Event} {e : Event}
    {o : Option TState} (hpre : Pre P L mem0) (h : history P L g d es)
    (hf : (Machine.machine P L g).Fired d e o) (hn : (Machine.machine P L g).next d e = some d') :
    history P L g d' (es ++ [e]) := by
  cases d
  case none =>
    change some none = some d' at hn
    cases hn
    trivial
  case some d =>
    change Machine.next P L g d e = some d' at hn
    cases d
    case prologue st =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        trivial
      · split at hn
        · rename_i w _
          split_ifs at hn with hw
          · fin_cases w <;> cases hn
            · change wgOf L g ≠ 2
              intro hh
              rw [hh] at hw
              exact (by decide : (2 : Nat) ≠ 0) hw
            · change wgOf L g ≠ 2
              intro hh
              rw [hh] at hw
              exact (by decide : (2 : Nat) ≠ 1) hw
            · change history P L g (some (.wg2 (Wg2.init P L g))) _
              unfold history Wg2.init Wg2.firstSite
              split_ifs
              all_goals simp [passedStore, passedQuery]
          · cases hn
            trivial
        · cases hn
          trivial
      · cases hn
    case wg2 d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i d' he
        cases hn
        constructor
        · intro h'
          rcases reached_query he h' with hl | ⟨hp, hk⟩
          · obtain ⟨f, hmem, hw⟩ := h.1 hl
            exact ⟨f, List.mem_append_left _ hmem, hw⟩
          · exact ⟨e, by simp, query_witness hpre hp hk hf⟩
        · intro h'
          rcases reached_first_store he h' with hl | ⟨hp, hk⟩
          · obtain ⟨f, hmem, hw⟩ := h.2 hl
            exact ⟨f, List.mem_append_left _ hmem, hw⟩
          · exact ⟨e, by simp, store_witness hp hk hf⟩
      · split_ifs at hn with hd
        · cases hn
          intro _
          obtain ⟨f, hmem, hw⟩ := h.2 (by simp [passedStore, hd])
          exact ⟨f, List.mem_append_left _ hmem, hw⟩
        · cases hn
          trivial
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn
      all_goals first | exact h | trivial
    all_goals
      simp only [Machine.next] at hn
      all_goals repeat' split at hn
      all_goals cases hn
      all_goals first | exact h | (intro hh; exact (h hh).elim) | trivial

private theorem history_at {X : Execution} {g i : Nat} {d : Wg2.D} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (hg : g < L.threads) (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d))) :
    history P L g (some (.wg2 d)) ((X.tr g).take i) :=
  (hs.produces (hX.thr g hg)).prefix_induction (history P L g) trivial
    (fun _ _ _ _ _ => history_step hpre) i (some (.wg2 d)) hd

/-- Every dequantizer tile store follows its query-completion acquire. -/
theorem query_before_store {X : Execution} {g i : Nat} {d : Wg2.D} {r : Fin 4} {s : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hg : g < L.threads)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hd : d.site = .store r s) :
    ∃ j < i, ∃ tag, X.get (g, j) = some
      ⟨tag, .wait ⟨.shared, ctaOf L g, L.sharedBase + Wg2.qUtccpOff⟩ 0 true true .cta⟩ := by
  have h := history_at hpre hX hs hg hState
  obtain ⟨e, he, hw⟩ := h.1 (by simp [passedQuery, hd])
  obtain ⟨j, hj, hget⟩ := List.mem_take_iff_getElem.mp he
  obtain ⟨tag, kind⟩ := e
  have hlt : j < (X.tr g).length := by omega
  have he' : X.get (g, j) = some ⟨tag, kind⟩ :=
    List.getElem?_eq_some_iff.mpr ⟨hlt, hget⟩
  change kind = _ at hw
  exact ⟨j, by omega, tag, hw ▸ he'⟩

/-- Each dequantizer's first tile store follows its query-completion acquire. -/
theorem query_before_first_store {X : Execution} {g i : Nat} {d : Wg2.D} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (hg : g < L.threads) (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hd : d.site = .store 0 0) :
    ∃ j < i, ∃ tag, X.get (g, j) = some
      ⟨tag, .wait ⟨.shared, ctaOf L g, L.sharedBase + Wg2.qUtccpOff⟩ 0 true true .cta⟩ :=
  query_before_store hpre hX hs hg hState hd
end

local macro "decide_site" : tactic =>
  `(tactic| first
    | decide
    | (rename_i a; revert a; decide)
    | (rename_i a b; revert a b; decide)
    | (rename_i a b c; revert a b c; decide))

private theorem at_store_tag {P : Params} {L : Launch} {g : Nat} {s : Machine.ThreadD}
    (h : (Machine.code P L g).pc s = 2752) :
    ∃ d : Wg2.D, s = .wg2 d ∧ d.site = .store 0 0 := by
  cases s
  case prologue d =>
    exfalso
    change d.pc = 2752 at h
    cases d <;> revert h <;> decide_site
  case head =>
    exfalso
    change 1843 = 2752 at h
    cases h
  case wg0 d =>
    exfalso
    change d.site.pc = 2752 at h
    generalize hd : d.site = site at h
    clear hd d
    cases site <;> revert h <;> decide_site
  case mma d =>
    exfalso
    change d.site.pc = 2752 at h
    generalize hd : d.site = site at h
    clear hd d
    cases site <;> revert h <;> decide_site
  case tma d =>
    exfalso
    change d.site.pc = 2752 at h
    generalize hd : d.site = site at h
    clear hd d
    cases site <;> revert h <;> decide_site
  case index d =>
    exfalso
    change d.site.pc = 2752 at h
    generalize hd : d.site = site at h
    clear hd d
    cases site <;> revert h <;> decide_site
  case wg2 d =>
    refine ⟨d, rfl, ?_⟩
    change d.site.pc = 2752 at h
    generalize hd : d.site = site at h ⊢
    clear hd d
    cases site <;> revert h <;> decide_site
  case idle d =>
    exfalso
    change d.pc = 2752 at h
    cases d <;> revert h <;> decide
  case done =>
    exfalso
    change 3611 = 2752 at h
    cases h

variable {P : Params}

/-- The first store's exact role state is recovered from its event in the tracked trace. -/
theorem first_store_state {L : Launch} {mem0 : Mem0} {X : Execution} {g j : Nat} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, j) = some e)
    (hfirst : FirstStore P L g e) :
    ∃ d u, Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 d)) ∧
      d.site = .store 0 0 ∧ (Machine.machine P L g).Fired (some (.wg2 d)) e (some u) := by
  obtain ⟨d, u, hd, t, hG, hf⟩ := hfirst
  have ht' : t.pc = d.site.pc := hG.1.1
  have hx : e.pc = 2752 := by
    rw [fires_pc hf, ht', hd]
    rfl
  have hn : ¬ Ends e := by
    intro hh
    cases fires_end_none hf hh
  obtain ⟨p, o, hst, hfire⟩ := RingSourceSites.fired_from_trace hX hs ht he
    (fun fault h => hn (.inl ⟨fault, h⟩))
  have hp : (Machine.code P L g).pc p = 2752 := by
    obtain ⟨v, hgood, hF⟩ := hfire
    exact (hgood.1.1.symm.trans (fires_pc hF).symm).trans hx
  obtain ⟨p', rfl, hp'⟩ := at_store_tag hp
  cases o with
  | none =>
    obtain ⟨_, _, hF⟩ := hfire
    exact (hn (fires_none_ends hF)).elim
  | some out => exact ⟨p', out, hst, hp', hfire⟩

private def isExitOp : Op → Bool
  | .ret | .exit => true
  | _ => false

set_option maxRecDepth 100000 in
private theorem exit_sites : OpPcsFast kernel.code isExitOp [Flow.exit_0] = true := by
  decide +kernel

private theorem not_dequant_exit {L : Launch} {g : Nat} {d : Wg2.D} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some (.wg2 d)) e o) (hk : e.kind = .exit) : False := by
  obtain ⟨t, _, hfire⟩ := hf
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hfire
  cases hc : kernel.code[d.site.pc]? with
  | none =>
    rw [hc] at hfire
    have he := congrArg Event.kind hfire.1
    rw [hk] at he
    cases he
  | some ins =>
    rw [hc] at hfire
    have hop : isExitOp ins.op = true := by
      rcases fires_exit_op hfire hk with h | h <;> rw [h] <;> rfl
    have hm := OpPcsFast.mem exit_sites hc hop
    generalize hp : d.site = s at hm
    clear * - s hm
    cases s <;> revert hm <;> decide_site

private theorem previous_reached_state {L : Launch} {X : Execution} {g i : Nat}
    {d : Machine.ThreadD} (ht : Frame.Tracked (Machine.code P L) X) (hg : g < L.threads)
    (hi : i ≤ (X.tr g).length) (hState : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hPrologue : ∀ s, d ≠ .prologue s) :
    ∃ j q e, i = j + 1 ∧ X.get (g, j) = some e ∧
      Frame.stateAt (Machine.code P L) X g j = some (some q) ∧
      Machine.next P L g q e = some (some d) := by
  cases i with
  | zero =>
    rw [Frame.stateAt_zero] at hState
    exact (hPrologue _ (Option.some.inj (Option.some.inj hState)).symm).elim
  | succ j =>
    have hJ : j < (X.tr g).length := by omega
    have hE : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hJ
    obtain ⟨q, hq⟩ := Frame.stateAt_live ht hg hState (Nat.le_succ j)
    have hn := Frame.stateAt_succ (C := Machine.code P L) hE
    rw [hState, hq] at hn
    exact ⟨j, q, _, rfl, hE, hq, hn.symm⟩

private theorem barrier_predecessor {L : Launch} {g : Nat} {q : Machine.ThreadD} {e : Event}
    {d : Wg2.D} (hn : Machine.next P L g q e = some (some (.wg2 d))) (hd : d.site = .barrier) :
    ∃ prev : Wg2.D, q = .wg2 prev ∧ prev.site = .free ∧
      totalBlocks prev.len0 prev.len1 ≤ prev.block + 1 := by
  cases q
  case prologue s =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        fin_cases w <;> split_ifs at hn <;> cases hn
        simp only [Wg2.init, Wg2.firstSite] at hd
        split_ifs at hd
      · cases hn
    · cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  case wg2 q =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i d' hs
      cases hn
      cases hq : q.site <;> simp only [Wg2.next, Wg2.nextSite, hq] at hs
      all_goals repeat' split at hs
      all_goals cases hs
      all_goals
        try simp only [Wg2.lenOrigNext, Wg2.lenExtraNext, Wg2.afterScale, Wg2.afterRaw,
          Wg2.afterStore, Wg2.afterFree] at hd
        repeat' split_ifs at hd
        all_goals first | exact ⟨q, rfl, hq, by omega⟩ | (rw [hq] at hd; cases hd) | cases hd
    · split_ifs at hn <;> cases hn
    · cases hn
  all_goals
    simp only [Machine.next] at hn
    all_goals repeat' split at hn
    all_goals cases hn

/-- The closing barrier is reached only after releasing the final raw generation. -/
theorem last_free_before_barrier_state {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat}
    {d : Wg2.D} (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hg : g < L.threads) (hi : i ≤ (X.tr g).length)
    (hReach : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hSite : d.site = .barrier) :
    ∃ j e q, j < i ∧ X.get (g, j) = some e ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 q)) ∧ q.site = .free ∧
      q.block + 1 = totalBlocks (P.topkLen (Wg2.eOf L g)) (P.extraTopkLen (Wg2.eOf L g)) := by
  obtain ⟨j, prev, e, hJ, he, hPrev, hNext⟩ :=
    previous_reached_state ht hg hi hReach (by simp)
  obtain ⟨q, rfl, hFree, hFinal⟩ := barrier_predecessor hNext hSite
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hPrev
  have hIn : Wg2.Inv P L g q := hInv
  have hLen := hIn.block
  rw [hIn.len0, hIn.len1] at hLen hFinal
  exact ⟨j, e, q, by omega, he, hPrev, hFree, by omega⟩

/-- In the dequantizer warpgroup, the composed state belongs to its prologue, body or end. -/
theorem role_state {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat} {d : Machine.ThreadD}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hg : g < L.threads) (hwg : wgOf L g = 2)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some d)) :
    (∃ s, d = .prologue s) ∨ (∃ q : Wg2.D, d = .wg2 q) ∨ d = .done := by
  have htrace := (hs g hg).machine.produces (hX.thr g hg)
  have hHist := htrace.prefix_induction (history P L g) trivial
    (fun _ _ _ _ _ => history_step hpre) i (some d) hState
  cases d
  case prologue s => exact .inl ⟨s, rfl⟩
  case wg2 q => exact .inr (.inl ⟨q, rfl⟩)
  case done => exact .inr (.inr rfl)
  all_goals exact (hHist hwg).elim

/-- A dequantizer past its closing arrival has released the final raw generation. -/
theorem last_free_before_done {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hg : g < L.threads) (hi : i ≤ (X.tr g).length) (hwg : wgOf L g = 2)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some .done)) :
    ∃ j e d, j < i ∧ X.get (g, j) = some e ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 d)) ∧ d.site = .free ∧
      d.block + 1 = totalBlocks (P.topkLen (Wg2.eOf L g)) (P.extraTopkLen (Wg2.eOf L g)) := by
  obtain ⟨j, q, e, hJ, he, hq, hn⟩ := previous_reached_state ht hg hi hState (by simp)
  rcases role_state hpre hX hs hg hwg hq with ⟨s, rfl⟩ | ⟨d, rfl⟩ | rfl
  · simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        fin_cases w <;> split_ifs at hn <;> cases hn
      · cases hn
    · cases hn
  · have hSite : d.site = .barrier := by
      simp only [Machine.next] at hn
      split at hn
      · cases hn
      · split_ifs at hn with hb
        · exact hb
        · cases hn
      · cases hn
    obtain ⟨k, f, p, hK, hf, hPrev, hp, hFinal⟩ :=
      last_free_before_barrier_state hX hs ht hg (PTX.len_of_get he).le hq hSite
    exact ⟨k, f, p, by omega, hf, hPrev, hp, hFinal⟩
  · cases hn

/-- Before its final CTA barrier, an exiting dequantizer completed the last raw generation. -/
theorem last_free_before_exit {L : Launch} {mem0 : Mem0} {X : Execution} {g i tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hwg : wgOf L g = 2) (hexit : X.get (g, i) = some ⟨tag, .exit⟩) :
    ∃ j e d, j < i ∧ X.get (g, j) = some e ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 d)) ∧ d.site = .free ∧
      d.block + 1 = totalBlocks (P.topkLen (Wg2.eOf L g)) (P.extraTopkLen (Wg2.eOf L g)) := by
  have hg := Frame.lt_of_get hX hexit
  obtain ⟨q, _, hState, hf⟩ := RingSourceSites.fired_from_trace hX (hs g hg).machine ht hexit
    (by simp)
  rcases role_state hpre hX hs hg hwg hState with ⟨s, rfl⟩ | ⟨d, rfl⟩ | rfl
  · exact (RingGateEvents.exit_after_prologue hf rfl s rfl).elim
  · exact (not_dequant_exit hf rfl).elim
  · exact last_free_before_done hpre hX hs ht hg (PTX.len_of_get hexit).le hwg hState

/-- An exiting dequantizer already issued its first tile write. -/
theorem first_store_before_exit {L : Launch} {mem0 : Mem0} {X : Execution} {g i tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hwg : wgOf L g = 2) (hexit : X.get (g, i) = some ⟨tag, .exit⟩) :
    ∃ j e, j < i ∧ X.get (g, j) = some e ∧ FirstStore P L g e := by
  have hg := Frame.lt_of_get hX hexit
  obtain ⟨d, _, hst, hf⟩ := RingSourceSites.fired_from_trace hX (hs g hg).machine ht hexit
    (by intro f hh; cases hh)
  have h := (hs g hg).machine.produces (hX.thr g hg)
  have hrec := h.prefix_induction (history P L g) trivial
    (fun _ _ _ _ _ => history_step hpre) i (some d) hst
  cases d
  case prologue s => exact (RingGateEvents.exit_after_prologue hf rfl s rfl).elim
  case wg2 d => exact (not_dequant_exit hf rfl).elim
  case done =>
    obtain ⟨e, he, hw⟩ := hrec hwg
    obtain ⟨j, hj, hget⟩ := List.mem_take_iff_getElem.mp he
    have hlt : j < (X.tr g).length := by omega
    exact ⟨j, e, by omega, List.getElem?_eq_some_iff.mpr ⟨hlt, hget⟩, hw⟩
  all_goals exact (hrec hwg).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2ReuseHistory
