-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputTrace
public import Lemmas.Flow.TraceInduction

@[expose] public section

/-! # The Tensor Memory payload carried through output staging -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0OutputPayload

open PTX PTX.Flow Wg0

private def activeTile : Wg0.Site → Option (Fin 4)
  | .oWait j | .oStage j _ => some j
  | _ => none

private def source (P : Params) (L : Launch) (g : Nat) (es : List Event) (d : D)
    (j : Fin 4) : Prop :=
  ∃ k < es.length, ∃ (d0 : D) (e : Event) (words : List Value),
    (Machine.machine P L g).after (Machine.machine P L g).init
      (es.take k) = some (some (.wg0 d0)) ∧ d0.site = .oLoad j ∧ es[k]? = some e ∧
    e.kind = .tc (.ld (64 * j.val) words .s32x32b) ∧ words.length = 64 ∧
    d = { loadOutput L g d0 j words with site := d.site, sub := d.sub }

variable {P : Params} {L : Launch}

private theorem forward_source {g : Nat} {es : List Event} {e : Event} {d d' : D} {j : Fin 4}
    (hs : source P L g es d j) (h : d' = { d with site := d'.site, sub := d'.sub }) :
    source P L g (es ++ [e]) d' j := by
  obtain ⟨k, hk, d0, f, words, hat, hd0, hf, hkind, hlen, hfields⟩ := hs
  refine ⟨k, by simp; omega, d0, f, words, ?_, hd0, ?_, hkind, hlen, ?_⟩
  · simpa only [List.take_append_of_le_length (Nat.le_of_lt hk)] using hat
  · simpa only [List.getElem?_append_left hk] using hf
  · calc
      d' = { d with site := d'.site, sub := d'.sub } := h
      _ = { loadOutput L g d0 j words with site := d'.site, sub := d'.sub } :=
        congrArg (fun v : D => { v with site := d'.site, sub := d'.sub }) hfields

private theorem loadContinues {g : Nat} {d : D} {e : Event} {o : Option TState} {col : Nat}
    {words : List Value} {shape : TcShape} (hf : (Wg0.code P L g).toMachine.Fired (some d) e o)
    (hk : e.kind = .tc (.ld col words shape)) : ∃ u, o = some u := by
  obtain ⟨t, _, hfire⟩ := hf
  generalize (Wg0.code P L g).toMachine.tmpl (some d) t = tm at hfire
  cases tm <;> simp only [Fires] at hfire <;> aesop

private theorem output_step {mem0 : Mem0} {g : Nat} {es : List Event} {e : Event} {d d' : D}
    {o : Option TState} {j : Fin 4} (hpre : Pre P L mem0)
    (ha : (Machine.machine P L g).after (Machine.machine P L g).init es = some (some (.wg0 d)))
    (hs : ∀ t, activeTile d.site = some t → source P L g es d t)
    (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o)
    (hn : Wg0.next P L g d e = some (some d')) (hj : activeTile d'.site = some j) :
    source P L g (es ++ [e]) d' j := by
  cases hd : d.site <;>
    simp only [Wg0.next, Wg0.nextSite, Wg0.writeStep, Wg0.waitStep, hd] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
        cases hj
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
      cases hj
    · cases hn
  case oLoad tile =>
    have hrole : (Wg0.code P L g).toMachine.Fired (some d) e o := hf
    cases hk : e.kind <;> rw [hk] at hn <;> try contradiction
    rename_i tc
    cases ht : tc <;> rw [ht] at hn <;> try contradiction
    rename_i col words shape
    cases hn
    have htj : tile = j := Option.some.inj hj
    subst j
    have hk' : e.kind = .tc (.ld col words shape) := hk.trans (congrArg Kind.tc ht)
    obtain ⟨u, rfl⟩ := loadContinues hrole hk'
    obtain ⟨word', hlen, he⟩ := fired_outputLoad hpre hd hrole
    have hsame : words = word' := (TcKind.ld.inj (Kind.tc.inj (hk'.symm.trans he))).2.1
    subst word'
    refine ⟨es.length, by simp, d, e, words, ?_, hd, ?_, he, hlen, rfl⟩
    · rwa [List.take_left]
    · simp
  case oWait tile =>
    split at hn
    · split at hn
      · cases hn
        have htj : tile = j := Option.some.inj hj
        subst j
        exact forward_source (hs tile (by rw [hd]; rfl)) rfl
      · cases hn
    · cases hn
  case oStage tile k =>
    split at hn
    · split at hn
      · split at hn
        · cases hn
          have htj : tile = j := Option.some.inj hj
          subst j
          exact forward_source (hs tile (by rw [hd]; rfl)) rfl
        · split at hn
          · cases hn
            have htj : tile = j := Option.some.inj hj
            subst j
            exact forward_source (hs tile (by rw [hd]; rfl)) rfl
          · cases hn
            cases hj
      · cases hn
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    simp only [Wg0.afterScoreSite, Wg0.afterLen, Wg0.afterSink, Wg0.epiAfterBar, hd,
      activeTile, reduceCtorEq] at hj
  all_goals split_ifs at hj

private def history (P : Params) (L : Launch) (g : Nat) (d : Option Machine.ThreadD)
    (es : List Event) : Prop :=
  (Machine.machine P L g).after (Machine.machine P L g).init es = some d ∧
    match d with
    | some (.wg0 v) => ∀ j, activeTile v.site = some j → source P L g es v j
    | _ => True

private theorem history_step {mem0 : Mem0} {g : Nat} {d d' : Option Machine.ThreadD}
    {es : List Event} {e : Event} {o : Option TState} (hpre : Pre P L mem0) (h : history P L g d es)
    (hf : (Machine.machine P L g).Fired d e o) (hn : (Machine.machine P L g).next d e = some d') :
    history P L g d' (es ++ [e]) := by
  refine ⟨by rw [PTX.Flow.Machine.after_snoc, h.1]; exact hn, ?_⟩
  cases d
  case none =>
    change some none = some d' at hn
    cases hn
    trivial
  case some d =>
    change Machine.next P L g d e = some d' at hn
    cases d
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        trivial
      · split at hn
        · rename_i w _
          split_ifs at hn
          · fin_cases w <;> cases hn
            · intro j hj
              simp only [Wg0.init, Wg0.firstSite, Wg0.afterSink, Wg0.afterLen] at hj
              repeat' split at hj
              all_goals cases hj
            · trivial
            · trivial
          · cases hn
            trivial
        · cases hn
          trivial
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> trivial
    case wg0 d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i v hs
        cases hn
        exact fun _ hj => output_step hpre h.1 h.2 hf hs hj
      · split_ifs at hn <;> cases hn <;> trivial
      · cases hn
    all_goals
      simp only [Machine.next] at hn
      repeat' split at hn
      all_goals cases hn
      all_goals trivial

private theorem at_active_tile {mem0 : Mem0} {X : Execution} {g i : Nat} {d : D} {j : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hd : activeTile d.site = some j) :
    ∃ p < i, ∃ (d0 : D) (e : Event) (words : List Value),
      Frame.stateAt (Machine.code P L) X g p = some (some (.wg0 d0)) ∧ d0.site = .oLoad j ∧
      X.get (g, p) = some e ∧ e.kind = .tc (.ld (64 * j.val) words .s32x32b) ∧
      words.length = 64 ∧ d = { loadOutput L g d0 j words with site := d.site, sub := d.sub } := by
  have h := (hs.produces (hX.thr g hg)).prefix_induction (history P L g) ⟨rfl, trivial⟩
    (fun _ _ _ _ _ => history_step hpre) i (some (.wg0 d)) hst
  obtain ⟨p, hp, d0, e, words, hstate, hd0, he, hk, hl, hfields⟩ :=
    h.2 j hd
  have hpi : p < i := by simp only [List.length_take] at hp; omega
  refine ⟨p, hpi, d0, e, words, ?_, hd0, ?_, hk, hl, hfields⟩
  · change (Machine.machine P L g).after (Machine.machine P L g).init
      ((X.tr g).take p) = some (some (.wg0 d0))
    simpa only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hpi)] using hstate
  · simpa only [List.getElem?_take, ite_eq_left hpi, Execution.get, Prod.fst, Prod.snd] using he

/-- At an actual staging state, the packet and row fields come from this same lane's earlier
Tensor Memory load of the tile. -/
theorem at_stage {mem0 : Mem0} {X : Execution} {g i : Nat} {d : D} {j : Fin 4} {k : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hd : d.site = .oStage j k) :
    ∃ p < i, ∃ (d0 : D) (e : Event) (words : List Value),
      Frame.stateAt (Machine.code P L) X g p = some (some (.wg0 d0)) ∧ d0.site = .oLoad j ∧
      X.get (g, p) = some e ∧ e.kind = .tc (.ld (64 * j.val) words .s32x32b) ∧
      words.length = 64 ∧ d = { loadOutput L g d0 j words with site := d.site, sub := d.sub } :=
  at_active_tile hpre hX hg hs hst (by rw [hd]; rfl)

/-- The output wait retains the exact words of its lane's tile load. -/
theorem at_wait {mem0 : Mem0} {X : Execution} {g i : Nat} {d : D} {j : Fin 4} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hd : d.site = .oWait j) :
    ∃ p < i, ∃ (d0 : D) (e : Event) (words : List Value),
      Frame.stateAt (Machine.code P L) X g p = some (some (.wg0 d0)) ∧ d0.site = .oLoad j ∧
      X.get (g, p) = some e ∧ e.kind = .tc (.ld (64 * j.val) words .s32x32b) ∧
      words.length = 64 ∧ d = { loadOutput L g d0 j words with site := d.site, sub := d.sub } :=
  at_active_tile hpre hX hg hs hst (by rw [hd]; rfl)


end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0OutputPayload
