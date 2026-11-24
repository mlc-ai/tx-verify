-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputControl
public import Lemmas.Clc.ClcExecution
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites

@[expose] public section

/-! # Mandatory output events of a softmax lane -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0OutputVisits

open PTX PTX.Flow Wg0

/-- The final PV acquire and tensor fence precede the consecutive ranks for each output tile.
The two optional issuer steps have the next tile's entry rank. -/
private def rank (d : D) : Nat :=
  match d.site with
  | .svDone => 1
  | .fenceEpilogue => 2
  | .oLoad j => 36 * j.val + 3
  | .oWait j => 36 * j.val + 4
  | .oStage j k => 36 * j.val + 4 * k.val + d.sub + 5
  | .stageFence j => 36 * j.val + 37
  | .epiBar j => 36 * j.val + 38
  | .elect j | .tmaStore j => 36 * j.val + 39
  | .commit => 147
  | .everyone => 148
  | .exit => 149
  | _ => 0

private theorem rank_step {P : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hsub : d.sub < d.site.elems) (hn : Wg0.next P L g d e = some (some d')) :
    rank d' ≤ rank d + 1 := by
  cases hd : d.site <;>
    simp only [Wg0.next, Wg0.nextSite, Wg0.writeStep, Wg0.waitStep, hd] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
        exact Nat.zero_le _
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
      exact Nat.zero_le _
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    simp_all [rank, Wg0.Site.elems, Wg0.afterScoreSite, Wg0.afterLen, Wg0.afterSink,
      Wg0.epiAfterBar, Wg0.loadScores, Wg0.init]
  all_goals try (split_ifs <;> simp_all)
  all_goals omega

private theorem rank_stage {d : D} {j : Fin 4} {k : Fin 8} {s : Fin 4}
    (hsub : d.sub < d.site.elems)
    (he : rank d = 36 * j.val + 4 * k.val + s.val + 5) :
    d.site = .oStage j k ∧ d.sub = s.val := by
  obtain ⟨j, hj⟩ := j
  obtain ⟨k, hk⟩ := k
  obtain ⟨s, hs⟩ := s
  cases hd : d.site <;> simp [rank, hd, Wg0.Site.elems] at he hsub
  case oStage j' k' =>
    have hj' : j'.val < 4 := j'.isLt
    have hk' : k'.val < 8 := k'.isLt
    have hje : j' = ⟨j, hj⟩ := Fin.ext (by change j'.val = j; omega)
    have hke : k' = ⟨k, hk⟩ := Fin.ext (by change k'.val = k; omega)
    exact ⟨by rw [hje, hke], by change d.sub = s; omega⟩
  all_goals omega

private def progress : Option Machine.ThreadD → Nat
  | some (.wg0 d) => rank d
  | some .done => 149
  | _ => 0

private def allowed : Option Machine.ThreadD → Prop
  | none | some (.prologue _) | some (.wg0 _) | some .done => True
  | _ => False

private theorem init_rank (P : Params) (L : Launch) (g : Nat) : rank (Wg0.init P L g) = 0 := by
  unfold rank Wg0.init Wg0.firstSite Wg0.afterSink Wg0.afterLen
  dsimp only
  split_ifs <;> rfl

variable {P : Params} {L : Launch}

private theorem composed_step {g : Nat} {d d' : Option Machine.ThreadD} {e : Event}
    {o : Option TState} (hwg : wgOf L g = 0) (ha : allowed d)
    (hf : (Machine.machine P L g).Fired d e o) (hn : (Machine.machine P L g).next d e = some d') :
    allowed d' ∧ progress d' ≤ progress d + 1 := by
  cases d
  case none =>
    change some none = some d' at hn
    cases hn
    exact ⟨trivial, Nat.zero_le _⟩
  case some d =>
    change Machine.next P L g d e = some d' at hn
    cases d
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        exact ⟨trivial, Nat.zero_le _⟩
      · split at hn
        · rename_i w _
          split_ifs at hn with hw
          · have hw0 : w = 0 := Fin.ext (hw.symm.trans hwg)
            subst w
            cases hn
            exact ⟨trivial, by change rank (Wg0.init P L g) ≤ 1; rw [init_rank]; decide⟩
          · cases hn
            exact ⟨trivial, Nat.zero_le _⟩
        · cases hn
          exact ⟨trivial, Nat.zero_le _⟩
      · cases hn
    case wg0 d =>
      have hi : Inv P L g d := (Exists.choose_spec hf).1.2
      simp only [Machine.next] at hn
      split at hn
      · rename_i v hstep
        cases hn
        exact ⟨trivial, rank_step hi.subLt hstep⟩
      · split_ifs at hn with hexit
        · cases hn
          rcases hexit with h | h <;> exact ⟨trivial, by simp [progress, rank, h]⟩
        · cases hn
          exact ⟨trivial, Nat.zero_le _⟩
      · cases hn
    case done => cases hn
    all_goals exact ha.elim

/-- A visited rank is the state before an actual event and includes the fired operands. -/
private def visited (P : Params) (L : Launch) (g : Nat) (es : List Event) (n : Nat) : Prop :=
  ∃ k < es.length, ∃ (d : D) (e : Event) (o : Option TState),
    (Machine.machine P L g).after (Machine.machine P L g).init (es.take k) = some (some (.wg0 d)) ∧
      es[k]? = some e ∧ rank d = n ∧ (Machine.machine P L g).Fired (some (.wg0 d)) e o ∧
      ∃ q, (Machine.machine P L g).next (some (.wg0 d)) e = some q ∧ n < progress q

private def history (P : Params) (L : Launch) (g : Nat) (d : Option Machine.ThreadD)
    (es : List Event) : Prop :=
  allowed d ∧ (Machine.machine P L g).after (Machine.machine P L g).init es = some d ∧
    ∀ n, 0 < n → n < progress d → visited P L g es n

private theorem visited_snoc {g n : Nat} {es : List Event} {e : Event} (h : visited P L g es n)
    : visited P L g (es ++ [e]) n := by
  obtain ⟨k, hk, d, f, o, hst, hf, hr, hfire, hs⟩ := h
  refine ⟨k, by simp; omega, d, f, o, ?_, ?_, hr, hfire, hs⟩
  · simpa only [List.take_append_of_le_length (Nat.le_of_lt hk)] using hst
  · simpa only [List.getElem?_append_left hk] using hf

private theorem history_step {g : Nat} {d d' : Option Machine.ThreadD} {es : List Event} {e : Event}
    {o : Option TState} (hwg : wgOf L g = 0) (h : history P L g d es)
    (hf : (Machine.machine P L g).Fired d e o) (hn : (Machine.machine P L g).next d e = some d') :
    history P L g d' (es ++ [e]) := by
  obtain ⟨ha, hstep⟩ := composed_step hwg h.1 hf hn
  refine ⟨ha, ?_, ?_⟩
  · rw [PTX.Flow.Machine.after_snoc, h.2.1]
    exact hn
  · intro n hpos hlt
    by_cases hprior : n < progress d
    · exact visited_snoc (h.2.2 n hpos hprior)
    have heq : n = progress d := by omega
    have hwg0 : ∃ v, d = some (.wg0 v) := by
      cases d
      · change n = 0 at heq
        omega
      rename_i d
      cases d
      case wg0 v => exact ⟨v, rfl⟩
      case prologue s =>
        change n = 0 at heq
        omega
      case done =>
        change none = some d' at hn
        cases hn
      all_goals exact h.1.elim
    obtain ⟨v, rfl⟩ := hwg0
    refine ⟨es.length, by simp, v, e, o, ?_, ?_, heq.symm, hf, d', hn, hlt⟩
    · rw [List.take_left]
      exact h.2.1
    · simp

/-- A followed warpgroup-zero lane is in the prologue, softmax role or return state. -/
theorem softmax_state_cases {mem0 : Mem0} {X : Execution} {g i : Nat} {d : Machine.ThreadD}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound) (hwg : wgOf L g = 0)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some d)) :
    (∃ s, d = .prologue s) ∨ (∃ s, d = .wg0 s) ∨ d = .done := by
  have ha := (hs.produces (hX.thr g hg)).prefix_induction (fun q _ => allowed q) trivial
    (fun _ _ _ _ _ h hf hn => (composed_step hwg h hf hn).1) i (some d) hstate
  cases d
  case prologue s => exact .inl ⟨s, rfl⟩
  case wg0 s => exact .inr (.inl ⟨s, rfl⟩)
  case done => exact .inr (.inr rfl)
  all_goals exact ha.elim

private theorem visited_of_prefix {mem0 : Mem0} {X : Execution} {g i n : Nat}
    {σ : Option Machine.ThreadD} (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) (hs : (Machine.machine P L g).Sound) (hwg : wgOf L g = 0)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some σ) (hpos : 0 < n) (hn : n < progress σ)
    :
    ∃ k < i, ∃ (d : D) (e : Event) (o : Option TState),
      Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d)) ∧
      X.get (g, k) = some e ∧ rank d = n ∧
      (Machine.machine P L g).Fired (some (.wg0 d)) e o ∧
      ∃ q, (Machine.machine P L g).next (some (.wg0 d)) e = some q ∧ n < progress q := by
  have hrec := (hs.produces (hX.thr g hg)).prefix_induction (history P L g)
    ⟨trivial, rfl, fun _ _ hn => (Nat.not_lt_zero _ hn).elim⟩
    (fun _ _ _ _ _ => history_step hwg) i σ hstate
  obtain ⟨k, hk, d, e, o, hst, he, hr, hf, hs'⟩ := hrec.2.2 n hpos hn
  have hki : k < i := by simp only [List.length_take] at hk; omega
  refine ⟨k, hki, d, e, o, ?_, ?_, hr, hf, hs'⟩
  · change (Machine.machine P L g).after (Machine.machine P L g).init
      ((X.tr g).take k) = some (some (.wg0 d))
    simpa only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hki)] using hst
  · simpa only [List.getElem?_take, ite_eq_left hki, Execution.get, Prod.fst, Prod.snd] using he

private theorem continued {g : Nat} {d : D} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o) (hub : ∀ f, e.kind ≠ .ub f)
    (hret : e.kind ≠ .exit) :
    ∃ u, o = some u := by
  obtain ⟨t, _, hf⟩ := hf
  generalize (Machine.machine P L g).tmpl (some (.wg0 d)) t = tm at hf
  cases tm <;> simp only [Fires] at hf <;> aesop

private theorem pvWaitBeforeEpilogue_state {mem0 : Mem0} {X : Execution} {g i : Nat} {d : D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound) (hinv : Inv P L g d)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hepilogue : d.site.inEpilogue = true) (hn : 1 < rank d) :
    ∃ w < i, ∃ site scope, X.get (g, w) = some
      ⟨site, .wait ⟨.shared, ctaOf L g, L.sharedBase + svDoneOff (d.block % 2)⟩
        (d.block / 2 % 2) true true scope⟩ ∧
      ∃ q : D, Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 q)) ∧
        q.site = .svDone ∧ q.block = d.block := by
  obtain ⟨w, hw, q, e, o, hVisited, he, hr, hf, next, hnext, hprogress⟩ :=
    visited_of_prefix hX hg hs hinv.wg hstate (n := 1) (by decide) hn
  have hq : q.site = .svDone := by
    cases h : q.site <;> simp [rank, h] at hr
    rfl
  obtain ⟨ok, scope, hk⟩ := RingEvents.gemmDone_wait_exact hpre (.inr hq) hf
  simp only [hq, reduceCtorEq, ↓reduceIte] at hk
  have hsuccess : ok = true := by
    cases ok
    · change Machine.next P L g (.wg0 q) e = some next at hnext
      simp only [Machine.next, Wg0.next, Wg0.nextSite, Wg0.waitStep, hq, hk, Bool.false_eq_true,
        ↓reduceIte] at hnext
      cases hnext
      simp [progress, rank, hq] at hprogress
    · rfl
  obtain rfl := hsuccess
  have hprior : Inv P L g q := (Exists.choose_spec hf).1.2
  have hOld := hprior.epilogueLast (by simp [hq, Site.inEpilogue])
  have hNew := hinv.epilogueLast hepilogue
  have hblock : q.block = d.block := by omega
  obtain ⟨site, kind⟩ := e
  change kind = _ at hk
  exact ⟨w, hw, site, scope, by rw [he, hk, hblock]; rfl, q, hVisited, hq, hblock⟩

/-- Every actual output issue follows its lane's successful acquire of the final PV tile. -/
theorem pvWaitBeforeIssue_state {mem0 : Mem0} {X : Execution} {g i : Nat} {d : D} {j : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound) (hinv : Inv P L g d)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hj : d.site = .tmaStore j) :
    ∃ w < i, ∃ site scope, X.get (g, w) = some
      ⟨site, .wait ⟨.shared, ctaOf L g, L.sharedBase + svDoneOff (d.block % 2)⟩
        (d.block / 2 % 2) true true scope⟩ ∧
      ∃ q : D, Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 q)) ∧
        q.site = .svDone ∧ q.block = d.block :=
  pvWaitBeforeEpilogue_state hpre hX hg hs hinv hstate
    (by rw [hj]; rfl) (by simp [rank, hj])

/-- An output Tensor Memory load follows its lane's successful acquire of the final PV tile. -/
theorem pvWaitBeforeLoad_state {mem0 : Mem0} {X : Execution} {g i : Nat} {d : D} {j : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound) (hinv : Inv P L g d)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hj : d.site = .oLoad j) :
    ∃ w < i, ∃ site scope, X.get (g, w) = some
      ⟨site, .wait ⟨.shared, ctaOf L g, L.sharedBase + svDoneOff (d.block % 2)⟩
        (d.block / 2 % 2) true true scope⟩ ∧
      ∃ q : D, Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 q)) ∧
        q.site = .svDone ∧ q.block = d.block :=
  pvWaitBeforeEpilogue_state hpre hX hg hs hinv hstate
    (by rw [hj]; rfl) (by simp only [rank, hj]; omega)

/-- A staging write also follows its lane's successful acquire of the final PV tile. -/
theorem pvWaitBeforeStage_state {mem0 : Mem0} {X : Execution} {g i : Nat} {d : D} {j : Fin 4}
    {k : Fin 8} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) (hs : (Machine.machine P L g).Sound) (hinv : Inv P L g d)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hj : d.site = .oStage j k) :
    ∃ w < i, ∃ site scope, X.get (g, w) = some
      ⟨site, .wait ⟨.shared, ctaOf L g, L.sharedBase + svDoneOff (d.block % 2)⟩
        (d.block / 2 % 2) true true scope⟩ ∧
      ∃ q : D, Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 q)) ∧
        q.site = .svDone ∧ q.block = d.block :=
  pvWaitBeforeEpilogue_state hpre hX hg hs hinv hstate
    (by rw [hj]; rfl) (by simp only [rank, hj]; omega)

/-- The CTA closing barrier follows this lane's successful acquire of the final PV tile. -/
theorem pvWaitBeforeClosing_state {mem0 : Mem0} {X : Execution} {g i : Nat} {d : D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound) (hinv : Inv P L g d)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hj : d.site = .everyone) :
    ∃ w < i, ∃ site scope, X.get (g, w) = some
      ⟨site, .wait ⟨.shared, ctaOf L g, L.sharedBase + svDoneOff (d.block % 2)⟩
        (d.block / 2 % 2) true true scope⟩ ∧
      ∃ q : D, Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 q)) ∧
        q.site = .svDone ∧ q.block = d.block :=
  pvWaitBeforeEpilogue_state hpre hX hg hs hinv hstate
    (by rw [hj]; rfl) (by simp [rank, hj])

/-- Every selected four-byte staging element has an actual write before the lane's tile fence. -/
theorem stageBeforeFence {mem0 : Mem0} {X : Execution} {g i : Nat} {d : D} {j : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound) (hwg : wgOf L g = 0)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hj : d.site = .stageFence j) (k : Fin 8) (s : Fin 4) :
    ∃ b < i, ∃ (e : Event) (d' : D) (a : Acc),
      X.get (g, b) = some e ∧
      Frame.stateAt (Machine.code P L) X g b = some (some (.wg0 d')) ∧
      d'.site = .oStage j k ∧ d'.sub = s.val ∧
      e.kind = .wr a (stagePair P L g d' (4 * k.val + s.val)).toBytes ∧
      a.loc = shLoc L g (stageWrite L g j.val k.val s.val) ∧ a.size = 4 := by
  let n := 36 * j.val + 4 * k.val + s.val + 5
  have hn : n < progress (some (.wg0 d)) := by
    change n < rank d
    simp only [rank, hj]
    have hk := k.isLt
    have hsub := s.isLt
    omega
  obtain ⟨b, hb, eD, e, o, hst, he, hr, hf, v, hnext, _⟩ :=
    visited_of_prefix hX hg hs hwg hstate (show 0 < n by omega) hn
  have hinv : Inv P L g eD := (Exists.choose_spec hf).1.2
  obtain ⟨hs', hsub⟩ := rank_stage hinv.subLt hr
  have hk : ∃ a bytes, e.kind = .wr a bytes := by
    change Machine.next P L g (.wg0 eD) e = some v at hnext
    cases hkind : e.kind <;>
      simp only [Machine.next, Wg0.next, Wg0.nextSite, Wg0.writeStep, hs', hkind,
        reduceCtorEq] at hnext
    rename_i a bytes
    exact ⟨a, bytes, rfl⟩
  obtain ⟨_, _, hk⟩ := hk
  obtain ⟨u, rfl⟩ := continued hf (by intro f; rw [hk]; exact Kind.noConfusion)
    (by rw [hk]; exact Kind.noConfusion)
  have hrole : (Wg0.code P L g).toMachine.Fired (some eD) e (some u) := hf
  obtain ⟨a, hkind, ha, hsize⟩ := fired_stageOutput hpre hg hs' hrole
  rw [hsub] at hkind ha
  exact ⟨b, hb, e, eD, a, he, hst, hs', hsub, hkind, ha, hsize⟩

/-- Every selected staging write precedes the source fence immediately before its tile barrier. -/
theorem stagedBeforeBarrier {mem0 : Mem0} {X : Execution} {g i : Nat} {d : D} {j : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound) (hwg : wgOf L g = 0) (hi : i < (X.tr g).length)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hj : d.site = .epiBar j) (k : Fin 8) (s : Fin 4) :
    ∃ fence, fence + 1 = i ∧ X.IsProxyFence (g, fence) (.async (some (.shared .cta))) none ∧
      ∃ b < fence, ∃ (e : Event) (d' : D) (a : Acc),
        X.get (g, b) = some e ∧
        Frame.stateAt (Machine.code P L) X g b = some (some (.wg0 d')) ∧
        d'.site = .oStage j k ∧ d'.sub = s.val ∧
        e.kind = .wr a (stagePair P L g d' (4 * k.val + s.val)).toBytes ∧
        a.loc = shLoc L g (stageWrite L g j.val k.val s.val) ∧ a.size = 4 := by
  obtain ⟨fence, e, d', hfc, he, hst, hs'⟩ :=
    Wg0OutputControl.fenceBeforeBarrier hi hstate hj
  have hn := hstate
  rw [← hfc, Frame.stateAt_succ he, hst] at hn
  change Machine.next P L g (.wg0 d') e = some (some (.wg0 d)) at hn
  have hk : ∃ f scope, e.kind = .fenceProxy f scope := by
    cases hkind : e.kind <;>
      simp only [Machine.next, Wg0.next, Wg0.nextSite, hs', hkind, reduceCtorEq] at hn
    exact ⟨_, _, rfl⟩
  obtain ⟨_, _, hk⟩ := hk
  obtain ⟨o, hf⟩ := (hs.produces (hX.thr g hg)).fired_at he hst
  obtain ⟨u, rfl⟩ := continued hf (by intro f; rw [hk]; exact Kind.noConfusion)
    (by rw [hk]; exact Kind.noConfusion)
  have hrole : (Wg0.code P L g).toMachine.Fired (some d') e (some u) := hf
  have hef := fired_stageFence hs' hrole
  have hproxy : X.IsProxyFence (g, fence) (.async (some (.shared .cta))) none := by
    refine ⟨e.pc, ?_⟩
    rwa [← hef]
  exact ⟨fence, hfc, hproxy, stageBeforeFence hpre hX hg hs hwg hst hs' k s⟩

private theorem rank_barrier {d : D} {j : Fin 4} (hsub : d.sub < d.site.elems)
    (he : rank d = 36 * j.val + 38) : d.site = .epiBar j := by
  cases hd : d.site <;> simp [rank, hd, Wg0.Site.elems] at he hsub
  case epiBar j' =>
    exact congrArg Wg0.Site.epiBar (Fin.ext (by omega))
  all_goals omega

/-- A completed output lane has reached the named barrier for every tile. -/
theorem barrierBeforeDone {mem0 : Mem0} {X : Execution} {g i : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound) (hwg : wgOf L g = 0)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some .done)) (j : Fin 4) :
    ∃ k < i, ∃ (d : D) (e : Event),
      Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d)) ∧
      d.site = .epiBar j ∧ X.get (g, k) = some e ∧ e.kind = .bar 9 (some 128) .sync := by
  have hj := j.isLt
  have hn : 36 * j.val + 38 < progress (some .done) := by change _ < 149; omega
  obtain ⟨k, hk, d, e, _, hst, he, hr, hf, _⟩ :=
    visited_of_prefix hX hg hs hwg hstate (show 0 < 36 * j.val + 38 by omega) hn
  have hi : Inv P L g d := (Exists.choose_spec hf).1.2
  have hd := rank_barrier hi.subLt hr
  have hbar : Wg0BarrierTrace.Bar9Site d.site := by rw [hd]; trivial
  exact ⟨k, hk, d, e, hst, hd, he, Wg0BarrierTrace.bar9_kind hpre hf hbar⟩

private theorem trackedFired {mem0 : Mem0} {X : Execution} {g i : Nat} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, i) = some e)
    (hn : ∀ f, e.kind ≠ .ub f) :
    ∃ d o, Frame.stateAt (Machine.code P L) X g i = some (some d) ∧
      (Machine.machine P L g).Fired (some d) e o := by
  have hg := Frame.lt_of_get hX he
  rcases (hs.produces (hX.thr g hg)).fired he with ⟨σ, o, hst, hf⟩ | ⟨_, _, f, rfl⟩
  · cases σ with
    | none => exact ((ht g i hg) hst).elim
    | some d => exact ⟨d, o, hst, hf⟩
  · exact (hn f rfl).elim

set_option maxRecDepth 100000 in
private theorem no_clc_sites : OpPcsFast kernel.code clcOp [] = true := by decide +kernel

private theorem noCanceled {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (g : Nat) : ¬ ClcCanceled L X g := by
  rintro ⟨_, q, howner⟩
  obtain ⟨⟨h, i⟩, s, targets, _, ⟨site, he⟩, _⟩ := hX.clc.canceled_has_issue howner
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, o, _, t, _, hf⟩ := trackedFired hX (hs h hg) ht he (by intro f h; cases h)
  change Fires t.pc (match kernel.code[(Machine.code P L h).pc d]? with
    | some ins => eventTmpl Assumptions.all L h t ins.op
    | none => .ub .pcOutOfRange) ⟨site, .clcIssue s targets⟩ o at hf
  cases hc : kernel.code[(Machine.code P L h).pc d]? with
  | none =>
    rw [hc] at hf
    cases hf.1
  | some ins =>
    rw [hc] at hf
    have hnc : clcOp ins.op = false := by
      cases hb : clcOp ins.op
      · rfl
      · exact (List.not_mem_nil (OpPcsFast.mem no_clc_sites hc hb)).elim
    have hbad := clcIssuesTo_of_op (m := s.mbar) hnc hf
    simp [clcIssuesTo] at hbad

private def isExitOp : Op → Bool
  | .ret | .exit => true
  | _ => false

set_option maxRecDepth 100000 in
private theorem exit_sites : OpPcsFast kernel.code isExitOp [Flow.exit_0] = true := by
  decide +kernel

private theorem not_wg0_exit {g : Nat} {d : D} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o) (hk : e.kind = .exit) : False := by
  obtain ⟨t, _, hf⟩ := hf
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  cases hc : kernel.code[d.site.pc]? with
  | none =>
    rw [hc] at hf
    have he := congrArg Event.kind hf.1
    rw [hk] at he
    cases he
  | some ins =>
    rw [hc] at hf
    have hop : isExitOp ins.op = true := by
      rcases fires_exit_op hf hk with h | h <;> rw [h] <;> rfl
    have hm := OpPcsFast.mem exit_sites hc hop
    generalize hp : d.site = s at hm
    clear * - s hm
    cases s <;> revert hm
    all_goals first | decide | (rename_i a; revert a; decide) |
      (rename_i a b; revert a b; decide)

/-- A softmax lane that actually exits was already in the completed role state. -/
theorem doneAtFollowedExit {mem0 : Mem0} {X : Execution} {g i : Nat} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (hFollowed : Frame.stateAt (Machine.code P L) X g i ≠ some none) (hwg : wgOf L g = 0)
    (he : X.get (g, i) = some e) (hk : e.kind = .exit) :
    Frame.stateAt (Machine.code P L) X g i = some (some .done) := by
  obtain ⟨d, _, hst, hf⟩ :=
    RingSourceSites.fired_at_followed hX hs hFollowed he (by simp [hk])
  have hrec := (hs.produces (hX.thr g (Frame.lt_of_get hX he))).prefix_induction (history P L g)
    ⟨trivial, rfl, fun _ _ hn => (Nat.not_lt_zero _ hn).elim⟩
    (fun _ _ _ _ _ => history_step hwg) i (some d) hst
  cases d
  case prologue s => exact (RingGateEvents.exit_after_prologue hf hk s rfl).elim
  case wg0 d => exact (not_wg0_exit hf hk).elim
  case done => exact hst
  all_goals exact hrec.1.elim

/-- A softmax lane that actually exits was already in the completed role state. -/
theorem doneAtExit {mem0 : Mem0} {X : Execution} {g i : Nat} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hwg : wgOf L g = 0) (he : X.get (g, i) = some e)
    (hk : e.kind = .exit) :
    Frame.stateAt (Machine.code P L) X g i = some (some .done) :=
  doneAtFollowedExit hX hs (ht g i (Frame.lt_of_get hX he)) hwg he hk

/-- A softmax lane of a complete execution reached the composed exit state. -/
theorem completeDone {mem0 : Mem0} {X : Execution} {g : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hd : Complete L X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hg : g < L.threads) (hwg : wgOf L g = 0) :
    ∃ i e, X.get (g, i) = some e ∧ e.kind = .exit ∧
      Frame.stateAt (Machine.code P L) X g i = some (some .done) := by
  rcases hd.1 g hg with hc | ⟨site, he⟩
  · exact (noCanceled hX hs ht g hc).elim
  · rw [List.getLast?_eq_getElem?] at he
    exact ⟨(X.tr g).length - 1, _, he, rfl, doneAtExit hX (hs g hg) ht hwg he rfl⟩

private theorem rank_commit {g : Nat} {d : D} {e : Event} {q : Option Machine.ThreadD}
    (hsub : d.sub < d.site.elems) (hr : rank d = 147) (hn : Machine.next P L g (.wg0 d) e = some q)
    (hi : 147 < progress q) :
    d.site = .commit ∧ e.kind = .bulkCommit ∧
      ∃ d', q = some (.wg0 d') ∧ d'.site = .everyone := by
  have hid : d.site = .commit ∨ d.site = .elect 3 ∨ d.site = .tmaStore 3 := by
    cases hd : d.site <;> simp [rank, hd, Wg0.Site.elems] at hr hsub
    case commit => exact .inl rfl
    case elect j =>
      exact .inr (.inl (congrArg Wg0.Site.elect (Fin.ext (by change j.val = 3; omega))))
    case tmaStore j =>
      exact .inr (.inr (congrArg Wg0.Site.tmaStore (Fin.ext (by change j.val = 3; omega))))
    all_goals omega
  rcases hid with h | h | h
  · cases hk : e.kind <;> simp only [Machine.next, Wg0.next, Wg0.nextSite, h, hk,
      reduceCtorEq] at hn
    cases hn
    exact ⟨h, rfl, _, rfl, rfl⟩
  · cases hk : e.kind <;> simp only [Machine.next, Wg0.next, Wg0.nextSite, h, hk,
      reduceCtorEq] at hn
    split_ifs at hn <;> cases hn <;> simp [progress, rank] at hi
  · cases hk : e.kind <;> simp only [Machine.next, Wg0.next, Wg0.nextSite, h, hk,
      reduceCtorEq] at hn
    have h3 : ¬ (3 : Fin 4).val + 1 < 4 := by decide
    rw [dite_eq_right h3] at hn
    cases hn
    simp [progress, rank] at hi

/-- The completed lane's bulk commit precedes the closing full-CTA barrier. -/
theorem commitBeforeDone {mem0 : Mem0} {X : Execution} {g i : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound) (hwg : wgOf L g = 0)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some .done)) :
    ∃ c < i, ∃ (e : Event) (d d' : D), X.get (g, c) = some e ∧
      e.kind = .bulkCommit ∧
      Frame.stateAt (Machine.code P L) X g c = some (some (.wg0 d)) ∧ d.site = .commit ∧
      Frame.stateAt (Machine.code P L) X g (c + 1) = some (some (.wg0 d')) ∧
      d'.site = .everyone := by
  obtain ⟨c, hc, d, e, _, hst, he, hr, hf, q, hn, hi⟩ :=
    visited_of_prefix hX hg hs hwg hstate (n := 147) (by decide)
      (by change 147 < 149; decide)
  have hinv : Inv P L g d := (Exists.choose_spec hf).1.2
  obtain ⟨hd, hekind, d', rfl, hd'⟩ := rank_commit hinv.subLt hr hn hi
  refine ⟨c, hc, e, d, d', he, hekind, hst, hd, ?_, hd'⟩
  rw [Frame.stateAt_succ he, hst]
  exact hn

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0OutputVisits
