-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1IndexOrdinal
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1IndexShuffle
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1IndexTracking
import Lemmas.Flow.NotClc

@[expose] public section

/-! # Matching the real index warp's consecutive butterfly instances -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Index

open PTX PTX.Flow PTX.Proof

noncomputable section

set_option maxRecDepth 10000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem next_final_block {g : Nat} {d d' : D} {e : Event}
    (hi : Inv P L g d) (hn : next P L g d e = some (some d'))
    (hd : d'.site = .barrier) :
    d'.block + 1 = totalBlocks d.len0 d.len1 := by
  have hb := hi.block
  cases hs : d.site <;> simp only [next, nextSite, hs] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    try simp only [afterPairFirst, afterReady] at hd ⊢
    repeat' split_ifs at hd ⊢
    all_goals try cases hd
    all_goals simp_all
    all_goals omega

private theorem barrier_not_shuffle {g : Nat} {d : D} {e : Event}
    (hd : d.site = .barrier) (hn : next P L g d e = some none) :
    Execution.isShfl e = false := by
  obtain ⟨tag, kind⟩ := e
  cases kind <;> simp_all [next, nextSite, Execution.isShfl]

private theorem count_append {pre : List Event} {e : Event} :
    (pre ++ [e]).countP Execution.isShfl =
      pre.countP Execution.isShfl + if Execution.isShfl e then 1 else 0 := by
  rw [List.countP_append]
  simp

private theorem count_step {g k : Nat} {e : Event}
    (he : X.get (g, k) = some e) :
    ((X.tr g).take (k + 1)).countP Execution.isShfl =
      ((X.tr g).take k).countP Execution.isShfl + if Execution.isShfl e then 1 else 0 := by
  rw [List.take_add_one, show (X.tr g)[k]? = some e from he, Option.toList_some, count_append]

private def Ordinal (X : Execution) (g k : Nat) : Nat :=
  ((X.tr g).take k).countP Execution.isShfl

private theorem ordinal_mono {g i j : Nat} (h : i ≤ j) :
    Ordinal X g i ≤ Ordinal X g j :=
  (List.take_isPrefix_take.mpr (Or.inl h)).countP_le

private def blocks (P : Params) (L : Launch) (g : Nat) : Nat :=
  totalBlocks (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g))

private def WasDismissed (P : Params) (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  ∃ j d e, 5 ≤ j ∧ j < k ∧ X.get (g, j) = some e ∧
    Frame.stateAt (Machine.code P L) X g j = some (some (.index d)) ∧
    Machine.next P L g (.index d) e = some none

private def IndexFrame (P : Params) (L : Launch) (X : Execution) (g j : Nat) :
    Option (Option Machine.ThreadD) → Prop
  | none => True
  | some none => WasDismissed P L X g j
  | some (some (.index d)) => d.site = .barrier → d.block + 1 = blocks P L g
  | some (some .done) => Ordinal X g j = 3 + 2 * blocks P L g
  | _ => False

private theorem frame_after_dispatch {g : Nat} {first : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hw : warpOf L g = 7) (he0 : X.get (g, 4) = some first) :
    ∀ n, 5 + n ≤ (X.tr g).length →
      IndexFrame P L X g (5 + n) (Frame.stateAt (Machine.code P L) X g (5 + n)) := by
  obtain ⟨hstart, hcount⟩ := shuffle_dispatch_prefix hpre hX hs hw he0
  intro n
  induction n with
  | zero =>
    intro _
    simp only [Nat.add_zero, hstart, IndexFrame]
    cases h0 : P.topkLenBase <;> cases h1 : P.extraTopkLenBase <;>
      simp [init, firstSite, h0, h1]
  | succ n ih =>
    intro hlen
    have hlt : 5 + n < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, 5 + n) = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hlast := ih hlt.le
    simp only [Nat.add_succ, Frame.stateAt_succ (show (X.tr g)[5 + n]? = some e from he)]
    cases hstate : Frame.stateAt (Machine.code P L) X g (5 + n) with
    | none => trivial
    | some s =>
      rw [hstate] at hlast
      cases s with
      | none =>
        change WasDismissed P L X g (5 + n) at hlast
        obtain ⟨j, d, ev, hj, hj', he', ht, hn⟩ := hlast
        exact ⟨j, d, ev, hj, by omega, he', ht, hn⟩
      | some s =>
        change IndexFrame P L X g (5 + n + 1) (Machine.next P L g s e)
        cases s <;> try exact hlast.elim
        case done => trivial
        case index d =>
          have hg := Frame.lt_of_get hX he
          obtain ⟨o, hf⟩ := RingEvents.fired_of_trace hX (hs _ hg) he hstate
          have hinv : Inv P L g d := hf.choose_spec.1.2
          simp only [Machine.next]
          split
          · rename_i d' hn
            intro hd
            simpa only [blocks, hinv.len0, hinv.len1] using next_final_block hinv hn hd
          · rename_i hn
            by_cases hd : d.site = .barrier
            · have hb := (show d.site = .barrier → d.block + 1 = blocks P L g from hlast) hd
              simp only [hd, ↓reduceIte, IndexFrame]
              have hn' := shuffleCount_at hstart hcount (by omega : 5 ≤ 5 + n) hlt.le hstate
              have hkind := barrier_not_shuffle hd hn
              unfold Ordinal
              rw [count_step he, hkind, hn', shuffleCount, hd]
              change 3 + 2 * d.block + 2 + 0 = 3 + 2 * blocks P L g
              omega
            · simp only [hd, ↓reduceIte, IndexFrame]
              exact ⟨5 + n, d, e, by omega, by omega, he, hstate, by simp [Machine.next, hn, hd]⟩
          · trivial

variable {g i : Nat}

private theorem frame_at {e : Event} (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound) (hw : warpOf L g = 7) (hi : 5 ≤ i)
    (he : X.get (g, i) = some e) :
    IndexFrame P L X g i (Frame.stateAt (Machine.code P L) X g i) := by
  have hlen : i < (X.tr g).length := PTX.len_of_get he
  obtain ⟨first, hfirst⟩ : ∃ e, X.get (g, 4) = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega : (4 : Nat) < (X.tr g).length)⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hi
  exact frame_after_dispatch hpre hX hs hw hfirst n hlen.le

private def isExitOp : Op → Bool
  | .ret | .exit => true
  | _ => false

private theorem notExitOpcode (s : Site) :
    (kernel.code[s.pc]?).any (fun i => isExitOp i.op) = false := by
  cases s with
  | lenOrig | lenExtra | barrier => decide +kernel
  | pair extra first hi => cases extra <;> cases first <;> cases hi <;> decide +kernel
  | coord extra hi => cases extra <;> cases hi <;> decide +kernel
  | quad1 extra | quad2 extra | valid extra | ready extra | waitFree extra =>
    cases extra <;> decide +kernel

private theorem index_fired_not_exit {g : Nat} {d : D} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some (.index d)) e o) :
    e.kind ≠ .exit := by
  intro he
  obtain ⟨t, _, hf⟩ := hf
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl asms L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  have hn := notExitOpcode d.site
  split at hf
  · rename_i ins hc
    rw [hc] at hn
    rcases fires_exit_op hf he with hx | hx <;> simp [hx, isExitOp] at hn
  · have hk := congrArg Event.kind hf.1
    rw [he] at hk
    cases hk

private theorem done_fired_exit {g : Nat} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some .done) e o) : e.kind = .exit := by
  obtain ⟨t, ⟨ha, _⟩, hf⟩ := hf
  change Fires t.pc (match kernel.code[3611]? with
    | some ins => eventTmpl asms L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  have hp : t.pc = 3611 := ha.1
  rw [hp, Flow.code_exit_0] at hf
  exact congrArg Event.kind hf.1

private theorem actual_state_or_prior_dismissal {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hw : warpOf L g = 7) (hi : 5 ≤ i) (he : X.get (g, i) = some e) (hkind : ∀ f, e.kind ≠ .ub f) :
    WasDismissed P L X g i ∨
      (∃ d, Frame.stateAt (Machine.code P L) X g i = some (some (.index d)) ∧ e.kind ≠ .exit) ∨
      (e.kind = .exit ∧ Ordinal X g i = 3 + 2 * blocks P L g) := by
  have hg := Frame.lt_of_get hX he
  have hframe := frame_at hpre hX hs hw hi he
  rcases ((hs g hg).produces (hX.thr g hg)).fired he with ⟨s, o, hstate, hf⟩ | ⟨_, _, f, hk⟩
  · change Frame.stateAt (Machine.code P L) X g i = some s at hstate
    rw [hstate] at hframe
    cases s with
    | none => exact .inl hframe
    | some s =>
      cases s <;> try exact False.elim hframe
      case index d => exact .inr (.inl ⟨d, hstate, index_fired_not_exit hf⟩)
      case done => exact .inr (.inr ⟨done_fired_exit hf, hframe⟩)
  · exact (hkind f (congrArg Event.kind hk)).elim

private def BadOrdinal (P : Params) (L : Launch) (X : Execution) (n : Nat) : Prop :=
  ∃ g i d e, warpOf L g = 7 ∧ 5 ≤ i ∧ X.get (g, i) = some e ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.index d)) ∧
    Machine.next P L g (.index d) e = some none ∧ Ordinal X g i = n

private theorem bad_is_shuffle {d : D} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hn : Machine.next P L g (.index d) e = some none) : Execution.isShfl e = true := by
  by_contra hk
  have hb : ValidInput P L g d e := by
    obtain ⟨p, kind⟩ := e
    cases h : d.site <;> cases kind <;> simp_all [ValidInput, Execution.isShfl]
  exact next_tracked_of_input hpre hX (hs _ (Frame.lt_of_get hX he)) he hd hb hn

private theorem prior_dismissal_has_smaller_ordinal {g j n : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hw : warpOf L g = 7) (hord : Ordinal X g j ≤ n)
    (hmin : ∀ m < n, ¬ BadOrdinal P L X m)
    (hf : WasDismissed P L X g j) : False := by
  obtain ⟨i, d, e, hi, hij, he, hd, hnext⟩ := hf
  have hk := bad_is_shuffle hpre hX hs he hd hnext
  have hm := ordinal_mono (X := X) (g := g) (show i + 1 ≤ j by omega)
  have hstep : Ordinal X g (i + 1) = Ordinal X g i + 1 := by
    unfold Ordinal
    rw [count_step he, hk]
    rfl
  rw [hstep] at hm
  exact hmin _ (by omega) ⟨g, i, d, e, hw, hi, he, hd, hnext, rfl⟩

private def dispatchState : Nat → Machine.ThreadD
  | 0 => .prologue .shfl0
  | 1 => .prologue .shfl1
  | 2 => .prologue .barrier
  | 3 => .prologue (.handoff 1)
  | _ => .head

private theorem dispatch_state_prefix (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound) (hw : warpOf L g = 7) (hi : i < 5)
    (hlen : i ≤ (X.tr g).length) :
    Frame.stateAt (Machine.code P L) X g i = some (some (dispatchState i)) := by
  have hgroup : wgOf L g = 1 := by unfold wgOf warpOf at *; omega
  have earlier (j : Nat) (hj : j < i) : ∃ e, X.get (g, j) = some e :=
    ⟨_, List.getElem?_eq_getElem (hj.trans_le hlen)⟩
  interval_cases i
  · exact Frame.stateAt_zero
  · obtain ⟨_, hp⟩ := earlier 0 (by decide)
    exact PrologueShuffleTrace.state_one hpre hX hs hp
  · obtain ⟨_, hp⟩ := earlier 1 (by decide)
    have h := PrologueShuffleTrace.state_two hpre hX hs hp
    rw [hw] at h
    exact h
  · obtain ⟨_, hp⟩ := earlier 2 (by decide)
    exact PrologueShuffleTrace.state_three hpre hX hs hp hgroup
  · obtain ⟨_, hp⟩ := earlier 3 (by decide)
    exact PrologueShuffleTrace.state_four hpre hX hs hp hgroup

private theorem dispatch_state {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hw : warpOf L g = 7) (hi : i < 5) (he : X.get (g, i) = some e) :
    Frame.stateAt (Machine.code P L) X g i = some (some (dispatchState i)) :=
  dispatch_state_prefix hpre hX hs hw hi (PTX.len_of_get he).le

private def DispatchEvent (e : Event) : Nat → Prop
  | 2 => e.kind = .bar 0 none .sync
  | 3 => ∃ inst, e.kind = .setMaxReg false 72 inst
  | _ => ∃ a r ok, e.kind = .shfl .idx a 0 31 r ok

private theorem dispatch_event {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hw : warpOf L g = 7) (hi : i < 5) (he : X.get (g, i) = some e) : DispatchEvent e i := by
  have hg := Frame.lt_of_get hX he
  have hgroup : wgOf L g = 1 := by unfold wgOf warpOf at *; omega
  have hstate := dispatch_state hpre hX hs hw hi he
  interval_cases i
  · rw [PrologueShuffleTrace.first_event hpre hX hs he]
    exact ⟨_, _, _, rfl⟩
  · rw [PrologueShuffleTrace.second_event hpre hX hs he]
    exact ⟨_, _, _, rfl⟩
  · obtain ⟨o, t, ⟨hat, _⟩, hf⟩ := RingEvents.fired_of_trace hX (hs _ hg) he hstate
    have hp : t.pc = 97 := hat.1
    change Fires t.pc (match kernel.code[97]? with
      | some ins => eventTmpl asms L g t ins.op
      | none => .ub .pcOutOfRange) e o at hf
    rw [hp, Flow.code_bar_0] at hf
    exact congrArg Event.kind hf.1
  · obtain ⟨o, t, ⟨hat, _⟩, hf⟩ := RingEvents.fired_of_trace hX (hs _ hg) he hstate
    have hp : t.pc = 1842 := hat.1
    change Fires t.pc (match kernel.code[1842]? with
      | some ins => eventTmpl asms L g t ins.op
      | none => .ub .pcOutOfRange) e o at hf
    rw [hp, Flow.code_setMaxReg_1] at hf
    have hp' : ∃ inst, e = ⟨1842, .setMaxReg false 72 inst⟩ ∧ o = some (PTX.next t) := hf
    obtain ⟨inst, h, _⟩ := hp'
    exact ⟨inst, congrArg Event.kind h⟩
  · rw [PrologueShuffleTrace.head_event hpre hX hs he hgroup]
    exact ⟨_, _, _, rfl⟩

private theorem dispatch_not_exit {g i tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hw : warpOf L g = 7) (hi : i < 5) (he : X.get (g, i) = some ⟨tag, .exit⟩) : False := by
  have h := dispatch_event hpre hX hs hw hi he
  interval_cases i <;> simp [DispatchEvent] at h

private theorem dispatch_shuffle_lt_three {g j n : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hw : warpOf L g = 7) (hj : j < 5) (he : X.get (g, j) = some e) (hn : X.ShflK (g, j) n) :
    n < 3 := by
  by_cases hsmall : j ≤ 2
  · have hc : Ordinal X g j ≤ j := List.countP_le_length.trans (List.length_take_le _ _)
    have ho : Ordinal X g j = n := hn.2
    omega
  have hkind : Execution.isShfl e = true := by
    obtain ⟨_, _, _, _, _, _, _, h⟩ := hn.1
    rw [he] at h
    cases h
    rfl
  interval_cases j
  · have h := dispatch_event hpre hX hs hw (by decide) he
    obtain ⟨inst, hh⟩ := h
    obtain ⟨p, k⟩ := e
    change k = _ at hh
    subst k
    cases hkind
  · have hcount := (shuffle_dispatch_prefix hpre hX hs hw he).2
    rw [show (5 : Nat) = 4 + 1 by decide, count_step he, hkind] at hcount
    have ho : Ordinal X g 4 = n := hn.2
    change ((X.tr g).take 4).countP Execution.isShfl = n at ho
    change ((X.tr g).take 4).countP Execution.isShfl + 1 = 3 at hcount
    omega

private theorem peer_warp {g shift : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (hshift : shift < 32) :
    SameWarp L g (butterflyPeer L g shift) := by
  have hl (g : Nat) : PTX.laneOf L g = laneOf L g := by
    rw [PTX.laneOf, Proof.laneOf, tidOf_eq hpre, hpre.block]
  have hmem : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have h := Step.sameWarp_lane (by rw [hpre.block]) hg (Nat.xor_lt_two_pow (n := 5) hmem hshift)
  simpa only [hl, butterflyPeer] using h.1

private theorem matched_at_minimum {g i n shift : Nat} {d : D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hw : warpOf L g = 7) (hi : 5 ≤ i) (he : X.get (g, i) = some e)
    (hn : X.ShflK (g, i) n) (hlo : 3 ≤ n) (hbound : n < 3 + 2 * blocks P L g)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hshift : shift < 32) (hmin : ∀ m < n, ¬ BadOrdinal P L X m) :
    MatchingButterfly P L X g n shift d := by
  let h := butterflyPeer L g shift
  have hw' : SameWarp L g h := peer_warp hpre (Frame.lt_of_get hX he) hshift
  have hwarp : warpOf L h = 7 := by
    rw [warpOf, tidOf_eq hpre] at hw ⊢
    have hh := hw'.2
    rw [hpre.block] at hh
    exact hh.symm.trans hw
  have hcta : ctaOf L h = ctaOf L g := hw'.1.2.2.symm
  have hblocks : blocks P L h = blocks P L g := by simp only [blocks, eOf, ctaidY, hcta]
  change (¬ ShflExited X h n) ∧ _
  constructor
  · rintro ⟨j, tag, hget, hcount⟩
    by_cases hj : j < 5
    · exact dispatch_not_exit hpre hX hs hwarp hj hget
    rcases actual_state_or_prior_dismissal hpre hX hs hwarp (Nat.le_of_not_gt hj) hget
        (fun _ h => by cases h) with hbad | ⟨d', _, hn⟩ | ⟨_, hor⟩
    · exact prior_dismissal_has_smaller_ordinal hpre hX hs hwarp hcount hmin hbad
    · exact hn rfl
    · have hc : Ordinal X h j ≤ n := hcount
      rw [hor, hblocks] at hc
      omega
  · intro j e' hn' he'
    have hj : 5 ≤ j := by
      by_contra! hj
      exact (Nat.not_lt_of_ge hlo) (dispatch_shuffle_lt_three hpre hX hs hwarp hj he' hn')
    have hnc : ∀ f, e'.kind ≠ .ub f := by
      obtain ⟨_, _, _, _, _, _, _, hget⟩ := hn'.1
      rw [he'] at hget
      cases hget
      intro f hu
      cases hu
    rcases actual_state_or_prior_dismissal hpre hX hs hwarp hj he' hnc with
      hbad | ⟨d', hstate, _⟩ | ⟨hExit, _⟩
    · exact (prior_dismissal_has_smaller_ordinal hpre hX hs hwarp hn'.2.le hmin hbad).elim
    · have heq := same_index_shuffle_stage hpre hX hs hw' hw hwarp hi hj he he' hn hn' hd hstate
      exact ⟨d', hstate, heq⟩
    · obtain ⟨_, _, _, _, _, _, _, hget⟩ := hn'.1
      rw [he'] at hget
      cases hget
      cases hExit

private def indexRoute (L : Launch) (g : Nat) : Option Machine.ThreadD → Prop
  | some (.index _) => warpOf L g = 7
  | _ => True

private theorem indexRoute_next {g : Nat} {s s' : Option Machine.ThreadD} {e : Event}
    (hs : indexRoute L g s) (hn : (Machine.machine P L g).next s e = some s') :
    indexRoute L g s' := by
  cases s with
  | none =>
    change some none = some s' at hn
    cases hn
    trivial
  | some s =>
    change Machine.next P L g s e = some s' at hn
    cases s
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        trivial
      · split at hn
        · rename_i w _
          split_ifs at hn
          · fin_cases w <;> cases hn <;> trivial
          · cases hn
            trivial
        · cases hn
          trivial
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> assumption
    case index d =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        exact hs
      · split_ifs at hn <;> cases hn <;> trivial
      · cases hn
    all_goals
      simp only [Machine.next] at hn
      all_goals repeat' split at hn
      all_goals cases hn
      all_goals trivial

/-- The actual dispatch into index work is restricted to warp seven. -/
theorem warp_of_index_state {d : D} {e : Event} (hX : Consistent L kernel asms mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.index d))) :
    warpOf L g = 7 := by
  have hg := Frame.lt_of_get hX he
  exact (hs.produces (hX.thr g hg)).prefix_induction (fun s _ => indexRoute L g s) trivial
    (fun _ _ _ _ _ hs _ hn => indexRoute_next hs hn) i (some (.index d)) hd

/-- Every actual firing of a followed index state preserves tracking. If a butterfly were the
first dismissal by ordinal, its source lane would still be followed through the earlier
butterflies and could only exit after the row's final block. -/
theorem next_tracked {d : D} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.index d))) :
    Machine.next P L g (.index d) e ≠ some none := by
  intro hn
  have hw := warp_of_index_state hX (hs _ (Frame.lt_of_get hX he)) he hd
  have hi : 5 ≤ i := by
    by_contra! hsmall
    have hx := dispatch_state hpre hX hs hw hsmall he
    rw [hd] at hx
    interval_cases i <;> cases hx
  classical
  have hex : ∃ n, BadOrdinal P L X n := ⟨_, g, i, d, e, hw, hi, he, hd, hn, rfl⟩
  let n := Nat.find hex
  have hmin : ∀ m < n, ¬ BadOrdinal P L X m := fun _ hm => Nat.find_min hex hm
  obtain ⟨g, i, d, e, hw, hi, he, hd, hn, hord⟩ := Nat.find_spec hex
  have hg := Frame.lt_of_get hX he
  have hk := bad_is_shuffle hpre hX hs he hd hn
  obtain ⟨o, hf⟩ := RingEvents.fired_of_trace hX (hs g hg) he hd
  have hinv : Inv P L g d := hf.choose_spec.1.2
  have hb : d.block < blocks P L g := by simpa only [blocks, hinv.len0, hinv.len1] using hinv.block
  apply next_tracked_of_input hpre hX (hs g hg) he hd _ hn
  rcases trace_shuffle_ordinal hpre hX hs hw hi he hk hd with
    ⟨extra, hsite, ho⟩ | ⟨extra, hsite, ho⟩
  · have hnc : n = 3 + 2 * d.block := hord.symm.trans ho.2
    have ho' : X.ShflK (g, i) n := hnc.symm ▸ ho
    have hm := matched_at_minimum hpre hX hs hw hi he ho' (by omega) (by omega) hd
      (shift := 1) (by decide) hmin
    have hkind := quad1_received hpre hX hs hsite he ho' hf hm
    simp only [ValidInput, hsite]
    intro m a b c recv ok h
    rw [hkind] at h
    cases h
    exact ⟨rfl, rfl⟩
  · have hnc : n = 4 + 2 * d.block := hord.symm.trans ho.2
    have ho' : X.ShflK (g, i) n := hnc.symm ▸ ho
    have hm := matched_at_minimum hpre hX hs hw hi he ho' (by omega) (by omega) hd
      (shift := 2) (by decide) hmin
    have hkind := quad2_received hpre hX hs hsite he ho' hf hm
    simp only [ValidInput, hsite]
    intro m a b c recv ok h
    rw [hkind] at h
    cases h
    exact ⟨rfl, rfl⟩

end

/-- The exact prologue or dispatch state of an index lane before entering the body. -/
theorem warp_seven_early_prefix {g i : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hw : warpOf L g = 7) (hi : i < 5) (hlen : i ≤ (X.tr g).length) :
    (∃ s, Frame.stateAt (Machine.code P L) X g i = some (some (.prologue s))) ∨
      Frame.stateAt (Machine.code P L) X g i = some (some .head) := by
  have h := dispatch_state_prefix hpre hX hs hw hi hlen
  interval_cases i
  all_goals first | exact .inl ⟨_, h⟩ | exact .inr h

/-- At a represented index stage the trace has performed exactly its shuffle ordinal. -/
theorem index_prefix_shuffle_count {g i : Nat} {d : D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hw : warpOf L g = 7) (hlen : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.index d))) :
    ((X.tr g).take i).countP Execution.isShfl = shuffleCount d := by
  have hi : 5 ≤ i := by
    by_contra! h
    rcases warp_seven_early_prefix hpre hX hs hw h hlen with ⟨_, hState⟩ | hState
    all_goals rw [hState] at hd; cases hd
  obtain ⟨e, he⟩ : ∃ e, X.get (g, 4) = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega : 4 < (X.tr g).length)⟩
  obtain ⟨hstart, hcount⟩ := shuffle_dispatch_prefix hpre hX hs hw he
  exact shuffleCount_at hstart hcount hi hlen hd

/-- A warp-seven lane can exit only after its two butterflies for every block. -/
theorem warp_seven_exit_count {g i tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hw : warpOf L g = 7) (he : X.get (g, i) = some ⟨tag, .exit⟩) :
    ((X.tr g).take i).countP Execution.isShfl =
      3 + 2 * totalBlocks (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)) := by
  have hi : 5 ≤ i := by
    by_contra! h
    exact dispatch_not_exit hpre hX hs hw h he
  rcases actual_state_or_prior_dismissal hpre hX hs hw hi he (by simp) with
    hBad | ⟨_, _, hNonexit⟩ | ⟨_, hCount⟩
  · obtain ⟨k, d, e, _, _, hk, hstate, hNext⟩ := hBad
    exact (next_tracked hpre hX hs hk hstate hNext).elim
  · exact (hNonexit rfl).elim
  · exact hCount

/-- A followed index lane after dispatch is in its body or has executed every butterfly. -/
theorem warp_seven_tail_body {g : Nat} {q : Machine.ThreadD}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hw : warpOf L g = 7) (hLen : 5 ≤ (X.tr g).length)
    (hq : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some q)) :
    (∃ d, q = .index d ∧ (d.site = .barrier → d.block + 1 =
      totalBlocks (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)))) ∨
    (q = .done ∧ (X.tr g).countP Execution.isShfl =
      3 + 2 * totalBlocks (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g))) := by
  obtain ⟨first, hf⟩ : ∃ e, X.get (g, 4) = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega : 4 < (X.tr g).length)⟩
  have hFrame := frame_after_dispatch hpre hX hs hw hf ((X.tr g).length - 5)
    (by omega : 5 + ((X.tr g).length - 5) ≤ (X.tr g).length)
  rw [show 5 + ((X.tr g).length - 5) = (X.tr g).length by omega, hq] at hFrame
  cases q <;> try exact hFrame.elim
  case index d => exact .inl ⟨d, rfl, hFrame⟩
  case done =>
    exact .inr ⟨rfl, by simpa only [IndexFrame, Ordinal, blocks, List.take_length] using hFrame⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Index
