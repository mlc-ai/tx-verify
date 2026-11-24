-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcCollectiveOperands
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreClosingGate
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix

@[expose] public section

/-! # Loads in a closing lane have issued their actual load waits -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmemLoadWaits

open PTX PTX.Flow Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private theorem fired_wait_at {w : Nat} {d : D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hd : Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 d)))
    (hsite : d.site = .scoreWait ∨ (∃ j, d.site = .rescaleWait j) ∨ ∃ j, d.site = .oWait j)
    (hlen : w < (X.tr g).length) :
    ∃ tag, X.get (g, w) = some ⟨tag, .tc .waitLd⟩ := by
  have he : X.get (g, w) = some (X.tr g)[w] := List.getElem?_eq_getElem hlen
  obtain ⟨o, hf⟩ := (Frame.trace hs hX (Frame.lt_of_get hX he)).fired_at he hd
  have hkind := TcCollectiveSites.waitLd_operands hpre hf hsite
  generalize (X.tr g)[w] = event at he hkind
  cases event
  obtain rfl := hkind
  exact ⟨_, he⟩

private theorem waited_at {w close tag : Nat} {d : D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hclose : X.get (g, close) = some ⟨tag, .bar 12 none .sync⟩)
    (hd : Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 d)))
    (hsite : d.site = .scoreWait ∨ (∃ j, d.site = .rescaleWait j) ∨ ∃ j, d.site = .oWait j)
    (hlen : w ≤ (X.tr g).length) :
    ∃ wtag, X.get (g, w) = some ⟨wtag, .tc .waitLd⟩ ∧
      d.site ≠ .everyone ∧ d.site ≠ .exit := by
  have hAllowed : d.site ≠ .everyone ∧ d.site ≠ .exit := by
    rcases hsite with h | ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  have hw := ScoreClosingGate.wg0_before_closing hpre hX hs ht hclose hd
    hAllowed.1 hAllowed.2 hlen
  have hwLen : w < (X.tr g).length := hw.trans (PTX.len_of_get hclose)
  obtain ⟨tag', he⟩ := fired_wait_at hpre hX hs hd hsite hwLen
  exact ⟨tag', he, hAllowed⟩

private theorem score_next {i tag arm part : Nat} {d : D} {address : Nat}
    {words : List Value} {shape : TcShape}
    (ha : arm < 2) (hp : part < 2)
    (he : X.get (g, i) = some ⟨tag, .tc (.ld address words shape)⟩)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .scoreLoad ⟨arm, ha⟩ ⟨part, hp⟩) (harm : arm = Wg0.arm L g) :
    Frame.stateAt (Machine.code P L) X g (i + 1) = some (some (.wg0
      {loadScores d (arm == part) words with site := afterScoreSite ⟨arm, ha⟩ ⟨part, hp⟩})) := by
  rw [Frame.stateAt_succ he, hd, Option.bind_some]
  change Machine.next P L g (.wg0 d) ⟨tag, .tc (.ld address words shape)⟩ = _
  simp [Machine.next, Wg0.next, Wg0.nextSite, hsite, harm]
  rfl

/-- A later followed state outside the loading sequence certifies the actual score wait. -/
theorem score_wait_before_later_state {i later : Nat} {d : D} {arm part : Fin 2}
    {e : Event} {other : Machine.ThreadD} {address : Nat} {words : List Value} {shape : TcShape}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hload : X.TLd (g, i) address words shape)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .scoreLoad arm part) (hlt : i < later)
    (hLaterGet : X.get (g, later) = some e)
    (hLater : Frame.stateAt (Machine.code P L) X g later = some (some other))
    (hOther : ∀ q, other = .wg0 q → ¬ (q.site = .scoreWait ∨ ∃ a k, q.site = .scoreLoad a k)) :
    ∃ w wtag q, i < w ∧ X.get (g, w) = some ⟨wtag, .tc .waitLd⟩ ∧
      Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 q)) ∧
      q.site = .scoreWait ∧ q.block = d.block := by
  obtain ⟨tag, he⟩ := hload
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hd
  obtain ⟨part', ha⟩ := (show Inv P L g d from hInv).armSite ⟨arm, part, hsite⟩
  have hArm := congrArg Fin.val (Site.scoreLoad.inj (hsite.symm.trans ha)).1
  have hNext := score_next arm.isLt part.isLt he hd hsite hArm
  have hb {q : D} (h : q.site = .scoreWait ∨ ∃ a k, q.site = .scoreLoad a k)
      {w : Nat} (hwle : w ≤ later)
      (hq : Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 q))) : w < later := by
    by_contra! hn
    have hEq : w = later := by omega
    subst w
    rw [hq] at hLater
    have hD := (Option.some.inj (Option.some.inj hLater)).symm
    exact hOther q hD h
  have hSameBlock (q : D) (own : Bool) (vals : List Value) :
      (loadScores q own vals).block = q.block := by
    unfold loadScores
    split <;> rfl
  have done {w : Nat} {q : D} (hw : i < w) (hwle : w ≤ later)
      (hq : Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 q)))
      (hqSite : q.site = .scoreWait) (hBlock : q.block = d.block) :
      ∃ w wtag q, i < w ∧ X.get (g, w) = some ⟨wtag, .tc .waitLd⟩ ∧
        Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 q)) ∧
        q.site = .scoreWait ∧ q.block = d.block := by
    have hlen := (hb (.inl hqSite) hwle hq).trans (PTX.len_of_get hLaterGet)
    obtain ⟨wtag, hwGet⟩ := fired_wait_at hpre hX hs hq (.inl hqSite) hlen
    exact ⟨w, wtag, q, hw, hwGet, hq, hqSite, hBlock⟩
  fin_cases part
  case «1» =>
    apply done (Nat.lt_succ_self i) (by omega) hNext rfl
    exact hSameBlock _ _ _
  case «0» =>
    let q := {loadScores d (arm.val == 0) words with site := .scoreLoad arm 1}
    have hq : Frame.stateAt (Machine.code P L) X g (i + 1) = some (some (.wg0 q)) := hNext
    have hqi := hb (.inr ⟨arm, 1, rfl⟩) (by omega) hq
    have hqLen := hqi.trans (PTX.len_of_get hLaterGet)
    have hget : X.get (g, i + 1) = some (X.tr g)[i + 1] := List.getElem?_eq_getElem hqLen
    obtain ⟨q', r, hq', hr, hStep⟩ := FollowedPrefix.step_at
      hLater hqi hget
    have hrLive : Machine.next P L g (.wg0 q) (X.tr g)[i + 1] = some (some r) := by
      rw [hq] at hq'
      obtain rfl := Option.some.inj (Option.some.inj hq')
      exact hStep
    generalize hEvent : (X.tr g)[i + 1] = event at hget hrLive
    obtain ⟨evtag, kind⟩ := event
    have hKind : ∃ a vs sh, kind = .tc (.ld a vs sh) := by
      cases kind <;> simp [Machine.next, Wg0.next, Wg0.nextSite, q] at hrLive
      case tc k =>
        cases k <;> simp at hrLive
        case ld a vs sh => exact ⟨a, vs, sh, rfl⟩
    obtain ⟨address', words', shape', rfl⟩ := hKind
    have hNext' := score_next arm.isLt (by decide : 1 < 2) hget hq rfl hArm
    apply done (show i < (i + 1) + 1 by omega) (by omega) hNext' rfl
    exact (hSameBlock _ _ _).trans (hSameBlock _ _ _)

/-- A later softmax state outside the matched wait proves the wait of a rescale load occurred. -/
theorem rescale_wait_before_later_state {i later : Nat} {d q : D} {tile : Fin 4}
    {e : Event} {address : Nat} {words : List Value} {shape : TcShape}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hload : X.TLd (g, i) address words shape)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleLoad tile) (hlt : i < later)
    (hLaterGet : X.get (g, later) = some e)
    (hLater : Frame.stateAt (Machine.code P L) X g later = some (some (.wg0 q)))
    (hOther : q.site ≠ .rescaleWait tile) :
    ∃ tag, i + 1 < later ∧ X.get (g, i + 1) = some ⟨tag, .tc .waitLd⟩ := by
  obtain ⟨tag, he⟩ := hload
  let wait := {d with site := .rescaleWait tile, rescaleWords := words}
  have hWait : Frame.stateAt (Machine.code P L) X g (i + 1) = some (some (.wg0 wait)) := by
    rw [Frame.stateAt_succ he, hd, Option.bind_some]
    change Machine.next P L g (.wg0 d) _ = _
    simp [Machine.next, Wg0.next, Wg0.nextSite, hsite, wait]
    rfl
  have hBefore : i + 1 < later := by
    by_contra! h
    have heq : later = i + 1 := by omega
    rw [heq, hWait] at hLater
    have hSiteEq := congrArg D.site (Machine.ThreadD.wg0.inj
      (Option.some.inj (Option.some.inj hLater)))
    exact hOther hSiteEq.symm
  obtain ⟨wtag, hw⟩ := fired_wait_at hpre hX hs hWait (.inr (.inl ⟨tile, rfl⟩))
    (hBefore.trans (PTX.len_of_get hLaterGet))
  exact ⟨wtag, hBefore, hw⟩

/-- Once a lane has arrived at the closing barrier, its earlier loads have matching waits. -/
theorem load_wait_of_closing {i close tag address : Nat} {words : List Value} {shape : TcShape}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hclose : X.get (g, close) = some ⟨tag, .bar 12 none .sync⟩)
    (hi : X.TLd (g, i) address words shape) :
    ∃ w wtag d, i < w ∧ X.get (g, w) = some ⟨wtag, .tc .waitLd⟩ ∧
      Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 d)) ∧
      d.site ≠ .everyone ∧ d.site ≠ .exit := by
  obtain ⟨it, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hd, rfl, hsite⟩ :=
    TcCollectiveSites.load_fields hpre hX (hs g hg).machine ht ⟨it, he⟩
  have hiLen := PTX.len_of_get he
  have finish {w : Nat} {q : D} (hw : i < w) (hlen : w ≤ (X.tr g).length)
      (hq : Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 q)))
      (hs' : q.site = .scoreWait ∨ (∃ k, q.site = .rescaleWait k) ∨ ∃ k, q.site = .oWait k) :
      ∃ w wtag d, i < w ∧ X.get (g, w) = some ⟨wtag, .tc .waitLd⟩ ∧
        Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 d)) ∧
        d.site ≠ .everyone ∧ d.site ≠ .exit := by
    obtain ⟨wtag, hwait, hAllowed⟩ := waited_at hpre hX hs ht hclose hq hs' hlen
    exact ⟨w, wtag, q, hw, hwait, hq, hAllowed⟩
  rcases hsite with ⟨arm, part, hsite, _, _⟩ | ⟨tile, hsite, _, _⟩
  · have hBefore := ScoreClosingGate.wg0_before_closing hpre hX hs ht hclose hd
      (by simp [hsite]) (by simp [hsite]) hiLen.le
    obtain ⟨other, hOther, hClose, _⟩ := ScoreClosingGate.closing_at hpre hX hs ht hclose
    have hExcluded (q : D) (hEq : other = .wg0 q) :
        ¬ (q.site = .scoreWait ∨ ∃ a k, q.site = .scoreLoad a k) := by
      subst other
      change q.site = .everyone at hClose
      simp [hClose]
    obtain ⟨w, wtag, q, hw, hWait, hq, hqSite, _⟩ := score_wait_before_later_state
      hpre hX hs ⟨it, he⟩ hd hsite hBefore hclose hOther hExcluded
    exact ⟨w, wtag, q, hw, hWait, hq, by simp [hqSite], by simp [hqSite]⟩
  · rcases hsite with hsite | hsite
    · let q := {d with site := .rescaleWait tile, rescaleWords := words}
      have hq : Frame.stateAt (Machine.code P L) X g (i + 1) = some (some (.wg0 q)) := by
        rw [Frame.stateAt_succ he, hd, Option.bind_some]
        change Machine.next P L g (.wg0 d) _ = _
        simp [Machine.next, Wg0.next, Wg0.nextSite, hsite, q]
        rfl
      exact finish (Nat.lt_succ_self i) hiLen hq (.inr (.inl ⟨tile, rfl⟩))
    · let q := {loadOutput L g d tile words with site := .oWait tile}
      have hq : Frame.stateAt (Machine.code P L) X g (i + 1) = some (some (.wg0 q)) := by
        rw [Frame.stateAt_succ he, hd, Option.bind_some]
        change Machine.next P L g (.wg0 d) _ = _
        simp [Machine.next, Wg0.next, Wg0.nextSite, hsite, q]
        rfl
      exact finish (Nat.lt_succ_self i) hiLen hq (.inr (.inr ⟨tile, rfl⟩))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmemLoadWaits
