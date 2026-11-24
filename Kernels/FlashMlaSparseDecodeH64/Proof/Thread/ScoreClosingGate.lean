-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerTrace
public import Lemmas.Kernel.Frame
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Lemmas.Step.CtaBarNamed
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreReleaseTrace

@[expose] public section

/-! # The final CTA barrier's participants and ordinal -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ScoreClosingGate

open PTX PTX.Flow PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The remaining roles use the same closing barrier as the softmax lane. -/
def ClosingSite : Machine.ThreadD → Prop
  | .wg0 d => d.site = .everyone
  | .mma d => d.site = .outBar
  | .tma d => d.site = .barrier
  | .index d => d.site = .barrier
  | .idle s => s = .sync
  | .wg2 d => d.site = .barrier
  | _ => False

private theorem close_template {t : TState} {id count : Nat} (hpre : Pre P L mem0)
    (hid : t.regs id = some (b32 12)) (hc : t.regs count = some (b32 384)) :
    eventTmpl Assumptions.all L g t (.barSyncN (.reg id) (.reg count) false) =
      .bar 12 (PTX.next t) none .sync := by
  have hi := readBits_b32 (L := L) (g := g) hid (by decide)
  have hcnt := readBits_b32 (L := L) (g := g) hc (by decide)
  simp [eventTmpl, barTmpl, hi, hcnt, hpre.block]

private theorem wg0_fired_closing {d : Wg0.D} {t : Nat} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hsite : d.site = .everyone)
    (hf : (Machine.machine P L t).Fired (some (.wg0 d)) e o) :
    e.kind = .bar 12 none .sync := by
  have hc : kernel.code[d.site.pc]? =
      some ⟨none, .barSyncN (.reg 2425) (.reg 2426) false⟩ := by
    rw [hsite]
    exact Flow.code_1835
  obtain ⟨_, hat, hfire⟩ := RingGateEvents.fired_at_code hf hc
  rw [Wg0.event_everyone hpre hat hsite] at hfire
  exact congrArg Event.kind hfire.1

/-- Every role’s closing site fires the same full-CTA synchronization. -/
theorem closing_kind {d : Machine.ThreadD} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hf : (Machine.machine P L g).Fired (some d) e o)
    (hs : ClosingSite d) : e.kind = .bar 12 none .sync := by
  cases d
  case wg0 d => exact wg0_fired_closing hpre hs hf
  case mma d =>
    have hp : d.site.pc = 2160 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
      change kernel.code[d.site.pc]? = some _
      simpa only [hp] using Flow.code_bar_11)
    change (Wg1Mma.code P L g).AtD d t at hat
    have hid : t.regs 918 = some (b32 12) :=
      Wg1Mma.atD_reg hat (r := 918) hp (by decide +kernel)
    have hcnt : t.regs 919 = some (b32 384) :=
      Wg1Mma.atD_reg hat (r := 919) hp (by decide +kernel)
    rw [close_template hpre hid hcnt] at hfire
    exact congrArg Event.kind hfire.1
  case tma d =>
    have hp : d.site.pc = 2330 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
      change kernel.code[d.site.pc]? = some _
      simpa only [hp] using Flow.code_bar_12)
    change (Wg1Tma.code P L g).AtD d t at hat
    have hid : t.regs 790 = some (b32 12) :=
      Wg1Tma.atD_regAt hat hp (by decide +kernel)
    have hcnt : t.regs 791 = some (b32 384) :=
      Wg1Tma.atD_regAt hat hp (by decide +kernel)
    rw [close_template hpre hid hcnt] at hfire
    exact congrArg Event.kind hfire.1
  case index d =>
    have hp : d.site.pc = 2585 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
      change kernel.code[d.site.pc]? = some _
      simpa only [hp] using Flow.code_bar_13)
    change (Wg1Index.code P L g).AtD d t at hat
    have hid : t.regs 659 = some (b32 12) :=
      Wg1Index.AtD.reg hat (by rw [hp]; decide +kernel)
    have hcnt : t.regs 660 = some (b32 384) :=
      Wg1Index.AtD.reg hat (by rw [hp]; decide +kernel)
    rw [close_template hpre hid hcnt] at hfire
    exact congrArg Event.kind hfire.1
  case idle s =>
    change s = .sync at hs
    subst s
    obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf Flow.code_bar_14
    rw [Thread.event_sync hat hpre.block] at hfire
    exact congrArg Event.kind hfire.1
  case wg2 d =>
    have hp : d.site.pc = 3610 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
      change kernel.code[d.site.pc]? = some _
      simpa only [hp] using Flow.code_bar_15)
    rw [Wg2.event_barrier hpre hat hp] at hfire
    exact congrArg Event.kind hfire.1
  all_goals exact hs.elim

/-- The audited closing site is the only source of barrier 12 for each role. -/
theorem closing_fired
    {d : Machine.ThreadD} {e : Event} {o : Option TState} {count : Option Nat} {mode : BarMode}
    (hpre : Pre P L mem0) (hf : (Machine.machine P L g).Fired (some d) e o)
    (hk : e.kind = .bar 12 count mode) :
    ClosingSite d ∧ count = none ∧ mode = .sync := by
  have hs := RingGateEvents.bar_site hf hk
  cases d
  case prologue d =>
    change d = .barrier at hs
    subst d
    obtain ⟨_, _, hfire⟩ := RingGateEvents.fired_at_code hf Flow.code_bar_0
    have he := (Kind.bar.inj (hk.symm.trans (congrArg Event.kind hfire.1))).1
    change (12 : Nat) = 0 at he
    cases he
  case wg0 d =>
    by_cases hc : d.site = .everyone
    · have hbar := wg0_fired_closing hpre hc hf
      exact ⟨hc, (Kind.bar.inj (hk.symm.trans hbar)).2⟩
    · rcases hs with hs | hs | hs | hs | hs | hs | ⟨j, hs⟩
      · have hp := Wg0BarrierTrace.bar9_kind hpre hf (by rw [hs]; trivial)
        cases (Kind.bar.inj (hk.symm.trans hp)).1
      · have hp := Wg0PeerTrace.pair_kind hpre hf hs
        have h := (Kind.bar.inj (hk.symm.trans hp)).1
        omega
      · have hp := Wg0BarrierTrace.bar9_kind hpre hf (by rw [hs]; trivial)
        cases (Kind.bar.inj (hk.symm.trans hp)).1
      · have hp := Wg0BarrierTrace.bar9_kind hpre hf (by rw [hs]; trivial)
        cases (Kind.bar.inj (hk.symm.trans hp)).1
      · have hp := Wg0BarrierTrace.bar9_kind hpre hf (by rw [hs]; trivial)
        cases (Kind.bar.inj (hk.symm.trans hp)).1
      · exact (hc hs).elim
      · have hp := Wg0BarrierTrace.bar9_kind hpre hf (by rw [hs]; trivial)
        cases (Kind.bar.inj (hk.symm.trans hp)).1
  case mma d => exact ⟨hs, (Kind.bar.inj (hk.symm.trans (closing_kind hpre hf hs))).2⟩
  case tma d => exact ⟨hs, (Kind.bar.inj (hk.symm.trans (closing_kind hpre hf hs))).2⟩
  case index d => exact ⟨hs, (Kind.bar.inj (hk.symm.trans (closing_kind hpre hf hs))).2⟩
  case idle d => exact ⟨hs, (Kind.bar.inj (hk.symm.trans (closing_kind hpre hf hs))).2⟩
  case wg2 d => exact ⟨hs, (Kind.bar.inj (hk.symm.trans (closing_kind hpre hf hs))).2⟩
  all_goals exact hs.elim

/-- Any actual arrival at the closing barrier uses full CTA synchronization. -/
theorem closing_at
    {i tag : Nat} {count : Option Nat} {mode : BarMode}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some ⟨tag, .bar 12 count mode⟩) :
    ∃ d, Frame.stateAt (Machine.code P L) X g i = some (some d) ∧
      ClosingSite d ∧ count = none ∧ mode = .sync := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, _, hd, hf⟩ := RingSourceSites.fired_from_trace hX (hs g hg).machine ht he (by simp)
  exact ⟨d, hd, closing_fired hpre hf rfl⟩

private def Closed : Option (Option Machine.ThreadD) → Prop
  | some (some (.wg0 d)) => d.site = .exit
  | some (some (.mma d)) => d.site = .exit
  | some (some (.tma d)) => d.site = .exit
  | some (some (.idle s)) => s = .exit
  | some (some .done) | some none | none => True
  | _ => False

private theorem closed_on_next {d : Machine.ThreadD} {e : Event}
    (hc : ClosingSite d) (he : e.kind = .bar 12 none .sync) :
    Closed (Machine.next P L g d e) := by
  cases d
  case wg0 d =>
    change d.site = .everyone at hc
    unfold Machine.next Wg0.next Wg0.nextSite
    simp only [hc, he]
    split_ifs <;> trivial
  case mma d =>
    change d.site = .outBar at hc
    simp [Machine.next, Wg1Mma.next, hc, Closed]
  case tma d =>
    change d.site = .barrier at hc
    simp [Machine.next, Wg1Tma.next, hc, he, Closed]
  case index d =>
    change d.site = .barrier at hc
    simp [Machine.next, Wg1Index.next, Wg1Index.nextSite, hc, he, Closed]
  case idle d =>
    change d = .sync at hc
    subst d
    simp [Machine.next, Thread.next, he, Closed]
  case wg2 d =>
    change d.site = .barrier at hc
    simp [Machine.next, Wg2.next, Wg2.nextSite, hc, he, Closed]
  all_goals exact hc.elim

private theorem closed_next {d : Machine.ThreadD} {e : Event}
    (hc : Closed (some (some d))) : Closed (Machine.next P L g d e) := by
  cases d
  case wg0 d =>
    change d.site = .exit at hc
    cases hk : e.kind <;> simp [Machine.next, Wg0.next, Wg0.nextSite, hc, hk, Closed]
    case tc k => cases k <;> trivial
  case mma d =>
    change d.site = .exit at hc
    simp [Machine.next, Wg1Mma.next, hc, Closed]
  case tma d =>
    change d.site = .exit at hc
    cases hk : e.kind <;> simp [Machine.next, Wg1Tma.next, hc, hk, Closed]
  case idle d =>
    change d = .exit at hc
    subst d
    simp [Machine.next, Thread.next, Closed]
  case done => trivial
  all_goals exact hc.elim

private theorem closed_mono {i j : Nat} (hij : i ≤ j) (hj : j ≤ (X.tr g).length)
    (hclosed : Closed (Frame.stateAt (Machine.code P L) X g i)) :
    Closed (Frame.stateAt (Machine.code P L) X g j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction n with
  | zero => exact hclosed
  | succ n ih =>
    have hlt : i + n < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[i + n]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hprev := ih hlt.le
    rw [Nat.add_succ, Frame.stateAt_succ he]
    cases hh : Frame.stateAt (Machine.code P L) X g (i + n) with
    | none => trivial
    | some s =>
      cases s with
      | none => trivial
      | some d =>
        rw [hh] at hprev
        exact closed_next hprev

private theorem closed_after_closing {i j k : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some ⟨k, .bar 12 none .sync⟩)
    (hij : i < j) (hj : j ≤ (X.tr g).length) :
    Closed (Frame.stateAt (Machine.code P L) X g j) := by
  obtain ⟨d, hd, hc, _, _⟩ := closing_at hpre hX hs ht he
  refine closed_mono hij hj ?_
  rw [Frame.stateAt_succ he, hd]
  exact closed_on_next hc rfl

/-- Every later event of a lane that has passed the closing barrier is outside named barriers. -/
theorem no_bar_after_closing {i j tag : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hClose : X.get (g, i) = some ⟨tag, .bar 12 none .sync⟩)
    (he : X.get (g, j) = some e) (hBefore : i < j)
    {id : Nat} {count : Option Nat} {mode : BarMode} (hBar : e.kind = .bar id count mode) :
    False := by
  have hClosed := closed_after_closing hpre hX hs ht hClose hBefore (PTX.len_of_get he).le
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, _, hd, hf⟩ := RingSourceSites.fired_from_trace hX (hs g hg).machine ht he (by
    intro fault h
    rw [hBar] at h
    cases h)
  rw [hd] at hClosed
  have hSite := RingGateEvents.bar_site hf hBar
  cases d
  case wg0 d =>
    change d.site = .exit at hClosed
    simp [RingGateEvents.BarSite, hClosed] at hSite
  case mma d =>
    change d.site = .exit at hClosed
    simp [RingGateEvents.BarSite, hClosed] at hSite
  case tma d =>
    change d.site = .exit at hClosed
    simp [RingGateEvents.BarSite, hClosed] at hSite
  case idle s =>
    change s = .exit at hClosed
    simp [RingGateEvents.BarSite, hClosed] at hSite
  case done => exact hSite.elim
  all_goals exact hClosed.elim

/-- A softmax state before the exit cannot follow its own closing barrier. -/
theorem wg0_before_closing {j w tag : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, j) = some ⟨tag, .bar 12 none .sync⟩)
    (hd : Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 d)))
    (hNotClosing : d.site ≠ .everyone) (hNotExit : d.site ≠ .exit)
    (hlen : w ≤ (X.tr g).length) : w < j := by
  obtain ⟨s, hs', hc, _, _⟩ := closing_at hpre hX hs ht he
  by_contra hn
  have hne : w ≠ j := by
    rintro rfl
    rw [hd] at hs'
    cases hs'
    change d.site = .everyone at hc
    exact hNotClosing hc
  have hclosed := closed_after_closing hpre hX hs ht he (by omega) hlen
  rw [hd] at hclosed
  change d.site = .exit at hclosed
  exact hNotExit hclosed

/-- An actual closing barrier has no earlier arrival of the same barrier in its lane. -/
theorem closing_ordinal {i tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some ⟨tag, .bar 12 none .sync⟩) :
    ((X.tr g).take i).countP (Execution.isBarId 12) = 0 := by
  by_contra hn
  obtain ⟨j, e, hget, hevent, _⟩ :=
    PTX.NamedBar.exists_ordinal (Execution.isBarId 12) ((X.tr g).take i)
      (r := 0) (by omega)
  have hj : j < i := by
    have := (List.getElem?_eq_some_iff.mp hget).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hj] at hget
  obtain ⟨tag', kind⟩ := e
  cases kind <;> simp only [Execution.isBarId, Bool.false_eq_true] at hevent
  case bar id count mode =>
    have hid : id = 12 := of_decide_eq_true hevent
    subst id
    obtain ⟨_, _, _, rfl, rfl⟩ := closing_at hpre hX hs ht hget
    have hh := closed_after_closing hpre hX hs ht hget hj (PTX.len_of_get he).le
    obtain ⟨s, hst, hc, _, _⟩ := closing_at hpre hX hs ht he
    rw [hst] at hh
    cases s <;> simp only [ClosingSite, Closed] at hh hc
    all_goals rw [hc] at hh
    all_goals cases hh

private def returnsOp : Op → Bool
  | .ret | .exit => true
  | _ => false

set_option maxRecDepth 100000 in
private theorem sole_ret : OpPcsFast kernel.code returnsOp [3611] = true := by
  decide +kernel

private theorem wg0_site_not_ret (s : Wg0.Site) : s.pc ≠ 3611 := by
  cases s
  all_goals first
    | decide
    | (rename_i a; revert a; decide)
    | (rename_i a b; revert a b; decide)

private theorem wg0_not_exit {d : Wg0.D} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o) (hk : e.kind = .exit) : False := by
  obtain ⟨t, _, hfire⟩ := hf
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hfire
  cases hc : kernel.code[d.site.pc]? with
  | none =>
    rw [hc] at hfire
    rw [congrArg Event.kind hfire.1] at hk
    cases hk
  | some ins =>
    rw [hc] at hfire
    have hop : returnsOp ins.op = true := by
      rcases fires_exit_op hfire hk with h | h <;> rw [h] <;> rfl
    have hm := OpPcsFast.mem sole_ret hc hop
    exact wg0_site_not_ret d.site (List.mem_singleton.mp hm)

/-- A followed softmax lane before exit can return only after its own closing arrival. -/
theorem closing_of_exited_wg0_lane {w j et : Nat} {d : Wg0.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hstate : Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 d)))
    (hNotExit : d.site ≠ .exit)
    (hw : X.get (g, w) = some e)
    (hexit : X.get (g, j) = some ⟨et, .exit⟩) :
    ∃ n tag, X.get (g, n) = some ⟨tag, .bar 12 none .sync⟩ := by
  classical
  by_contra hn
  have hg := Frame.lt_of_get hX hexit
  have hlast := Execution.exit_last hX hg hexit
  have hlen := PTX.len_of_get hw
  have hle : w ≤ j := by simp only at hlen hlast; omega
  obtain ⟨last, _, hlastState, _⟩ :=
    RingSourceSites.fired_from_trace hX (hs g hg).machine ht hexit (by simp)
  have hrole (n : Nat) (hstart : w ≤ n) (hend : n ≤ j) :
      ∃ s, Frame.stateAt (Machine.code P L) X g n = some (some (.wg0 s)) ∧
        s.site ≠ .exit := by
    induction n with
    | zero =>
      have hw0 : w = 0 := by omega
      subst w
      exact ⟨d, hstate, hNotExit⟩
    | succ n ih =>
      rcases Nat.eq_or_lt_of_le hstart with rfl | hlt
      · exact ⟨d, hstate, hNotExit⟩
      obtain ⟨s, hst, hns⟩ := ih (by omega) (by omega)
      have hj : n < (X.tr g).length := by
        have := PTX.len_of_get hexit
        simp only at this
        omega
      obtain ⟨e, he⟩ : ∃ e, X.get (g, n) = some e := ⟨_, List.getElem?_eq_getElem hj⟩
      obtain ⟨_, hf⟩ := (Frame.trace hs hX hg).fired_at he hst
      have hone : s.site ≠ .everyone := by
        intro hq
        have hb := wg0_fired_closing hpre hq hf
        have hbar : X.get (g, n) = some ⟨e.pc, .bar 12 none .sync⟩ := by
          cases e
          exact he.trans (congrArg some (congrArg (Event.mk _) hb))
        exact hn ⟨n, _, hbar⟩
      obtain ⟨next, hnext⟩ := FollowedPrefix.state_at hlastState hend
      rw [Frame.stateAt_succ he, hst, Option.bind_some] at hnext
      change Machine.next P L g (.wg0 s) e = some (some next) at hnext
      have hfull := hnext
      simp only [Machine.next] at hnext
      split at hnext
      · rename_i q hq
        cases hnext
        refine ⟨q, ?_, ?_⟩
        · rw [Frame.stateAt_succ he, hst]
          exact hfull
        · intro hqExit
          obtain ⟨other, heq, hEveryone⟩ := ScoreReleaseTrace.exit_predecessor hfull hqExit
          exact hone ((Machine.ThreadD.wg0.inj heq) ▸ hEveryone)
      · simp [hns, hone] at hnext
        cases hnext
      · cases hnext
  obtain ⟨s, hst, _⟩ := hrole j hle le_rfl
  obtain ⟨_, hf⟩ := (Frame.trace hs hX hg).fired_at hexit hst
  exact wg0_not_exit hf rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ScoreClosingGate
