-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Lemmas.Flow.NotArrive
public import Lemmas.Flow.WaitLoopPcs
import Lemmas.Flow.NotBulk

import Lemmas.Flow.WaitAcquire

@[expose] public section

/-! # Decoded arrival and poll sites of the composed thread -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingSourceSites

open PTX PTX.Flow

local macro "decide_site" : tactic =>
  `(tactic| first
    | (intro _; exact ⟨false, rfl⟩)
    | (intro _; exact ⟨true, rfl⟩)
    | (intro _; rename_i b; exact ⟨b, rfl⟩)
    | decide
    | (rename_i a; revert a; decide)
    | (rename_i a b; revert a b; decide)
    | (rename_i a b c; revert a b c; decide))

private theorem pollOp_ne {op : Op} (h : pollOp op = false) :
    ∀ (dst base : Nat) (off : Int) (par : Opnd) (acq : Bool) (sc : MbarScope),
      op ≠ .mbarWait dst base off par acq sc := by
  intro dst base off par acq sc he
  subst op
  simp [pollOp] at h

set_option maxRecDepth 100000 in
private theorem arrive_sites : OpPcsFast kernel.code arriveOp Flow.mbarArrive.toList = true := by
  decide +kernel

/-- Every actual ordinary barrier arrival has a site in the decoded arrival list. -/
theorem actual_arrive_pc {L : Launch} {mem0 : Mem0} {X : Execution} {i : EvId}
    {e : Event} {m : Loc} {tx count : Nat} {rel : Bool} {scope : MbarScope}
    (hX : Consistent L kernel Assumptions.all mem0 X) (he : X.get i = some e)
    (hKind : e.kind = .arrive m tx count rel scope) : e.pc ∈ Flow.mbarArrive.toList := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, _, hc, hf⟩
  · rw [hf] at hKind
    cases hKind
  · cases hop : arriveOp ins.op
    · exact (fires_notArrive (eventTmpl_notArrive (arriveOp_ne hop)) hf
        m tx count rel scope hKind).elim
    · exact OpPcsFast.mem arrive_sites hc hop

section
variable {P : Params} {L : Launch} {g : Nat} {d : Machine.ThreadD} {e : Event} {o : Option TState}

private theorem arrive_pc_of_fired {m : Loc} {tx count : Nat} {rel : Bool} {scope : MbarScope}
    (hf : (Machine.machine P L g).Fired (some d) e o) (hk : e.kind = .arrive m tx count rel scope) :
    (Machine.code P L g).pc d ∈ Flow.mbarArrive.toList := by
  obtain ⟨t, _, hf⟩ := hf
  change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  cases hc : kernel.code[(Machine.code P L g).pc d]? with
  | none =>
    rw [hc] at hf
    obtain ⟨he, _⟩ := hf
    rw [he] at hk
    contradiction
  | some ins =>
    rw [hc] at hf
    cases hop : arriveOp ins.op
    · exact (fires_notArrive (eventTmpl_notArrive (arriveOp_ne hop)) hf
        m tx count rel scope hk).elim
    · exact OpPcsFast.mem arrive_sites hc hop

/-- The role sites at which a thread can issue a barrier arrival. -/
def ArriveSite : Machine.ThreadD → Prop
  | .wg0 q => q.site = .lastStore ∨ q.site = .validFree ∨ q.site = .soReady
  | .mma q => q.site = .qArrive
  | .tma q => q.site = .rawReady ∨ q.site = .coordFree
  | .index q => ∃ extra, q.site = .ready extra
  | .wg2 q => q.site = .ready ∨ q.site = .free
  | _ => False

/-- The frozen kernel and the followed role exhaust all barrier arrival sites. -/
theorem arrive_site {m : Loc} {tx count : Nat} {rel : Bool} {scope : MbarScope}
    (hf : (Machine.machine P L g).Fired (some d) e o) (hk : e.kind = .arrive m tx count rel scope) :
    ArriveSite d := by
  have hm := arrive_pc_of_fired hf hk
  clear * - d hm
  cases d
  case prologue q =>
    change False
    change q.pc ∈ _ at hm
    cases q <;> revert hm <;> decide_site
  case wg0 q =>
    change q.site.pc ∈ _ at hm
    simp only [ArriveSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case mma q =>
    change q.site.pc ∈ _ at hm
    simp only [ArriveSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case tma q =>
    change q.site.pc ∈ _ at hm
    simp only [ArriveSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case index q =>
    change q.site.pc ∈ _ at hm
    simp only [ArriveSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case wg2 q =>
    change q.site.pc ∈ _ at hm
    simp only [ArriveSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case idle q =>
    change False
    change q.pc ∈ _ at hm
    cases q <;> revert hm <;> decide
  case head =>
    change 1843 ∈ _ at hm
    exact (by decide : 1843 ∉ Flow.mbarArrive.toList) hm
  case done =>
    change 3611 ∈ _ at hm
    exact (by decide : 3611 ∉ Flow.mbarArrive.toList) hm

set_option maxRecDepth 100000 in
private theorem poll_sites : OpPcsFast kernel.code pollOp Flow.mbarWait.toList = true := by
  decide +kernel

/-- Every actual mbarrier poll has a site in the frozen poll list. -/
theorem actual_wait_pc {L : Launch} {mem0 : Mem0} {X : Execution} {i : EvId}
    {e : Event} {m : Loc} {p : Nat} {ok acq : Bool} {scope : MbarScope}
    (hX : Consistent L kernel Assumptions.all mem0 X) (he : X.get i = some e)
    (hk : e.kind = .wait m p ok acq scope) : e.pc ∈ Flow.mbarWait.toList := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, _, hc, hf⟩
  · rw [hf] at hk
    cases hk
  · cases hop : pollOp ins.op
    · exact (fires_notWait (eventTmpl_notWait (pollOp_ne hop)) hf m p ok acq scope hk).elim
    · exact OpPcsFast.mem poll_sites hc hop

set_option maxRecDepth 100000 in
private theorem wait_flags_audit : kernel.code.all (fun ins =>
    match ins.op with
    | .mbarWait _ _ _ _ acq sc => acq && decide (sc = .cta)
    | _ => true) = true := by decide +kernel

/-- The frozen kernel's mbarrier polls are CTA-scope acquires in the actual execution. -/
theorem actual_wait_acquire {L : Launch} {mem0 : Mem0} {X : Execution} {i : EvId}
    {e : Event} {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hX : Consistent L kernel Assumptions.all mem0 X) (he : X.get i = some e)
    (hk : e.kind = .wait m p ok acq sc) : acq = true ∧ sc = .cta := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, _, hc, hf⟩
  · rw [hf] at hk
    cases hk
  · obtain ⟨dst, base, off, par, sc0, hop, _⟩ := fires_wait_flags hf hk
    have hCheck := List.all_eq_true.mp wait_flags_audit ins (List.mem_of_getElem? hc)
    simp only [hop, Bool.and_eq_true, decide_eq_true_eq] at hCheck
    obtain ⟨rfl, rfl⟩ := hCheck
    refine ⟨rfl, ?_⟩
    rw [hop] at hf
    have hScope : Assumptions.all.any (·.clusterScopeMbar t.pc) = false := rfl
    simp only [eventTmpl, widenMbarScope, hScope, Bool.false_eq_true, ↓reduceIte, tmaTmpl,
      bind, Except.bind, pure, Except.pure] at hf
    cases hm : mbarLoc L i.1 t base off with
    | error f =>
      simp only [hm, ofExec, Fires] at hf
      rw [hf.1] at hk
      cases hk
    | ok loc =>
      cases hq : readBits L i.1 t 32 par with
      | error f =>
        simp only [hm, hq, ofExec, Fires] at hf
        rw [hf.1] at hk
        cases hk
      | ok q =>
        simp only [hm, hq, ofExec, Fires] at hf
        obtain ⟨_, hSame, _⟩ := hf
        exact (Kind.wait.inj (hk.symm.trans (congrArg Event.kind hSame))).2.2.2.2

private theorem poll_pc_of_fired {m : Loc} {parity : Nat} {ok acq : Bool} {scope : MbarScope}
    (hf : (Machine.machine P L g).Fired (some d) e o) (hk : e.kind = .wait m parity ok acq scope) :
    (Machine.code P L g).pc d ∈ Flow.mbarWait.toList := by
  obtain ⟨t, _, hf⟩ := hf
  change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  cases hc : kernel.code[(Machine.code P L g).pc d]? with
  | none =>
    rw [hc] at hf
    obtain ⟨he, _⟩ := hf
    rw [he] at hk
    contradiction
  | some ins =>
    rw [hc] at hf
    cases hop : pollOp ins.op
    · exact (fires_notWait (eventTmpl_notWait (pollOp_ne hop)) hf
        m parity ok acq scope hk).elim
    · exact OpPcsFast.mem poll_sites hc hop

/-- The role sites at which a thread can issue a barrier poll. -/
def PollSite : Machine.ThreadD → Prop
  | .wg0 q => q.site = .maskReady ∨ q.site = .qkDone ∨ q.site = .svDone
  | .mma q => q.site = .qWait ∨ q.site = .qCopyWait ∨ q.site = .kvWait ∨ q.site = .soWait
  | .tma q => q.site = .waitQ ∨ q.site = .waitLast ∨ q.site = .waitCoord ∨ q.site = .waitFree
  | .index q => ∃ extra, q.site = .waitFree extra
  | .wg2 q => q.site = .qUtccp ∨ q.site = .rawReady ∨ q.site = .svDone
  | _ => False

/-- The frozen kernel and the followed role exhaust all barrier poll sites. -/
theorem poll_site {m : Loc} {parity : Nat} {ok acq : Bool} {scope : MbarScope}
    (hf : (Machine.machine P L g).Fired (some d) e o) (hk : e.kind = .wait m parity ok acq scope) :
    PollSite d := by
  have hm := poll_pc_of_fired hf hk
  clear * - d hm
  cases d
  case prologue q =>
    change False
    change q.pc ∈ _ at hm
    cases q <;> revert hm <;> decide_site
  case wg0 q =>
    change q.site.pc ∈ _ at hm
    simp only [PollSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case mma q =>
    change q.site.pc ∈ _ at hm
    simp only [PollSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case tma q =>
    change q.site.pc ∈ _ at hm
    simp only [PollSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case index q =>
    change q.site.pc ∈ _ at hm
    simp only [PollSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case wg2 q =>
    change q.site.pc ∈ _ at hm
    simp only [PollSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case idle q =>
    change False
    change q.pc ∈ _ at hm
    cases q <;> revert hm <;> decide
  case head =>
    change 1843 ∈ _ at hm
    exact (by decide : 1843 ∉ Flow.mbarWait.toList) hm
  case done =>
    change 3611 ∈ _ at hm
    exact (by decide : 3611 ∉ Flow.mbarWait.toList) hm
end

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
include hX hs

/-- An actual non-fault event at a followed index has a concrete composed role step. -/
theorem fired_at_followed (hFollowed : Frame.stateAt (Machine.code P L) X g i ≠ some none)
    (he : X.get (g, i) = some e) (hn : ∀ f, e.kind ≠ .ub f) :
    ∃ d o, Frame.stateAt (Machine.code P L) X g i = some (some d) ∧
      (Machine.machine P L g).Fired (some d) e o := by
  have hg := Frame.lt_of_get hX he
  rcases (hs.produces (hX.thr g hg)).fired he with ⟨s, o, hst, hf⟩ | ⟨_, _, f, rfl⟩
  · cases s with
    | none => exact (hFollowed hst).elim
    | some d => exact ⟨d, o, hst, hf⟩
  · exact (hn f rfl).elim

/-- An actual barrier event fires at one of the corresponding composed role sites. -/
theorem fired_from_trace (ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, i) = some e)
    (hn : ∀ f, e.kind ≠ .ub f) :
    ∃ d o, Frame.stateAt (Machine.code P L) X g i = some (some d) ∧
      (Machine.machine P L g).Fired (some d) e o :=
  fired_at_followed hX hs (ht g i (Frame.lt_of_get hX he)) he hn

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingSourceSites
