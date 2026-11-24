-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.IpInitElect
public import Kernels.InklingRelDecode.Proof.Interface.LockBar0
public import Kernels.InklingRelDecode.Proof.Interface.SyncFacts

@[expose] public section

/-!
# The start and the prologue along a thread's events

`Thread/IpInitStage.lean` gives the default partition's start and prologue a stage and, up to the
prologue's first `bar.sync 0, 128` (`ProA.Site.bar2`), an exact number of earlier barrier-0
events. This file lifts them to an execution:

* `step_pred`: the state before event `k + 1` and the state before event `k` are joined by the
  machine's step on event `k`;
* `event_b0`: an event is a barrier-0 event exactly when its state's instruction is one
  (`b0At`), and the `bar.sync 0, 128` of `bar2` fires `bar 0 (some 128)`;
* `exact_count`: at a state with an exact count (`exb`) the thread's earlier barrier-0 events are
  that many;
* `stg_trace`: the stage never decreases along the thread and rises at the start and the
  prologue;
* `reach_bar2`: a thread at a prologue site after `bar2`, or in the softmax region or the
  epilogue, was earlier at `bar2`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.IpInit

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The predecessor of a state**: the state before event `k` and the event join it to the state
before event `k + 1` by the machine's step. -/
theorem step_pred {g k : Nat} {s' : TSt} (hk : k < (X.tr g).length)
    (h : St Q L X g (k + 1) = some (some s')) :
    ∃ s e, St Q L X g k = some (some s) ∧ (X.tr g)[k]? = some e ∧
      (threadCode L g Q).next s e = some (some s') := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
  have h' : Frame.stateAt (code L Q) X g (k + 1) = some (some s') := h
  rw [Frame.stateAt_succ he] at h'
  cases hσ : Frame.stateAt (code L Q) X g k with
  | none => rw [hσ] at h'; simp at h'
  | some o =>
    cases o with
    | none => rw [hσ] at h'; simp [Flow.Code.toMachine] at h'
    | some s =>
      rw [hσ] at h'
      simp only [Option.bind_some] at h'
      exact ⟨s, e, hσ, he, h'⟩

/-- **The predecessor of a default-partition state** is a default-partition state. -/
theorem step_pred_d {g k : Nat} {d' : DComp.St} (hk : k < (X.tr g).length)
    (h : St Q L X g (k + 1) = some (some (.d d'))) :
    ∃ d e, St Q L X g k = some (some (.d d)) ∧ (X.tr g)[k]? = some e ∧
      DComp.next L g Q d e = some (some d') := by
  obtain ⟨s, e, hσ, he, hn⟩ := step_pred hk h
  cases s with
  | d d =>
    obtain ⟨a, ha, hh⟩ := Ledger.mapInv (show (DComp.next L g Q d e).map
      (Option.map TSt.d) = some (some (.d d')) from hn)
    cases hh
    exact ⟨d, e, hσ, he, ha⟩
  | w w =>
    obtain ⟨a, ha, hh⟩ := Ledger.mapInv (show (WComp.next L g w e).map
      (Option.map TSt.w) = some (some (.d d')) from hn)
    cases hh

/-- **An event fired before the last one continues**: it fires from the state before it into a
concrete state. -/
theorem fired_step (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {e : Event} {s : TSt}
    (hg : g < L.threads) (he : (X.tr g)[k]? = some e) (hk : k + 1 < (X.tr g).length)
    (hσ : St Q L X g k = some (some s)) :
    ∃ u, (threadCode L g Q).toMachine.Fired (some s) e (some u) := by
  obtain ⟨τ, u, hτ, hf⟩ := Machine.Trace.fired_some (Frame.trace hS hX hg) he hk
  have h2 : St Q L X g k = some τ := hτ
  rw [hσ] at h2
  cases h2
  exact ⟨u, hf⟩

/-- **An event is on barrier 0 exactly when its state's instruction is**: and at `bar.sync 0, 128`
it fires that arrival. -/
theorem event_b0 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {e : Event} {s : TSt}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s)) :
    Execution.isBarId 0 e = true ↔ b0At (TSt.pc s) ≠ 0 := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hc' : kernel.code[TSt.pc s]? = some ins := hc
  have hf' : Fires (TSt.pc s) (eventTmpl asms L g t ins.op) e o := hf
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have hmem := List.mem_of_getElem? hc'
  constructor
  · intro h1
    obtain ⟨pc, c, m, hev⟩ := NamedBar.isBarId_form h1
    have hk : e.kind = .bar 0 c m := by rw [hev]
    rcases bar_kind_op hb hmem hf' hk with ⟨al, hop⟩ | ⟨-, al, hop⟩
    · simp [b0At, hc', hop]
    · simp [b0At, hc', hop]
  · intro h1
    cases hop : ins.op with
    | barSync b al =>
      cases b with
      | imm v =>
        by_cases hv : v = 0
        · subst hv
          rw [hop] at hf'
          have := EvD.fires_barSync_imm (id := 0) (by decide) hf'
          rw [this]
          simp [Execution.isBarId]
        · simp [b0At, hc', hop, hv] at h1
      | _ => simp [b0At, hc', hop] at h1
    | barSyncN b c al =>
      cases b with
      | imm v =>
        cases c with
        | imm w =>
          by_cases hvw : v = 0 ∧ w = 128
          · obtain ⟨rfl, rfl⟩ := hvw
            rw [hop] at hf'
            have := EvD.fires_barSyncN_128 hb hf'
            rw [this]
            simp [Execution.isBarId]
          · simp only [b0At, hc', hop] at h1
            split at h1 <;> simp_all
        | _ => simp [b0At, hc', hop] at h1
      | _ => simp [b0At, hc', hop] at h1
    | _ => simp [b0At, hc', hop] at h1

/-- The first state of a default-partition thread is a state of the common start with no
barrier-0 event before it. -/
theorem init_exb {g : Nat} {d : DComp.St} (h : (threadCode L g Q).init = .d d) :
    exb d = some 0 := by
  have h' : (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init) = .d d := h
  split_ifs at h' with hc
  · cases h'
    show exb (.dstart (DStart.D.start L g)) = some 0
    unfold DStart.D.start
    split_ifs <;> rfl

/-- The first state of a default-partition thread is not after the prologue's first barrier. -/
theorem init_not_late {g : Nat} {d : DComp.St} (h : (threadCode L g Q).init = .d d) :
    (∃ x, d = .dstart x) := by
  have h' : (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init) = .d d := h
  split_ifs at h' with hc
  · cases h'
    exact ⟨DStart.D.start L g, rfl⟩

/-- **The exact barrier-0 count**: at a state with an exact count (`exb`), the thread's earlier
events on barrier 0 are that many. -/
theorem exact_count (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g : Nat} :
    ∀ k d n, k ≤ (X.tr g).length → St Q L X g k = some (some (.d d)) → exb d = some n →
      ((X.tr g).take k).countP (Execution.isBarId 0) = n := by
  intro k
  induction k with
  | zero =>
    intro d n _ hs hn
    have hs : Frame.stateAt (code L Q) X g 0 = some (some (.d d)) := hs
    rw [Frame.stateAt_zero] at hs
    have h0 := init_exb (Option.some.inj (Option.some.inj hs))
    rw [h0] at hn
    simp only [Option.some.injEq] at hn
    simp [← hn]
  | succ k ih =>
    intro d' n' hk hs' hn'
    obtain ⟨d, e, hσ, he, hn⟩ := step_pred_d (by omega) hs'
    obtain ⟨n, hn0, hnn⟩ := exb_next hn hn'
    have h1 := ih d n (by omega) hσ hn0
    have h2 := event_b0 hpre hX hS (show X.get (g, k) = some e from he) hσ
    rw [countP_succ he, h1, hnn]
    simp only [b0inc, TSt.pc] at h2 ⊢
    by_cases hb : b0At (DComp.pc d) = 0
    · have : ¬ Execution.isBarId 0 e = true := fun h => (h2.mp h) hb
      simp [this, hb]
    · have := h2.mpr hb
      simp [this, hb]

/-- **The stage along a thread**: it never decreases, and it rises at the common start and in
the prologue. -/
theorem stg_trace {g : Nat} {k : Nat} {d : DComp.St} (hd : St Q L X g k = some (some (.d d))) :
    ∀ j d', k ≤ j → j ≤ (X.tr g).length → St Q L X g j = some (some (.d d')) →
      stg d ≤ stg d' ∧ (k < j → ((∃ x, d = .dstart x) ∨ (∃ x, d = .pro x)) → stg d < stg d') := by
  intro j
  induction j with
  | zero =>
    intro d' hkj _ hd'
    have : k = 0 := by omega
    subst this
    rw [hd] at hd'
    cases hd'
    exact ⟨le_rfl, fun h => by omega⟩
  | succ j ih =>
    intro d' hkj hj hd'
    by_cases hk : k = j + 1
    · subst hk
      rw [hd] at hd'
      cases hd'
      exact ⟨le_rfl, fun h => by omega⟩
    · obtain ⟨d0, e, hσ, he, hn⟩ := step_pred_d (by omega) hd'
      obtain ⟨h1, h2⟩ := ih d0 (by omega) (by omega) hσ
      obtain ⟨h3, h4⟩ := stg_next hn
      refine ⟨le_trans h1 h3, fun _ hc => ?_⟩
      by_cases hkj : k < j
      · exact lt_of_lt_of_le (h2 hkj hc) h3
      · have : k = j := by omega
        subst this
        rw [hd] at hσ
        cases hσ
        exact h4 hc

/-! ### Finding the earlier states -/

theorem site_eq_close : ∀ a : ProA.Site, ∀ c ∈ closeSites, a.ctorIdx = c.ctorIdx → a = c := by
  intro a
  cases a <;> decide

/-- The states after the prologue's first `bar.sync 0, 128`. -/
def After2 : DComp.St → Prop
  | .dstart _ => False
  | .pro d => ProA.Site.bar2.ctorIdx < d.site.ctorIdx
  | .sm _ => True
  | .epi _ => True

/-- **A thread after the prologue's first barrier was at it**: at a prologue site after `bar2`, or
in the softmax region or the epilogue, an earlier state of the thread is `bar2`. -/
theorem reach_bar2 {g : Nat} :
    ∀ k d, k ≤ (X.tr g).length → St Q L X g k = some (some (.d d)) → After2 d →
      ∃ y < k, ∃ dt, St Q L X g y = some (some (.d (.pro ⟨.bar2, dt⟩))) := by
  intro k
  induction k with
  | zero =>
    intro d _ hs ha
    have hs : Frame.stateAt (code L Q) X g 0 = some (some (.d d)) := hs
    rw [Frame.stateAt_zero] at hs
    obtain ⟨x, hx⟩ := init_not_late (Option.some.inj (Option.some.inj hs))
    subst hx
    exact absurd ha id
  | succ k ih =>
    intro d' hk hs' ha
    obtain ⟨d, e, hσ, he, hn⟩ := step_pred_d (by omega) hs'
    rcases next_cases hn with ⟨x, x', rfl, rfl, -, -⟩ | ⟨x, x', rfl, -, -, rfl⟩ |
      ⟨x, x', rfl, hb, rfl, hnx⟩ | ⟨x, x', rfl, hb18, rfl⟩ | ⟨x, x', rfl, rfl⟩ |
      ⟨x, x', rfl, rfl⟩ | ⟨x, x', rfl, rfl⟩
    · exact absurd ha id
    · exact absurd ha (by simp [After2, ProA.D.start]; decide)
    · by_cases h1 : ProA.Site.bar2.ctorIdx < x.site.ctorIdx
      · obtain ⟨y, hy, hdt⟩ := ih (.pro x) (by omega) hσ h1
        exact ⟨y, by omega, hdt⟩
      · by_cases h2 : x.site.ctorIdx = ProA.Site.bar2.ctorIdx
        · have h3 := site_eq_close x.site .bar2 (by decide) h2
          obtain ⟨s, dt⟩ := x
          simp only at h3
          subst h3
          exact ⟨k, by omega, dt, hσ⟩
        · have h3 : x.site.ctorIdx < ProA.Site.bar2.ctorIdx := by omega
          have := pro_next_le hnx (c := .bar2) (by decide) h3
          simp only [After2] at ha
          omega
    · have h1 : ProA.Site.bar2.ctorIdx < x.site.ctorIdx := by rw [hb18]; decide
      obtain ⟨y, hy, hdt⟩ := ih (.pro x) (by omega) hσ h1
      exact ⟨y, by omega, hdt⟩
    · obtain ⟨y, hy, hdt⟩ := ih (.sm x) (by omega) hσ trivial
      exact ⟨y, by omega, hdt⟩
    · obtain ⟨y, hy, hdt⟩ := ih (.sm x) (by omega) hσ trivial
      exact ⟨y, by omega, hdt⟩
    · obtain ⟨y, hy, hdt⟩ := ih (.epi x) (by omega) hσ trivial
      exact ⟨y, by omega, hdt⟩

theorem elSite_close : ∀ j < 12, ProA.elSite j ∈ closeSites := by decide

/-- The states at a prologue site after the election `el j`. -/
def AfterEl (j : Nat) : DComp.St → Prop
  | .pro d => (ProA.elSite j).ctorIdx < d.site.ctorIdx
  | _ => False

/-- **A thread after the election `el j` made it**: an earlier state of the thread is `el j`, its
event an election, and, if the election returned the thread's lane and the thread is in warp 0,
the next state is the initialization `in j`. -/
theorem elect_before (hb : L.block = 256) {g j : Nat} (hj : j < 12) :
    ∀ k d, k ≤ (X.tr g).length → St Q L X g k = some (some (.d d)) → AfterEl j d →
      ∃ k0 < k, ∃ dt e0 mk inst ld, St Q L X g k0 = some (some (.d (.pro ⟨ProA.elSite j, dt⟩))) ∧
        (X.tr g)[k0]? = some e0 ∧ e0.kind = .elect mk inst ld ∧
        (laneOf L g = ld → g % L.block < 32 →
          ∃ dt', St Q L X g (k0 + 1) = some (some (.d (.pro ⟨ProA.inSite j, dt'⟩)))) := by
  intro k
  induction k with
  | zero =>
    intro d _ hs ha
    have hs : Frame.stateAt (code L Q) X g 0 = some (some (.d d)) := hs
    rw [Frame.stateAt_zero] at hs
    obtain ⟨x, hx⟩ := init_not_late (Option.some.inj (Option.some.inj hs))
    subst hx
    exact absurd ha id
  | succ k ih =>
    intro d' hk hs' ha
    obtain ⟨d, e, hσ, he, hn⟩ := step_pred_d (by omega) hs'
    rcases next_cases hn with ⟨x, x', rfl, rfl, -, -⟩ | ⟨x, x', rfl, -, -, rfl⟩ |
      ⟨x, x', rfl, hb18, rfl, hnx⟩ | ⟨x, x', rfl, hb18, rfl⟩ | ⟨x, x', rfl, rfl⟩ |
      ⟨x, x', rfl, rfl⟩ | ⟨x, x', rfl, rfl⟩
    · exact absurd ha id
    · exact absurd ha (by simp only [AfterEl, ProA.D.start]; exact Nat.not_lt_zero _)
    · have hc := elSite_close j hj
      by_cases h1 : (ProA.elSite j).ctorIdx < x.site.ctorIdx
      · obtain ⟨k0, hk0, r⟩ := ih (.pro x) (by omega) hσ h1
        exact ⟨k0, by omega, r⟩
      · by_cases h2 : x.site.ctorIdx = (ProA.elSite j).ctorIdx
        · have h3 := site_eq_close x.site _ hc h2
          obtain ⟨s, dt⟩ := x
          simp only at h3
          subst h3
          obtain ⟨mk, inst, ld, hk', hiff⟩ := el_step hb hj hnx
          refine ⟨k, by omega, dt, e, mk, inst, ld, hσ, he, hk', fun hl hw => ?_⟩
          obtain ⟨s', dt'⟩ := x'
          simp only at hiff
          have := hiff.mpr ⟨hl, hw⟩
          subst this
          exact ⟨dt', hs'⟩
        · have h3 : x.site.ctorIdx < (ProA.elSite j).ctorIdx := by omega
          have := pro_next_le hnx hc h3
          simp only [AfterEl] at ha
          omega
    · exact absurd ha id
    · exact absurd ha id
    · exact absurd ha id
    · exact absurd ha id

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
