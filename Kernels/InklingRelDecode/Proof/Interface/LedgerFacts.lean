-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LedgerInv
public import Kernels.InklingRelDecode.Proof.Interface.ExitFacts

@[expose] public section

/-!
# The statements of the register ledger, from the phases of the abstract states

* `ledger_shape`: the register request of ordinal `r` of a thread of warpgroup `w` is `inc 256`,
  except the workers' (`w = 1`) `dec 24` at ordinals `r % 3 = 1`;
* `ledger_b1`: a request that is no loop head and is not the thread's first has `n` barrier-1
  events before it, `0 < n ≤ 3`, and every thread of its warpgroup has made at least as many
  requests before its barrier-1 event of ordinal `n - 1`;
* `ledger_exit`: an exiting thread has made at least three barrier-1 arrivals.

They follow from `phase_inv` (`LedgerInv.lean`): the default partition's requests are at the
phases `(1,1)` and `(2,3)` of its single round; a worker's requests that are no loop head are
a role's, in the first round (`t = 0`), at phase `(1,1)` and `(2,3)`; the arrivals of ordinal 0
and 2 of any thread have made one and two requests. The only fact about values is `RoleReads`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The state before an event that is no undefined behaviour**: followed, of the kind of the
thread (default partition or worker). -/
theorem event_ctx (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {g k : Nat} {e : Event} (he : X.get (g, k) = some e) (hne : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    ∃ s, St Q L X g k = some (some s) ∧
      (((∃ d, s = .d d) ∧ IsDefault L g) ∨ ((∃ w, s = .w w) ∧ ¬ IsDefault L g)) := by
  obtain ⟨s, hσ⟩ := Frame.event_state hS hX ht he hne
  refine ⟨s, hσ, ?_⟩
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hS hX he hσ
  cases s with
  | d d => exact .inl ⟨⟨d, rfl⟩, hinv.1⟩
  | w w => exact .inr ⟨⟨w, rfl⟩, hinv.1⟩

theorem event_le (he : X.get (g, k) = some e) : k ≤ (X.tr g).length := by
  have := (List.getElem?_eq_some_iff.mp he).1
  simp only at this
  omega

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
include hpre hX hS ht

/-- **The phase at an event**: the state before it, the kind of thread, and its counts. -/
theorem phase_at_event (hR : RoleReads L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hne : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    ∃ s, St Q L X g k = some (some s) ∧ PhaseAt X g k s ∧
      (((∃ d, s = .d d) ∧ IsDefault L g) ∨ ((∃ w, s = .w w) ∧ ¬ IsDefault L g)) := by
  obtain ⟨s, hσ, hc⟩ := event_ctx hX hS ht he hne
  exact ⟨s, hσ, phase_inv hpre hX hS hR k s (event_le he) hσ, hc⟩

omit hpre hX hS ht in
theorem no_ub_request {pc : Nat} {i : Bool} {n inst : Nat} :
    ∀ pc' f, (⟨pc, .setMaxReg i n inst⟩ : Event) ≠ ⟨pc', .ub f⟩ := by
  intro pc' f h
  cases h

/-- **The request schedule**: the register request of ordinal `r` of a thread of warpgroup `w` is
`inc 256`, except the workers' `dec 24` at ordinals `r % 3 = 1`. -/
theorem ledger_shape (hR : RoleReads L X) {g k pc : Nat} {inc : Bool} {n inst : Nat}
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) :
    (inc, n) =
      if (g % L.block) / 128 = 1 ∧ rqN X g k % 3 = 1 then (false, 24) else (true, 256) := by
  obtain ⟨s, hσ, ⟨hto, t, h1, h2, h3, h4, h5, h6⟩, hc⟩ := phase_at_event hpre hX hS ht hR he
    no_ub_request
  have hq := (event_req hX hS he hσ).2 pc inc n inst rfl
  have hb : L.block = 256 := hpre.block
  rcases hc with ⟨⟨d, rfl⟩, hd⟩ | ⟨⟨w, rfl⟩, hd⟩
  · obtain ⟨hi, hn⟩ := d_req_inc (s := d) hq
    unfold IsDefault at hd
    have : g % L.block / 128 = 0 := by omega
    simp [this, hi, hn]
  · have hs := w_req_sched (s := w) hq
    have hle := (w_ph_le w).1
    unfold IsDefault at hd
    have hg : g % L.block / 128 = 1 := by
      have := Nat.mod_lt g (show L.block > 0 by omega)
      omega
    simp only [tPh] at h1
    rw [hs]
    simp only [hg, true_and]
    by_cases hp : (wPh w).1 = 1
    · have : rqN X g k % 3 = 1 := by omega
      simp [hp, this]
    · have : ¬ rqN X g k % 3 = 1 := by omega
      simp [hp, this]

omit hpre hX hS ht in
theorem loop_not_exempt : ¬ (asms.all (fun a => !a.regSyncExempt Worker.Site.loop.pc) = true) := by
  simp [asms, Assumptions.all, Assumptions.setMaxNRegSync, Assumption.setMaxNRegSyncAt,
    Assumptions.regSyncSites, Worker.Site.pc]

omit hpre hX hS ht in
/-- The events of a barrier-1 arrival: no undefined behaviour. -/
theorem no_ub_bar {pc : Nat} {c : Option Nat} {m : BarMode} :
    ∀ pc' f, (⟨pc, .bar 1 c m⟩ : Event) ≠ ⟨pc', .ub f⟩ := by
  intro pc' f h
  cases h

/-- **A barrier-1 event's phase**: at ordinal 0 it has made at least one request, at ordinal 2 at
least two. -/
theorem b1_requests (hR : RoleReads L X) {h i pc : Nat} {cnt : Option Nat} {m : BarMode}
    (he : X.get (h, i) = some ⟨pc, .bar 1 cnt m⟩) :
    (b1N X h i = 0 → 1 ≤ rqN X h i) ∧ (b1N X h i = 2 → 2 ≤ rqN X h i) := by
  obtain ⟨s, hσ, ⟨hto, t, h1, h2, h3, h4, h5, h6⟩, hc⟩ := phase_at_event hpre hX hS ht hR he
    no_ub_bar
  have hb := event_b1 hpre hX hS he hσ
  have hb1 : tB1 s = true := by
    rw [← hb]
    simp [Execution.isBarId]
  rcases hc with ⟨⟨d, rfl⟩, hd⟩ | ⟨⟨w, rfl⟩, hd⟩
  · obtain ⟨p1, p2, p3⟩ := d_b1_phase (s := d) hb1
    have ht0 := h3 rfl
    simp only [tPh] at h1 h2
    constructor <;> intro hz <;> omega
  · obtain ⟨p1, p2, p3⟩ := w_b1_phase (s := w) hb1 hto
    simp only [tPh] at h1 h2
    constructor <;> intro hz <;> omega

/-- **The pairing of the requests with the barrier-1 events** (`b1` of the ledger). -/
theorem ledger_b1 (hR : RoleReads L X) {g k pc : Nat} {inc : Bool} {n inst : Nat}
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩)
    (hna : asms.all (fun a => !a.regSyncExempt pc) = true) (hpos : 0 < rqN X g k) :
    0 < b1N X g k ∧ b1N X g k ≤ 3 ∧
      ∀ h i pc' cnt m, SetMaxNReg.SameGroup L g h → X.get (h, i) = some ⟨pc', .bar 1 cnt m⟩ →
        b1N X h i + 1 = b1N X g k → rqN X g k ≤ rqN X h i := by
  obtain ⟨s, hσ, ⟨hto, t, h1, h2, h3, h4, h5, h6⟩, hc⟩ := phase_at_event hpre hX hS ht hR he
    no_ub_request
  have hq := (event_req hX hS he hσ).2 pc inc n inst rfl
  have hpc : pc = TSt.pc s := by
    have := Frame.event_pc hS hX he hσ
    exact this
  have hb : L.block = 256 := hpre.block
  -- the request's own state: the phase `(1,1)` or `(2,3)` of its first round
  have key : ((tPh s = (1, 1) ∨ tPh s = (2, 3)) ∧ t = 0) := by
    rcases hc with ⟨⟨d, rfl⟩, hd⟩ | ⟨⟨w, rfl⟩, hd⟩
    · rcases d_req_phase (s := d) hq with hp | hp | hp
      · have ht0 := h3 rfl
        simp only [tPh] at h1
        rw [hp] at h1
        omega
      · exact ⟨.inl hp, h3 rfl⟩
      · exact ⟨.inr hp, h3 rfl⟩
    · have hr : ¬ ∃ P, w = .worker ⟨.loop, P⟩ := by
        rintro ⟨P, rfl⟩
        apply loop_not_exempt
        have : pc = Worker.Site.loop.pc := hpc
        rw [← this]
        exact hna
      have hk := w_req_kind hq hr hto
      have hph : wPh w = (1, 1) ∨ wPh w = (2, 3) := w_req_phase hq hr
      exact ⟨hph, h4 hk⟩
  obtain ⟨hph, ht0⟩ := key
  subst ht0
  have hb1 : b1N X g k = (tPh s).2 := by omega
  have hr1 : rqN X g k = (tPh s).1 := by omega
  rcases hph with hp | hp <;> rw [hp] at hb1 hr1 <;> simp only at hb1 hr1
  · refine ⟨by omega, by omega, ?_⟩
    intro h i pc' cnt m hgrp hev hbh
    have := (b1_requests hpre hX hS ht hR hev).1 (by omega)
    omega
  · refine ⟨by omega, by omega, ?_⟩
    intro h i pc' cnt m hgrp hev hbh
    have := (b1_requests hpre hX hS ht hR hev).2 (by omega)
    omega

/-- **An exiting thread has made at least three barrier-1 arrivals.** -/
theorem ledger_exit (hR : RoleReads L X) {g j pc : Nat} (he : X.get (g, j) = some ⟨pc, .exit⟩) :
    3 ≤ b1N X g j := by
  have hne : ∀ pc' f, (⟨pc, .exit⟩ : Event) ≠ ⟨pc', .ub f⟩ := by
    intro pc' f h
    cases h
  rcases exit_event_state hX hS ht he with ⟨d, hσ, hs⟩ | ⟨x, hσ, hs⟩
  · obtain ⟨-, t, h1, h2, h3, h4, h5, h6⟩ := phase_inv hpre hX hS hR j _ (event_le he) hσ
    have hp := d_exit_phase d hs
    have ht0 := h3 rfl
    simp only [tPh] at h2
    rw [hp] at h2
    omega
  · obtain ⟨-, t, h1, h2, h3, h4, h5, h6⟩ := phase_inv hpre hX hS hR j _ (event_le he) hσ
    have h6 := h5 rfl
    have hp : wPh (.exit x) = (1, 1) := rfl
    simp only [tPh] at h2
    rw [hp] at h2
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
