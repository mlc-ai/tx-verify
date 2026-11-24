-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingInitPublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingConsumerControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Lemmas.Flow.NotObject
import Lemmas.Flow.NotBulk
import Lemmas.Order.OrderBaseCausality

@[expose] public section

/-! # Table initialization before actual arrivals and waits -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat} {e : Event}

private theorem init_before_actual_nonaccess
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (ha : e.acc = none) (hub : ∀ f, e.kind ≠ .ub f)
    (hRole : ∀ d o, (Machine.machine P L g).Fired (some d) e o → ∀ s, d ≠ .prologue s)
    (j : Fin 23) :
    ∃ init, X.MbInit init (initTable.loc L (ctaOf L g) j) (initCount j) ∧
      baseCausality L X init (g, i) := by
  rcases Frame.fired hs hX he with ⟨role, o, hd, hf⟩ | ⟨_, _, f, hFault⟩
  · cases role with
    | some d =>
      exact completed_init_before_followed_role hpre hX hs he hd (hRole d o hf) j
    | none =>
      obtain ⟨k, hk, d, f, hGet, hState, hDismiss⟩ := prior_dismissal (PTX.len_of_get he).le hd
      have hNonPrologue : ∀ s, d ≠ .prologue s := by
        intro s h
        cases dismissal_is_consumer hpre hX hs hGet hState hDismiss <;> cases h
      obtain ⟨init, hInit, hBefore⟩ :=
        completed_init_before_followed_role hpre hX hs hGet hState hNonPrologue j
      have hPo : po X (g, k) (g, i) := po_of_not_access rfl hk (PTX.len_of_get he) (by
        rw [he, Option.bind_some, ha])
      exact ⟨init, hInit, hBefore.trans (.single (.inl hPo))⟩
  · exact (hub f (congrArg Event.kind hFault)).elim

/-- Actual mbarrier polls use the caller's CTA and follow publication of its table. -/
theorem table_init_before_actual_poll {m : Loc} {p : Nat} {ok acq : Bool} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hk : e.kind = .wait m p ok acq scope) (j : Fin 23) :
    m.cta = ctaOf L g ∧
      ∃ init, X.MbInit init (initTable.loc L (ctaOf L g) j) (initCount j) ∧
        baseCausality L X init (g, i) := by
  have hub (f : Fault) : e.kind ≠ .ub f := by rw [hk]; intro h; cases h
  have hc : m.cta = ctaOf L g := by
    rcases get_source hX he with ⟨f, hf⟩ | ⟨_, _, _, _, _, hf⟩
    · exact (hub f hf).elim
    · exact (fires_wait_local hf hk).2
  refine ⟨hc, init_before_actual_nonaccess hpre hX hs he ?_ hub ?_ j⟩
  · obtain ⟨tag, kind⟩ := e
    change kind = _ at hk
    subst kind
    rfl
  · intro d o hf s h
    subst d
    exact RingSourceSites.poll_site hf hk

/-- Actual mbarrier arrivals follow table publication, including after numerical dismissal. -/
theorem table_init_before_actual_arrive {m : Loc} {tx count : Nat} {rel : Bool} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hk : e.kind = .arrive m tx count rel scope) (j : Fin 23) :
    ∃ init, X.MbInit init (initTable.loc L (ctaOf L g) j) (initCount j) ∧
      baseCausality L X init (g, i) := by
  refine init_before_actual_nonaccess hpre hX hs he ?_ ?_ ?_ j
  · obtain ⟨tag, kind⟩ := e
    change kind = _ at hk
    subst kind
    rfl
  · intro f h
    rw [hk] at h
    cases h
  · intro d o hf s h
    subst d
    exact RingSourceSites.arrive_site hf hk

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
