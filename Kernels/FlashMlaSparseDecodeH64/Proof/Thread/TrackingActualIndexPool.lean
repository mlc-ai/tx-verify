-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingActualIndexPhases
import Lemmas.Order.OrderWaits

@[expose] public section

/-! # Releases observed by a sequence of actual index-ring waits -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- One successful wait after a completed phase of an initialized index barrier. -/
structure IndexPhaseWait (X : Execution) (m : Loc) (g i expected : Nat) where
  pos : Nat
  tag : Nat
  parity : Nat
  pos_lt : pos < i
  event : X.get (g, pos) = some ⟨tag, .wait m parity true true .cta⟩
  index : Nat
  record : Record Ref
  before : State
  get : (X.objects m)[index]? = some record
  source : record.id = .thread (g, pos)
  clean : record.fault = none
  waited : record.reply.waited = some true
  state : stateBefore (X.objects m) index = some before
  count : before.expected = expected
  positive : 0 < before.phase
  seen : observedAt (X.objects m) index = some (before.phase - 1)

/-- Distinct completed phases give disjoint sets of actual release records.
Every release precedes the event that follows all of these waits. -/
theorem actual_index_phase_pool {m : Loc} {g i rounds expected : Nat} {slot : Fin 4} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hm : m = ready L (ctaOf L g) slot ∨ m = free L (ctaOf L g) slot)
    (he : X.get (g, i) = some e)
    (waits : Fin rounds → IndexPhaseWait X m g i expected)
    (ordered : StrictMono (fun j => (waits j).before.phase)) :
    ∃ records : Finset Nat, records.card = rounds * expected ∧ ∀ k ∈ records,
      ∃ (r : Record Ref) (h j tag : Nat), (X.objects m)[k]? = some r ∧ r.id = .thread (h, j) ∧
        X.get (h, j) = some ⟨tag, .arrive m 0 1 true .cta⟩ ∧
        baseCausality L X (h, j) (g, i) := by
  classical
  let log := X.objects m
  have entries (a : Fin rounds) :
      ∃ entries : Finset Nat, entries.card = expected ∧ ∀ k ∈ entries,
        ∃ (r : Record Ref) (h j tag : Nat), k < (waits a).index ∧
          log[k]? = some r ∧ r.id = .thread (h, j) ∧
          r.fault = none ∧ phaseAt log k = some ((waits a).before.phase - 1) ∧
          X.get (h, j) = some ⟨tag, .arrive m 0 1 true .cta⟩ := by
    let w := waits a
    have hp := w.positive
    have hPhase : w.before.phase = ((waits a).before.phase - 1) + 1 := by
      change w.before.phase = (w.before.phase - 1) + 1
      omega
    exact actual_index_phase_units hpre hX hs hm w.get w.state hPhase w.count
  let batch (a : Fin rounds) := (entries a).choose
  have hDisj :
      (↑(Finset.univ : Finset (Fin rounds)) : Set (Fin rounds)).PairwiseDisjoint batch := by
    intro a _ b _ hNe
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    obtain ⟨_, _, _, _, _, _, _, _, hA, _⟩ := (entries a).choose_spec.2 k hk
    obtain ⟨_, _, _, _, _, _, _, _, hB, _⟩ := (entries b).choose_spec.2 k hk'
    have hEq := Option.some.inj (hA.symm.trans hB)
    have hPosA := (waits a).positive
    have hPosB := (waits b).positive
    exact hNe (ordered.injective (by omega))
  refine ⟨Finset.univ.biUnion batch, ?_, fun k hk => ?_⟩
  · rw [Finset.card_biUnion hDisj]
    simp only [show ∀ a, (batch a).card = expected from fun a => (entries a).choose_spec.1,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  · obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨r, h, j, tag, hPast, hr, hId, hClean, hAt, hGet⟩ := (entries a).choose_spec.2 k ha
    let w := waits a
    have hObs : WaitObserves X (.thread (h, j)) (g, w.pos) m true .cta :=
      ⟨⟨w.tag, w.parity, w.event⟩, k, w.index, r, w.record, w.before.phase - 1, hr, hId, hClean,
        w.get, w.source, w.clean, w.waited, hPast, hAt, w.seen,
        (objects_single_lifetime hX m).sameLifetime k w.index⟩
    have hCta : m.cta = ctaOf L g := by rcases hm with rfl | rfl <;> rfl
    have hhCta := (actual_arrive_fields hX hGet rfl).2.1
    have hSame : SameCta L h g :=
      ⟨Frame.lt_of_get hX hGet, Frame.lt_of_get hX he, hhCta.symm.trans hCta⟩
    have hOrder := Staging.baseCausality_of_handoff (e := (h, j)) (f := (g, i))
      ⟨0, 1, tag, hGet⟩ hObs (ScopesMeet.of_sameCta hSame) ⟨rfl, le_rfl⟩
      ⟨rfl, w.pos_lt, PTX.len_of_get he⟩
    exact ⟨r, h, j, tag, hr, hId, hGet, hOrder⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
