-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingActualIndexPool
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingProducerPhase

@[expose] public section

/-! # Free phases observed by an actual coordinate producer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An index publication and its coordinate and validity stores share the same reuse protocol. -/
def IndexProductionSite (site : Wg1Index.Site) : Prop :=
  (∃ extra, site = .ready extra) ∨ (∃ extra high, site = .coord extra high) ∨
    ∃ extra, site = .valid extra

/-- A producer above use `n` observes at least `n + 1` completed batches of returns. -/
theorem actual_producer_free_pool {g i n : Nat} {d : Wg1Index.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hSite : IndexProductionSite d.site) (hUse : n < d.block / 4) :
    let m := free L (ctaOf L g) (indexSlot d.block)
    ∃ records : Finset Nat, records.card = (n + 1) * 129 ∧ ∀ k ∈ records,
      ∃ (r : Record Ref) (h j tag : Nat), (X.objects m)[k]? = some r ∧
        r.id = .thread (h, j) ∧ X.get (h, j) = some ⟨tag, .arrive m 0 1 true .cta⟩ ∧
        baseCausality L X (h, j) (g, i) := by
  classical
  let slot := indexSlot d.block
  let m := free L (ctaOf L g) slot
  have hPoll (use : Nat) (hUse : use ≤ d.block / 4) :
      Nonempty (ProducerFreePoll X g i use m) := by
    rcases hSite with ⟨extra, hReady⟩ | hStore
    · exact producer_free_poll_record hpre hX hs he hd hReady hUse
    · exact index_store_free_poll_record hpre hX hs he hd hStore hUse
  let poll (a : Fin (n + 1)) := (hPoll (a.val + 1) (by have := a.isLt; omega)).some
  have hOrdered : StrictMono (fun a : Fin (n + 1) => (poll a).before.phase) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro a
    exact (poll a.castSucc).phase_lt_succ hX (poll a.succ)
  let waits (a : Fin (n + 1)) : IndexPhaseWait X m g i 129 := by
    let w := poll a
    have ha : a.val + 1 ≤ d.block / 4 := by have := a.isLt; omega
    have hLower : a.val + 1 ≤ w.before.phase := by
      rcases hSite with ⟨extra, hReady⟩ | hStore
      · exact producer_free_phase_lower hpre hX hs he hd hReady ha w
      · exact index_store_free_phase_lower hpre hX hs he hd hStore ha w
    have hp : 0 < w.before.phase := by omega
    exact ⟨w.pos, w.tag, 1 - (a.val + 1) % 2, w.pos_lt, w.event, w.index, w.record, w.before,
      w.get_record, w.id, w.clean, w.response, w.state, w.expected, hp,
      by simpa only [ite_eq_left hp] using w.observed⟩
  exact actual_index_phase_pool hpre hX hs
    (.inr rfl : m = ready L (ctaOf L g) slot ∨ m = free L (ctaOf L g) slot) he waits hOrdered

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
