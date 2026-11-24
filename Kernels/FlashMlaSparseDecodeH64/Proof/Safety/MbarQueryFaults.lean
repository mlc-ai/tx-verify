-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarSimpleFaults
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryCopyCompletion
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaLeader
import Lemmas.Protocol.GatedFaults

public section

/-! # Fault-free query copy barrier -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow AsyncCopy MBarrier

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
include hpre hX hs

/-- All arrivals on the query-copy barrier come from its one CTA-local notification. -/
theorem query_copy_notify_unique (ht : Frame.Tracked (Machine.code P L) X) {cta : Nat}
    {r q : Record Ref} {n tx n' tx' : Nat} (hr : r ∈ X.objects (Protocol.QueryCopy.object L cta))
    (hq : q ∈ X.objects (Protocol.QueryCopy.object L cta)) (ha : r.action = .arrive n tx)
    (hb : q.action = .arrive n' tx') : r.id = q.id := by
  let sound := fun g hg => (hs g hg).machine
  obtain ⟨lane, hi⟩ := Wg1MmaLeader.cta_issuer (cta := cta) hpre hX sound
  obtain ⟨_, _, ⟨g, i⟩, _, sp, rank, hId, he, hTarget⟩ :=
    Protocol.QueryCopy.arrival_form hX hpre sound ht hr ha
  obtain ⟨_, _, ⟨g', j⟩, _, sp', rank', hId', he', hTarget'⟩ :=
    Protocol.QueryCopy.arrival_form hX hpre sound ht hq hb
  obtain ⟨hc, d, hd, hState⟩ := Protocol.QueryCopy.notify_source hpre hX sound ht he hTarget
  obtain ⟨hc', d', hd', hState'⟩ :=
    Protocol.QueryCopy.notify_source hpre hX sound ht he' hTarget'
  have hg : g = g' := (hi g i d hc hState (by simp [hd])).trans
    (hi g' j d' hc' hState' (by simp [hd'])).symm
  subst g'
  have hij := QueryTmaSites.commit_site_unique he he' hState hState' hd hd'
  subst j
  have hsp : sp = sp' := (TcKind.commit.inj (Kind.tc.inj
    (congrArg Event.kind (Option.some.inj (he.symm.trans he')))))
  subst sp'
  have hrank := MbarRing.Notify.rank_eq hTarget hTarget'
  rw [hId, hId', hrank]

/-- The per-CTA query-copy barrier never faults, including on its sole commit notification. -/
theorem mbar_query_copy_clean (ht : Frame.Tracked (Machine.code P L) X) {cta : Nat} {r : Record Ref}
    (hr : r ∈ X.objects (Protocol.QueryCopy.object L cta)) :
    r.fault = none := by
  let sound := fun g hg => (hs g hg).machine
  let m := Protocol.QueryCopy.object L cta
  have hFirst := Protocol.QueryCopy.init_first (cta := cta) hpre hX sound ht
  have hNoInv := Protocol.objects_single_lifetime hX m
  have hComp : ∀ q ∈ X.objects m, ∀ n, q.action ≠ .completeTx n :=
    fun q hq n h => Protocol.QueryCopy.no_completion hpre hX sound ht hq h
  cases ha : r.action with
  | init n => exact mbar_init_clean hpre hX hs ht hr ha
  | pollParity p ok => exact mbar_poll_clean hpre hX hs ht hr ha
  | inval => exact (mbar_record_not_inval hX hr ha).elim
  | increment =>
    cases record_source hX.tma.2.2.1 hr with
    | increment _ he _ => exact (Protocol.no_async_arrive hX he rfl).elim
    | init _ _ h | arrive _ _ h | wait _ _ h | inval _ _ h | tensor _ _ _ h
    | arriveOn _ _ _ _ h | bulk _ _ _ _ h | commit _ _ _ h | clc _ _ _ _ h =>
      rw [ha] at h
      cases h
  | completeTx n => exact (hComp r hr n ha).elim
  | arrive n tx =>
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    have hUnit : ∀ q ∈ X.objects m, ∀ n tx, q.action = .arrive n tx → n = 1 ∧ tx = 0 := by
      intro q hq n tx hAct
      obtain ⟨hn, ht, _⟩ := Protocol.QueryCopy.arrival_form hX hpre sound ht hq hAct
      exact ⟨hn, ht⟩
    have hCh := X.objects_checked hX m
    let lanes : Finset Unit := {()}
    let label : Ref → Unit × Nat := fun _ => ((), 0)
    have hValid := hCh.gated_arrive hNoInv lanes label
      (fun i st hi hst => ⟨by
        simpa [lanes] using PairTmaRing.expected_of_init hX hFirst hNoInv hst,
        MbarRing.tx_zero_of hX hNoInv (fun q hq n tx h => (hUnit q hq n tx h).2)
          hComp hi hst⟩)
      (fun i q n tx hi hAct => by
        obtain ⟨_, st, hSt, _⟩ := PairTmaRing.state_of_init hX hFirst hNoInv hi (by simp [hAct])
        exact ⟨st, hSt⟩)
      (fun i q n tx hi hAct => by
        obtain ⟨hn, ht⟩ := hUnit q (List.mem_of_getElem? hi) n tx hAct
        exact ⟨hn, ht, by simp [lanes, label]⟩)
      (fun i j q q' n tx n' tx' hi hj ha ha' _ =>
        ObjectInit.checked_record_index_eq hCh hi hj (query_copy_notify_unique hpre hX hs ht
          (List.mem_of_getElem? hi) (List.mem_of_getElem? hj) ha ha'))
      (fun _ _ _ _ _ _ h => by simp [label] at h)
      (Protocol.objects_no_pending_increment hX m)
    exact (hValid k r n tx hk ha).1

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
