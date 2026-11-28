-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.Lag
public import Lemmas.Protocol.PairTmaRing.Blocker
public import Lemmas.Protocol.SingleTmaRing.RingFacts

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow PTX.AsyncCopy
open PTX.MBarrier hiding okPolls

/-- Count issued events by their issuing thread in the object's log. The producer
family is injective, so records witnessing the counts of different lanes are disjoint. -/
private theorem receipts {X : Execution} {l : Loc} {n} (lane : Fin n → Nat)
    (hinj : Function.Injective lane) (event : Event → Bool) (record : Record Ref → Bool)
    (ident : EvId → Ref) (issuer : ∀ i, (ident i).issuer = i)
    (receipt : ∀ b k e, X.get (lane b,k) = some e → event e = true →
      ∃ r ∈ X.objects l, r.id = ident (lane b,k) ∧ record r = true) :
    ∑ b, (X.tr (lane b)).countP event ≤ (X.objects l).countP record := by
  let tagged := fun b (r : Record Ref) => record r && (r.id.issuer.1 == lane b)
  have bounds (b) : (X.tr (lane b)).countP event ≤ (X.objects l).countP (tagged b) := by
    apply countP_le_of_records (fun k => ident (lane b,k))
    · intro i j _ _ h
      have := congrArg (fun r : Ref => r.issuer.2) h
      simpa only [issuer] using this
    · intro k hk
      obtain ⟨e,he,hy⟩ := (mem_indicesP_iff _ _ _).mp hk
      obtain ⟨r,hr,hi,hc⟩ := receipt b k e he hy
      exact ⟨r,hr,hi,by simp [tagged,hc,hi,issuer]⟩
  apply (Finset.sum_le_sum fun b _ => bounds b).trans
  apply PairTmaRing.sum_countP_le
  · intro r _ a b ha hb
    simp only [tagged,Bool.and_eq_true,beq_iff_eq] at ha hb
    exact hinj (ha.2.symm.trans hb.2)
  · intro r _ b h
    simp only [tagged,Bool.and_eq_true] at h
    exact h.1

variable {L : Launch} {K : Kernel} {A : List Assumption} {m : Mem0} {X : Execution}
  {S : SingleTmaRing.Slot} {sc : MbarScope} {n : Nat}

theorem arrivals_recorded (hX : Consistent L K A m X) (H : SingleTmaRing.Hyp L K A X S sc)
    (fits : S.Fits) (lane : Fin n → Nat) (hinj : Function.Injective lane) :
    ∑ b, arrivals S.full (X.tr (lane b)) ≤ arrivalUnits (X.objects S.full) := by
  rw [arrivalUnits_eq_length (fun _ hr _ _ _ ha => (SingleTmaRing.arrival_source H hr ha).1),
    ← List.countP_eq_length_filter]
  apply receipts lane hinj (arrivesOn S.full) countedArrive Ref.thread (fun _ => rfl)
  intro b k e he hm
  rcases e with ⟨pc,kind⟩
  cases kind with
  | arrive l tx cnt rel sc =>
    obtain rfl : l = S.full := by simpa [arrivesOn,sourceArrive] using hm
    have act : objectAction X X.async S.full (.thread (lane b,k)) = some (.arrive cnt tx) := by
      simp [objectAction,he]
    obtain ⟨r,hr,hid⟩ := (hX.tma.2.2.1 S.full).2.2 _ _ act
    have ha := ((hX.tma.2.2.1 S.full).2.1 r hr).1
    rw [hid,act] at ha
    exact ⟨r,hr,hid,countedArrive_iff.mpr
      ⟨SingleTmaRing.fault_free hX H fits (.inl rfl) hr,_,_,(Option.some.inj ha).symm⟩⟩
  | _ => simp [arrivesOn,sourceArrive] at hm

theorem copies_recorded (hX : Consistent L K A m X) (H : SingleTmaRing.Hyp L K A X S sc)
    (fits : S.Fits) (lane : Fin n → Nat) (hinj : Function.Injective lane)
    (hall : ¬ Descent.Obl L X .tensor) :
    ∑ b, (X.tr (lane b)).countP (issuesTo S.full) ≤ completedTxCount (X.objects S.full) := by
  classical
  have delivered : ∀ i a sp, X.TensorIssue i a sp →
      ∃ obs, X.tensor i = some obs ∧ obs.effects.notified = true := Classical.not_not.mp hall
  apply receipts lane hinj (issuesTo S.full) _ (fun i => .async i (.notify .load)) (fun _ => rfl)
  rintro b k ⟨pc,kind⟩ he hm
  cases kind with
  | tensorIssue a sp =>
    have hl : sp.mbar = S.full := by simpa [issuesTo] using hm
    obtain ⟨obs,hobs,notified⟩ := delivered _ _ _ ⟨pc,he⟩
    have act : objectAction X X.async S.full (.async (lane b,k) (.notify .load)) =
        some (.completeTx (TensorTransfer.bytes sp.descriptor)) := by
      simp [objectAction,he,hobs,notified,hl]
    obtain ⟨r,hr,hid⟩ := (hX.tma.2.2.1 S.full).2.2 _ _ act
    have ha := ((hX.tma.2.2.1 S.full).2.1 r hr).1
    rw [hid,act] at ha
    refine ⟨r,hr,hid,?_⟩
    rw [(Option.some.inj ha).symm,SingleTmaRing.fault_free hX H fits (.inl rfl) hr]
  | _ => simp [issuesTo] at hm

theorem ready_short (hX : Consistent L K A m X) (H : SingleTmaRing.Hyp L K A X S sc)
    (fits : S.Fits) {st : State}
    (hs : stateBefore (X.objects S.full) (X.objects S.full).length = some st) :
    arrivalUnits (X.objects S.full) = st.phase ∨
      completedTxCount (X.objects S.full) < S.n * (st.phase + 1) := by
  have hc := SingleTmaRing.completions_le hX H fits le_rfl hs
  rw [List.take_length] at hc
  exact (MbarRing.Blocker.tx_short (X.objects_checked hX S.full) H.full_noInval hs
    (PairTmaRing.expected_of_init hX H.full_init H.full_noInval hs)
    (SingleTmaRing.full_expected_bytes H _ fun _ h => h)
    (fun r hr hf n hn => SingleTmaRing.full_uniform H r hr n hn hf) hc
    (SingleTmaRing.full_noIncrement H)).imp_right And.right

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
