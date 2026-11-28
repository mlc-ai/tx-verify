-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.Receipts

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow PTX.SingleTmaRing
open PTX.MBarrier hiding okPolls

/-- A recorded ready arrival of use past the waiter's ordinal would already have
observed that ordinal's empty notification. This is excluded by the MMA warp count row. -/
theorem ready_phase {L K A m X S sc g} (hX : Consistent L K A m X) (H : Hyp L K A X S sc)
    (fits : S.Fits) (ahead : ∀ {k pc sp}, X.get (S.cm,k) = some ⟨pc,.tc (.commit sp)⟩ →
      sp.mbar = S.empty → ((X.tr S.cm).take k).countP (commitsTo S.empty) < okPolls S.full (X.tr g))
    {st : State} (hs : stateBefore (X.objects S.full) (X.objects S.full).length = some st) :
    st.phase ≤ okPolls S.full (X.tr g) + 1 := by
  classical
  let n := okPolls S.full (X.tr g)
  let kinds : Finset (SingleTmaRing.Kind S) := {⟨0,by omega⟩}
  let T := (SF X S).filter (fun x => x.1 ∈ kinds)
  have sub : T ⊆ kinds ×ˢ Finset.range (n+1) := by
    intro x hx
    obtain ⟨hmem,hkind⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_product.mpr ⟨hkind,Finset.mem_range.mpr ?_⟩
    by_contra! hlt
    have hguard := guardP H hmem (by omega : 1 ≤ n+1) hlt
    have hz : x.1.val = 0 := congrArg Fin.val (Finset.mem_singleton.mp hkind)
    rw [kOwner_of_zero hz] at hguard
    have present := MbarRing.Round.Slot.present_of_guard hguard
    obtain ⟨hy,_⟩ := (SingleTmaRing.ring hX H fits).observes_empty hX.depAcyclic
      (a := 0) (n := n) present 0
    obtain ⟨_,⟨_,sp,he,hm,_,hc⟩,_⟩ := SE_op H hy
    have hbad := ahead he hm
    dsimp only [cmE] at hc hbad
    rw [hc] at hbad
    exact Nat.lt_irrefl _ hbad
  have card := Finset.card_le_card sub
  simp only [Finset.card_product,kinds,Finset.card_singleton,Finset.card_range,one_mul] at card
  have units := MbarRing.Round.units_le_of_uses (X.objects_checked hX S.full)
    (fun x : SingleTmaRing.Kind S × Nat => itF X S x.1 x.2) T (i := (X.objects S.full).length)
    (fun k r a tx hk hf ha => (full_count H k r a tx hk hf ha).1)
    (fun k _ r a tx hk hf ha => (full_count H k r a tx hk hf ha).2)
  obtain ⟨pend,acc⟩ := ((X.objects_checked hX S.full).accounted H.full_noInval le_rfl).2 st hs
  have p := PairTmaRing.expected_of_init hX H.full_init H.full_noInval hs
  rw [p,full_noIncrement H] at pend acc
  change st.phase ≤ n + 1
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
