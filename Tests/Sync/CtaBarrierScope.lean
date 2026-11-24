-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.JointWaits
public import Mathlib.Tactic

/-! Named CTA barrier IDs and generations are local to one CTA bank. These
regressions use actual source/resource identities and checked record provenance;
matching numeric keys cannot manufacture dependencies between different CTAs. -/
namespace PTX.Tests.CtaBarrierScope
open PTX CtaBarrier

private theorem key_present {L : Launch} {X : Execution} {e : EvId} {key : Nat}
    (hk : CtaBarK L X e key) : ∃ev,X.get e=some ev := by
  obtain ⟨count,pc,hget⟩ := hk.2.1
  exact ⟨_,hget⟩

/-- Same-CTA arrivals at a real common resource generation retain their legal
issue-to-return dependency, including explicitly counted named barriers. -/
theorem same_cta_key_wait {L : Launch} {X : Execution} {e f : EvId} {key : Nat}
    (hc : SameCta L e.1 f.1) (he : CtaBarK L X e key) (hf : CtaBarK L X f key) :
    CtaBarWaits L X e f false true :=
  ⟨key_present he,key_present hf,
    .inr (.inl ⟨rfl,rfl,hc,key,⟨he.1,(let ⟨c,pc,h⟩ := he.2.1; ⟨c,pc,_,h⟩),he.2.2⟩,hf⟩)⟩

/-- Different CTA keys do not create the key-matching waiting branch. -/
theorem different_cta_no_key_branch {L : Launch} {X : Execution} {e f : EvId}
    (hc : e.1/L.block≠f.1/L.block) :
    ¬(SameCta L e.1 f.1 ∧ ∃key,CtaBarK L X e key ∧ CtaBarK L X f key) := by
  rintro ⟨hs,_⟩
  exact hc hs.2.2

/-- Checked real records also exclude the other waiting branches: record-order
edges have false destinations, and a completion record belongs to its actual
receiver CTA. Thus even equal numeric keys cannot create any cross-CTA
issue-to-return dependency. -/
theorem different_cta_no_wait {L : Launch} {X : Execution} {e f : EvId} {key : Nat}
    (hh : CtaBarHistoryOk L X) (he : CtaBarK L X e key) (hf : CtaBarK L X f key)
    (hne : e.1/L.block≠f.1/L.block) : ¬CtaBarWaits L X e f false true := by
  intro hw
  have hb : 0<L.block := by
    by_contra hn
    have hz : L.block=0 := by omega
    have ht := hf.1
    simp only [Launch.threads,hz,Nat.mul_zero] at ht
    omega
  obtain ⟨count,pc,hebar⟩ := he.2.1
  rcases hw.2.2 with ⟨_,hfalse,_⟩ | ⟨_,_,hc,_⟩ | ⟨_,_,k,i,r,_,hr,her,_⟩
  · cases hfalse
  · exact hne hc.2.2
  · have hcta : f.1/L.block<L.grid := by
      by_contra hn
      rw [hh.1 _ (by omega)] at hr
      cases hr
    have hs := (hh.2 _ hcta).2.1 r (List.mem_of_getElem? hr)
    cases r with
    | exit g q =>
      have heq : e=q := by simpa only [Record.refs,List.mem_singleton] using her
      subst q
      obtain ⟨_,_,pc',hget⟩ := hs
      rw [hebar] at hget
      cases hget
    | arrival id warp n lanes =>
      obtain ⟨p,hp,hpe⟩ := List.mem_map.mp her
      have hsrc := hs p hp
      have htid : e.1=(f.1/L.block)*L.block+p.1 := by
        rw [←hpe]
        exact hsrc.2.1
      apply hne
      rw [htid,Nat.add_comm,Nat.add_mul_div_right _ _ hb,Nat.div_eq_of_lt hsrc.1,Nat.zero_add]

end PTX.Tests.CtaBarrierScope
