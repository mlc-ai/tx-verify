-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.CtaBarrier.CtaBarrierGeneration
public import Lemmas.CtaBarrier.CtaBarrierExecution

@[expose] public section

namespace PTX.CtaBarrier
variable {α : Type} [DecidableEq α]

/-- Unique history references give each source arrival exactly one resource ID
and generation. No source ordinal or fixed participant schedule is assumed. -/
theorem GenerationOf.unique {block id id' phase phase' : Nat} {h : List (Record α)} {e : α}
    (hnd : (h.flatMap Record.refs).Nodup)
    (he : GenerationOf block h e id phase) (hf : GenerationOf block h e id' phase') :
    id = id' ∧ phase = phase' := by
  obtain ⟨i,s,warp,count,lanes,g,hi,hs,hm,hphase,t,ht⟩ := he
  obtain ⟨j,u,warp',count',lanes',g',hj,hu,hm',hphase',t',ht'⟩ := hf
  have heRef : e ∈ (Record.arrival id warp count lanes).refs := List.mem_map.mpr ⟨(g,e),hm,rfl⟩
  have hfRef : e ∈ (Record.arrival id' warp' count' lanes').refs :=
    List.mem_map.mpr ⟨(g',e),hm',rfl⟩
  have heq : i = j := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hij | hji
    · exact Nat.lt_irrefl _ (refs_index_lt hnd hi hj hij heRef hfRef)
    · exact Nat.lt_irrefl _ (refs_index_lt hnd hj hi hji hfRef heRef)
  subst j
  have hrec := Option.some.inj (hi.symm.trans hj)
  cases hrec
  have hstate : s = u := Except.ok.inj (hs.symm.trans hu)
  subst u
  exact ⟨rfl,hphase.symm.trans hphase'⟩

end PTX.CtaBarrier

namespace PTX

/-- One checked source arrival has one actual key, even after other resources
are updated. This is an identity theorem about resource records. -/
theorem CtaBarK.key_unique {L : Launch} {X : Execution} {e : EvId} {key key' : Nat}
    (hh : CtaBarHistoryOk L X) (hk : CtaBarK L X e key) (hk' : CtaBarK L X e key') :
    key = key' := by
  have hb : 0 < L.block := by
    have hg := hk.1
    unfold Launch.threads at hg
    by_contra hn
    have hz : L.block = 0 := by omega
    rw [hz,Nat.mul_zero] at hg
    omega
  have hc : e.1/L.block < L.grid := (Nat.div_lt_iff_lt_mul hb).mpr hk.1
  obtain ⟨hmod,hdiv⟩ := CtaBarrier.GenerationOf.unique (hh.2 _ hc).1 hk.2.2 hk'.2.2
  omega

end PTX
