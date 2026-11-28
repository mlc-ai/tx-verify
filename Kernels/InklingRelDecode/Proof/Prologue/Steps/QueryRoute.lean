-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.QuerySkip
import Lemmas.Flow.Step.GuardedLoadU
import Lemmas.Flow.CtlStepsU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

private def choose (g : Nat) (a b c d : Bool) : Nat :=
  if g ≤ 0 && a then 0 else if g ≤ 1 && b then 16 else if g ≤ 2 && c then 32
  else if g ≤ 3 && d then 48 else 64

private def mask (a b c d : Bool) : Nat → Bool
  | 0 => a | 1 => b | 2 => c | _ => d

private theorem bounds : ∀ (g : Fin 5) (a b c d : Bool),
    let z := choose g a b c d
    16*g.val ≤ z ∧ z ≤ 64 ∧
    (∀ n : Fin 64, 16*g.val ≤ n.val → n.val < z → mask a b c d (n.val/16) = false) ∧
    (z < 64 → mask a b c d (z/16) = true) := by decide +kernel

private noncomputable def queryIndex (t group : Nat) (d : D) := choose group
  (queryOn t 0 d) (queryOn t 1 d) (queryOn t 2 d) (queryOn t 3 d)

private theorem to_site (t group : Nat) (d : D) : querySite t d group =
    qSiteAt (queryIndex t group d) := by
  unfold querySite qSiteAt queryIndex choose
  split_ifs <;> first | rfl | omega

private theorem mask_val (t n : Nat) (d : D) (hn : n<64) :
    mask (queryOn t 0 d) (queryOn t 1 d) (queryOn t 2 d) (queryOn t 3 d) (n/16) =
      queryOn t (n/16) d := by
  have h : n/16=0 ∨ n/16=1 ∨ n/16=2 ∨ n/16=3 := by omega
  rcases h with h|h|h|h <;> rw [h] <;> rfl

theorem query_route {Q L g w d} (group : Fin 5) :
    let t := g%L.block
    let s := querySite t d group.val
    SegU kernel Assumptions.all L g (qSiteAt (16*group.val)).pc
      (facts Q L g w d (qSiteAt (16*group.val)).pc) s.pc (facts Q L g w d s.pc) ∧
      Inv t {d with site := s} ∧ s.sub = 0 := by
  intro t s
  let z := queryIndex t group.val d
  obtain ⟨lo,hi,off,on⟩ := bounds group (queryOn t 0 d) (queryOn t 1 d)
    (queryOn t 2 d) (queryOn t 3 d)
  change 16*group.val ≤ z at lo
  change z ≤ 64 at hi
  dsimp only [s]
  rw [to_site]
  refine ⟨skip_queries lo hi (fun n hn lt => ?_),?_⟩
  · have small : n < 64 := by omega
    exact (mask_val t n d small).symm.trans (off ⟨n,small⟩ hn lt)
  · change Inv t {d with site := qSiteAt z} ∧ (qSiteAt z).sub = 0
    unfold qSiteAt
    split_ifs with small
    · exact ⟨(mask_val t z d small).symm.trans (on small),rfl⟩
    · exact ⟨trivial,rfl⟩

private theorem boundary {j : Fin 64} (last : j.val%16=15) (t : Nat) (d : D) :
    afterQuery d t j = querySite t d ((j.val+1)/16) := by
  unfold afterQuery
  split_ifs with h k
  · rfl
  · omega
  · have eq : (j.val+1)/16=4 := by omega
    rw [eq]; rfl

theorem step_query_boundary {Q L g w} (d : D) (j : Fin 64) (hs : d.site = .ldq j)
    (last : j.val%16=15) : (code Q L g w).StepAtU d := by
  obtain ⟨s,a,b,c,won,bcast⟩ := d
  cases hs
  let d : D := ⟨.ldq j,a,b,c,won,bcast⟩
  let group : Fin 5 := ⟨(j.val+1)/16,by omega⟩
  let s := querySite (g%L.block) d group
  let dn := {d with site := s}
  obtain ⟨route,inv,sub⟩ := query_route (Q := Q) (L := L) (g := g) (w := w) (d := d) group
  have eq : 16*group.val=j.val+1 := by dsimp [group]; omega
  rw [eq] at route
  have prove (hi : Inv (g%L.block) d) : (code Q L g w).StepAtU d := by
    apply Code.guardedLoadU (C := code Q L g w) (d := d) (dn := dn)
      (qLoadPair (L := L) (g := g) j).2 rfl _ rfl rfl rfl rfl rfl rfl sub rfl _ inv _
      ((after_query_cross j).comp route)
    · apply Code.guardTrue_factsFrom (query_live j)
      rw [query_value,show queryOn _ _ d = true from hi]
      rfl
    · intro ac bs
      change some (some {d with site := afterQuery d _ j}) = _
      rw [boundary last]
    · change qDst j ∉ (factsFrom _ _).map Prod.fst
      rw [factsFrom_keys]
      exact fun h => Bool.noConfusion ((query_data j).symm.trans (List.mem_filter.mp h).2)
  exact ⟨fun hi => (prove hi).site hi,fun ins ht hi => (prove hi).step ins ht hi⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
