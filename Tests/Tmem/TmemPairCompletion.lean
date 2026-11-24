-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases

namespace PTX.Tests.TmemPairCompletion
open Tmem.Pair
noncomputable section
set_option maxHeartbeats 0

private def L : Launch := {grid := 2,block := 32,clusterSize := 2,params := fun _=>none}
private def action : Nat → Tmem.Action
  | 0 => .alloc 32 0
  | 1 => .relinquish
  | _ => .dealloc 0 32
private def ev (n : Nat) : Event := ⟨n,.tc (.resource .two none (action n).request)⟩
private def w (cta n : Nat) : WarpRequest := ⟨cta,0,fun _=>n,n,none,(action n).request⟩
private def ent (cta n : Nat) : Requests := ⟨w cta n,.two,action n⟩
private def source : Execution := {
  tr := fun _=>[ev 0,ev 1,ev 2],rf := fun _ _=>none}
private def full : Execution := {source with
  tmemHistory := fun cta=>if cta<2 then [ent cta 0,ent cta 1,ent cta 2] else []
  tmemPairing := [(w 0 0,w 1 0),(w 0 1,w 1 1),(w 0 2,w 1 2)]}
private def skipped : Execution := {source with
  tmemHistory := fun cta=>if cta<2 then [ent cta 0,ent cta 2] else []
  tmemPairing := [(w 0 0,w 1 0),(w 0 2,w 1 2)]}

/-- Every actual warp request of these traces is one of the three operations of its CTA. -/
private theorem valid_eq {X : Execution} (htr : X.tr = source.tr) {v : WarpRequest}
    {g : CtaGroup} (hv : v.Valid L X g) : ∃ n<3, v = w v.cta n := by
  obtain ⟨-,hwarp,hget,k,hk⟩ := hv
  have hw0 : v.warp = 0 := by simp only [L] at hwarp; omega
  have hidx : ∀ lane, v.indices lane = k := by
    intro lane
    obtain ⟨⟨ev',he,_⟩,hcount⟩ := hk lane
    simp only [Execution.get,htr,source,WarpRequest.event] at he hcount
    have hlt := (List.getElem?_eq_some_iff.mp he).1
    simp only [List.length_cons,List.length_nil] at hlt
    generalize v.indices lane = i at hlt hcount ⊢
    have hi3 : i<3 := by omega
    have hc : ((([ev 0,ev 1,ev 2] : List Event).take i).countP isTcColl)=i := by
      interval_cases i <;> rfl
    omega
  have he := hget 0
  simp only [Execution.get,htr,source,WarpRequest.event,hidx] at he
  have hlt := (List.getElem?_eq_some_iff.mp he).1
  simp only [List.length_cons,List.length_nil] at hlt
  refine ⟨k,by omega,?_⟩
  obtain ⟨cta,warp,indices,pc,dst,request⟩ := v
  simp only at hw0 hidx he ⊢
  subst hw0
  have hi : indices = fun _ => k := funext hidx
  subst hi
  interval_cases k <;> cases he <;> rfl

private theorem wvalid {X : Execution} (htr : X.tr = source.tr) (cta n : Nat) (hc : cta<2)
    (hn : n<3) : (w cta n).Valid L X .two := by
  refine ⟨show cta<2 from hc,by simp [w,L],fun lane=>?_,n,fun lane=>?_⟩
  · simp only [Execution.get,htr,source,WarpRequest.event,w]
    interval_cases n <;> rfl
  · refine ⟨⟨ev n,?_,rfl⟩,?_⟩
    · simp only [Execution.get,htr,source,WarpRequest.event,w]
      interval_cases n <;> rfl
    · simp only [htr,source,WarpRequest.event,w]
      interval_cases n <;> rfl

private theorem covered_full (g n : Nat) (hg : g<64) (hn : n<3) : Covered L full (g,n) := by
  refine ⟨[w 0 n,w 1 n],.inr ⟨(w 0 n,w 1 n),?_,rfl⟩,?_⟩
  · change (w 0 n,w 1 n)∈[(w 0 0,w 1 0),(w 0 1,w 1 1),(w 0 2,w 1 2)]
    interval_cases n <;> simp
  · by_cases hlo : g<32
    · exact ⟨w 0 n,by simp,⟨g,hlo⟩,by simp [WarpRequest.event,w,L]⟩
    · refine ⟨w 1 n,by simp,⟨g-32,by omega⟩,?_⟩
      apply Prod.ext
      · change 1*32+0*32+(g-32)=g
        omega
      · rfl

/-- Complete records and pairings satisfy the prefix law: every earlier request of a warp of a
completed operation is covered. -/
example : CompletionClosed L full := by
  intro ws hws x hx v group hv hb i hp
  obtain ⟨lane,rfl⟩ := hp
  obtain ⟨n,hn,hvn⟩ := valid_eq rfl hv
  have hcta := hv.1
  rw [hvn]
  have hlt : (WarpRequest.event L (w v.cta n) lane).1<64 := by
    simp only [WarpRequest.event,w,L] at hcta ⊢
    omega
  exact covered_full _ n hlt hn

/-- Different action kinds are in scope; permit relinquishment is ordered before later
deallocation without an action-equality or lifetime-equality premise. -/
example : (w 0 1).Before (w 0 2) := by
  simp [WarpRequest.Before,w]
example : (ent 0 1).action≠(ent 0 2).action := by decide

/-- A CTA's allocator cannot skip its warp's actual intermediate relinquishment: the warp has
returned from it, so its CTA's allocator has performed it (DEP-TMEM-ALLOC-WAIT), although its
peer-wait choice is false. -/
example : ¬Tmem.Pair.Blocking L skipped := by
  intro h
  obtain ⟨cta,x,hx,l,he⟩ := h.performed (i := (0,1)) (pc := 1) (group := .two) (dst := none)
    (request := .relinquish) rfl (by decide)
  have hc : cta<2 := by
    by_contra hc
    simp only [skipped, ite_eq_right hc, List.not_mem_nil] at hx
  have hx' : x∈[ent cta 0,ent cta 2] := by simpa only [skipped, ite_eq_left hc] using hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx'
  have h2 := congrArg Prod.snd he
  rcases hx' with rfl|rfl <;> simp [WarpRequest.event,ent,w] at h2
example : skipped.tmemPairBlocks (0,1)=false := rfl

/-- Issued requests alone do not force any record or peer barrier. -/
example : CompletionClosed L source := by
  intro ws hws
  rcases hws with ⟨_,_,hr,_⟩|⟨_,hq,_⟩
  · cases hr
  · cases hq

/-- A different warp or CTA is outside the Before domain. -/
example : ¬(w 0 1).Before {w 0 2 with warp:=1} := by
  simp [WarpRequest.Before,w]
example : ¬(w 0 1).Before (w 1 2) := by
  simp [WarpRequest.Before,w]

/-- Every lane matters; a representative lane cannot hide a later source
position in another lane. -/
example : ¬({w 0 1 with indices:=fun lane=>if lane.val=0 then 1 else 3}).Before (w 0 2) := by
  intro h
  have hh := h.2.2 ⟨1,by decide⟩
  change 3<2 at hh
  omega
end
end PTX.Tests.TmemPairCompletion
