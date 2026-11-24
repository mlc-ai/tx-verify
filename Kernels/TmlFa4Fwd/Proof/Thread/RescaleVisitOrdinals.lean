-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleBodyOrdinals
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import all Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
import all Kernels.TmlFa4Fwd.Proof.WarpOrdinals
import Lemmas.Flow.VoteSeq
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow

private theorem noVote (e : Event) (h : isTcColl e = true) : isFullWarpVote e = false := by
  obtain ⟨_,k⟩ := e
  cases k with
  | tc op => cases op <;> rfl
  | _ => cases h

private theorem noBar (id : Nat) (e : Event) (h : isTcColl e = true) :
    Execution.isBarId id e = false := by
  obtain ⟨_,k⟩ := e
  cases k with
  | tc op => cases op <;> rfl
  | _ => cases h

private theorem joinOrdinal {X : Execution} {g i site group : Nat}
    (h : X.get (g,i) = some ⟨site,.bar group (some 64) .sync⟩) (id : Nat) :
    ((X.tr g).take (i+1)).countP (Execution.isBarId id) =
      ((X.tr g).take i).countP (Execution.isBarId id) + (if id = group then 1 else 0) := by
  by_cases eq : id = group
  · subst id
    rw [ite_eq_left (rfl : group = group)]
    exact countP_take_succ h (by simp [Execution.isBarId])
  · rw [ite_eq_right eq,Nat.add_zero]
    exact countP_take_succ_false h (by simp [Execution.isBarId,Ne.symm eq])

private theorem afterArrivals {X : Execution} {g s : Nat} {test : Event → Bool}
    {credit reuse : Loc} (a : X.Arrive (g,s) credit 0 1 true .cta)
    (b : X.Arrive (g,s+1) reuse 0 1 true .cta)
    (off : ∀ pc obj, test ⟨pc,.arrive obj 0 1 true .cta⟩ = false) :
    ((X.tr g).take (s+2)).countP test = ((X.tr g).take s).countP test := by
  obtain ⟨_,ha⟩ := a
  obtain ⟨_,hb⟩ := b
  exact (countP_take_succ_false hb (off _ _)).trans (countP_take_succ_false ha (off _ _))

/-- A rescale stage issues a join, a scalar read, a ballot, its tensor body
and two mbarrier arrivals. Only the CTA join advances a named-barrier ordinal. -/
theorem rescaleVisitCounts {X : Execution} {g i k s endPos n group : Nat}
    {site rdSite voteSite : Nat} {r : Acc} {bs : List (Option Byte)} {hit : Bool} {word : BitVec 32}
    {credit reuse : Loc} (join : X.get (g,i) = some ⟨site,.bar group (some 64) .sync⟩)
    (read : X.get (g,i+1) = some ⟨rdSite,.rd r bs⟩)
    (vote : X.get (g,k) = some ⟨voteSite,.vote (2^32-1) hit word⟩)
    (a : X.Arrive (g,s) credit 0 1 true .cta) (b : X.Arrive (g,s+1) reuse 0 1 true .cta)
    (pVote : k = i+2) (pBody : s = k+1+n) (pEnd : endPos = s+2)
    (tensor : ((X.tr g).take s).countP isTcColl = ((X.tr g).take (k+1)).countP isTcColl+n) :
    ((X.tr g).take endPos).countP isTcColl = ((X.tr g).take i).countP isTcColl+n ∧
    ((X.tr g).take endPos).countP isFullWarpVote = ((X.tr g).take i).countP isFullWarpVote+1 ∧
    ∀ id, ((X.tr g).take endPos).countP (Execution.isBarId id) =
      ((X.tr g).take i).countP (Execution.isBarId id) + (if id = group then 1 else 0) := by
  let count (test : Event → Bool) (j : Nat) := ((X.tr g).take j).countP test
  have suffix (test : Event → Bool) (off : ∀ pc obj, test ⟨pc,.arrive obj 0 1 true .cta⟩ = false) :
      count test endPos = count test s :=
    (congrArg (count test) pEnd).trans (afterArrivals a b off)
  have body (test : Event → Bool) (disj : ∀ e, isTcColl e = true → test e = false) :
      count test s = count test (k+1) := by
    have tc : count isTcColl (k+1+n) = count isTcColl (k+1)+n :=
      (congrArg (count isTcColl) pBody.symm).trans tensor
    exact (congrArg (count test) pBody).trans (rescaleBodyCountUnchanged disj tc)
  have beforeVote (test : Event → Bool)
      (off : test ⟨rdSite,.rd r bs⟩ = false) : count test k = count test (i+1) :=
    (congrArg (count test) pVote).trans (countP_take_succ_false read off)
  have tc : count isTcColl (k+1) = count isTcColl i :=
    (countP_take_succ_false (p := isTcColl) vote rfl).trans
      ((beforeVote isTcColl rfl).trans (countP_take_succ_false join rfl))
  have vp := (beforeVote isFullWarpVote rfl).trans (countP_take_succ_false join rfl)
  refine ⟨(suffix isTcColl (fun _ _ => rfl)).trans (tensor.trans (congrArg (·+n) tc)),?_,?_⟩
  · exact (suffix isFullWarpVote (fun _ _ => rfl)).trans ((body isFullWarpVote noVote).trans
      ((countP_take_ballot vote).trans (congrArg (·+1) vp)))
  · intro id
    let test := Execution.isBarId id
    exact (suffix test (fun _ _ => rfl)).trans ((body test (noBar id)).trans
      ((countP_take_succ_false (p := test) vote rfl).trans
        ((beforeVote test rfl).trans (joinOrdinal join id))))

end PTX.Kernels.TmlFa4Fwd.Correction
