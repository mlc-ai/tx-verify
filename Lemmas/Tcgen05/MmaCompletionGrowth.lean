-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Tc.TcMmaCompletion
public import Lemmas.Tcgen05.MmaCompletionFrame

@[expose] public section

namespace PTX.TcMma
noncomputable section

private theorem get_of_growth_old {X Y : Execution} (hle : X.le Y) {i : EvId}
    (hi : i.2<(X.tr i.1).length) {ev : Event} (he : Y.get i=some ev) :
    X.get i=some ev := by
  obtain ⟨suffix,hs⟩ := hle.1 i.1
  change (Y.tr i.1)[i.2]?=some ev at he
  rw [←hs,List.getElem?_append_left hi] at he
  exact he

/-- Metadata-only updates preserve the completion domain exactly. This leaf
frame needs no complete-MMA implementation or extension machinery. -/
theorem completionClosed_of_trace {L : Launch} {X Y : Execution} (hx : CompletionClosed L X)
    (htr : X.tr=Y.tr) (hdone : Y.async.mmaDone=X.async.mmaDone) : CompletionClosed L Y := by
  intro i j hp hd
  have hiss (p d s a m) : X.MmaIssue p d s a m ↔ Y.MmaIssue p d s a m := by
    simp only [Execution.MmaIssue,Execution.get,htr]
  rw [hdone] at hd ⊢
  exact hx i j ((completionPrecedes_congr hiss).mpr hp) hd

/-- Every predecessor of an old completed source target is itself an old
actual source issue. New trace suffixes cannot add earlier same-source events. -/
theorem completionPrecedes_of_growth_old_target {L : Launch} {X Y : Execution} (hle : X.le Y)
    {i j : EvId} (hj : j.2<(X.tr j.1).length)
    (hp : CompletionPrecedes L Y i j) : CompletionPrecedes L X i j := by
  rw [completionPrecedes_iff] at hp ⊢
  obtain ⟨hg,hlt,hw,⟨d,s,a,m,d',s',a',m',hi,hj',hsa⟩,
    ⟨e,u,b,n,e',u',b',n',hi2,hj2,hrest⟩⟩ := hp
  have hib : i.2<(X.tr i.1).length := by rw [hg]; exact Nat.lt_trans hlt hj
  have hold {p : EvId} (hp : p.2<(X.tr p.1).length) {d s a m}
      (h : Y.MmaIssue p d s a m) : X.MmaIssue p d s a m := by
    obtain ⟨pc,he⟩ := h
    exact ⟨pc,get_of_growth_old hle hp he⟩
  exact ⟨hg,hlt,hw,⟨d,s,a,m,d',s',a',m',hold hib hi,hold hj hj',hsa⟩,
    ⟨e,u,b,n,e',u',b',n',hold hib hi2,hold hj hj2,hrest⟩⟩

/-- Full source growth with unchanged completion effects transports the law.
Existing async origin supplies the old target's real source index. This covers
all noncompletion extensions without classifying their new event or histories. -/
theorem completionClosed_of_growth {L : Launch} {X Y : Execution} (hle : X.le Y)
    (hdone : Y.async.mmaDone=X.async.mmaDone)
    (ht : AsyncCopy.TcEffectsOk X) (hX : CompletionClosed L X) : CompletionClosed L Y := by
  intro i j hp hd
  have hdold : X.async.mmaDone j=true := by rwa [hdone] at hd
  have hj : j.2<(X.tr j.1).length := by
    rcases ht.1 j (ht.2 j hdold) with ⟨d,s,a,m,ops,⟨pc,he⟩,_⟩ |
      ⟨c,ops,⟨pc,he⟩,_⟩ | ⟨s,ops,⟨pc,he⟩,_⟩ <;> exact (List.getElem?_eq_some_iff.mp he).1
  have hdi := hX i j (completionPrecedes_of_growth_old_target hle hj hp) hdold
  rwa [hdone]
end
end PTX.TcMma
