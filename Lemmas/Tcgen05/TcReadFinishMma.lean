-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.MmaFinish
public import Lemmas.Tmem.TmemStore
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Tcgen05.TcFence
public import Core.Assembly.Execution

@[expose] public section

/-! Finishing an unobserved shared-input MMA preserves old TMEM load values.
Observed result ancestry is closed under accumulator pipelines by actual commit
tracking, including every recursive accumulation source. -/
namespace PTX.TcMma
open AsyncCopy
noncomputable section

/-- Actual source programs may elect one MMA issuing thread in each warp. -/
def WarpIssuerUnique (L : Launch) (X : Execution) : Prop :=
  ∀ {i j : EvId}, (∃d s acc mask,X.MmaIssue i d s acc mask) →
    (∃d s acc mask,X.MmaIssue j d s acc mask) → SameWarp L i.1 j.1 → i.1=j.1

/-- A delivered commit tracks the MMA. -/
def HasObservation (X : Execution) (i : EvId) : Prop :=
  ∃commit rank,TracksMma X i commit ∧ rank ∈ X.tcNotified commit

 theorem Result.actual_issue {L : Launch} {A : List Assumption} {X : Execution}
    {i : EvId} {cell : Cell} {value : Value} (h : Result L A X i cell value) :
    ∃d s acc mask,X.MmaIssue i d s acc mask := by
  cases h with
  | overwrite hi _ _ _ => exact ⟨_,_,_,_,hi⟩
  | accumulate hi _ _ _ _ _ => exact ⟨_,_,_,_,hi⟩
  | accumulateStored hi _ _ _ _ _ => exact ⟨_,_,_,_,hi⟩

 theorem HasObservation.done {X : Execution} (hc : CommitOk X) {i : EvId}
    (h : HasObservation X i) : X.async.mmaDone i=true := by
  obtain ⟨commit,rank,htrack,hnotify⟩ := h
  exact (hc commit rank hnotify).2 i htrack

/-- A pipeline predecessor of an observed MMA is tracked by the very same
commit. A completed predecessor may instead use its own observed commit. -/
 theorem observed_acc_predecessor {L : Launch} {X : Execution}
    (hu : WarpIssuerUnique L X) (ha : ∀ n, ¬ Relation.TransGen (TcStep L X) n n)
    {source consumer : EvId}
    (hs : ∃d s acc mask,X.MmaIssue source d s acc mask)
    (hc : ∃d s acc mask,X.MmaIssue consumer d s acc mask)
    (hb : WriteBefore L X source consumer) (ho : HasObservation X consumer) :
    HasObservation X source := by
  obtain ⟨d,s,acc,mask,hissue⟩ := hs
  rcases hb.of_mma hissue with hd | ⟨hwarp,horder,_⟩
  · exact hd.tracked
  · have hthread := hu ⟨d,s,acc,mask,hissue⟩ hc hwarp
    have hindex := tcStep_same_thread ha horder.tcStep hthread (by
      obtain ⟨_, _, _, _, pc, hp⟩ := hc
      simp [hp, Event.acc])
    obtain ⟨commit,rank,htrack,hnotify⟩ := ho
    refine ⟨commit,rank,?_,hnotify⟩
    exact ⟨hthread.trans htrack.1,lt_trans hindex htrack.2.1,
      .inl ⟨d,s,acc,mask,hissue⟩,htrack.2.2.2⟩

variable {L : Launch} {A : List Assumption} {X : Execution} {i : EvId}
  {values : MmaOperands} {ra rb : Nat → Option Ref}
local notation "Y" => X.finishMma i values ra rb

 theorem finishMma_cpValue {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d s acc mask) {source : EvId} {cell : Cell} {value : Value} :
    CpValue Y source cell value ↔ CpValue X source cell value := by
  have hnot : ∀ c,¬X.CpIssue i c := by
    intro c hcp
    obtain ⟨pc,he⟩ := hi
    obtain ⟨pc',he'⟩ := hcp
    rw [he] at he'
    cases he'
  by_cases hsource : source=i
  · subst source
    constructor <;> rintro ⟨c,_,_,_,_,_,_,hcp,_⟩
    all_goals exact (hnot c hcp).elim
  · simp only [CpValue,Execution.finishMma,ite_eq_right hsource]
    rfl

/-- Reflect the whole result derivation. Every recursive source receives an
actual completion observation, rather than merely excluding the root source. -/
 theorem Result.of_finishMma_observed (hu : WarpIssuerUnique L X)
    (ha : ∀ n, ¬ Relation.TransGen (TcStep L X) n n) (hc : CommitOk X)
    (hn : X.async.mmaDone i=false)
    {source : EvId} {cell : Cell} {value : Value}
    (h : Result L A Y source cell value) (ho : HasObservation X source) :
    Result L A X source cell value := by
  induction h with
  | @overwrite j d s mask row col cell operands value hi hp hr hv =>
    have hne : j≠i := by
      intro heq
      subst j
      have hd := ho.done hc
      rw [hn] at hd
      cases hd
    exact .overwrite hi hp (by simpa only [Execution.finishMma,ite_eq_right hne] using hr) hv
  | @accumulate j d s mask row col cell operands value source old hi hp hr prev hs hv ih =>
    have hne : j≠i := by
      intro heq
      subst j
      have hd := ho.done hc
      rw [hn] at hd
      cases hd
    have hsource := observed_acc_predecessor hu ha prev.actual_issue
      ⟨d,s,true,mask,hi⟩ hs.2.2.1 ho
    exact .accumulate hi hp (by simpa only [Execution.finishMma,ite_eq_right hne] using hr)
      (ih hsource) hs hv
  | @accumulateStored j d s mask row col cell operands value source old hi hp hr prev hs hv =>
    have hne : j≠i := by
      intro heq
      subst j
      have hd := ho.done hc
      rw [hn] at hd
      cases hd
    exact .accumulateStored hi hp (by simpa only [Execution.finishMma,ite_eq_right hne] using hr)
      prev hs hv

 theorem shift_not_mmaIssue {x : EvId} {t : TcShift.Spec} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} (hs : X.ShiftIssue x t) (hm : X.MmaIssue x d s acc mask) :
    False := by
  obtain ⟨pc, hp⟩ := hm
  obtain ⟨pc', hq⟩ := hs
  rw [hp] at hq; cases hq

/-- A result ordered before a consumer that is not an MMA is ordered by observed completion,
so it reflects through the finish of an unobserved MMA. -/
 theorem Result.of_finishMma_before (hu : WarpIssuerUnique L X)
    (ha : ∀ n, ¬ Relation.TransGen (TcStep L X) n n) (hc : CommitOk X)
    (hn : X.async.mmaDone i=false) {source consumer : EvId} {cell : Cell} {value : Value}
    (h : Result L A Y source cell value) (hb : WriteBefore L X source consumer)
    (hcons : ∀ d s acc mask, ¬ X.MmaIssue consumer d s acc mask) :
    Result L A X source cell value := by
  obtain ⟨d,s,acc,mask,hissue⟩ := h.actual_issue
  rcases WriteBefore.of_mma hissue hb with hd | hp
  · exact h.of_finishMma_observed hu ha hc hn hd.tracked
  · obtain ⟨-, -, d₁, s₁, a₁, m₁, d₂, s₂, a₂, m₂, -, hy, -⟩ := hp
    exact (hcons _ _ _ _ hy).elim

 theorem Wrote.of_finishMma {K : Kernel} {mem0 : Mem0} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X)
    (hu : WarpIssuerUnique L X) (hi : X.MmaIssue i d s acc mask) (hn : X.async.mmaDone i=false)
    {source consumer : EvId} {cell : Cell} {value : Value}
    (hw : Wrote L A Y source cell value) (hb : WriteBefore L X source consumer)
    (hcons : ∀ d s acc mask, ¬ X.MmaIssue consumer d s acc mask) :
    Wrote L A X source cell value := by
  rcases hw with hr | hstore | hcopy | ⟨src, from', ⟨hsc, hsrc, hrd, hrs⟩, hval⟩
  · exact .inl (hr.of_finishMma_before hu (tcStep_acyclic hX hg) hX.tcCommit hn hb hcons)
  · exact .inr (.inl hstore)
  · exact .inr (.inr (.inl ((finishMma_cpValue hi).mp hcopy)))
  · refine .inr (.inr (.inr ⟨src, from', ⟨hsc, hsrc, hrd, hrs⟩, ?_⟩))
    obtain ⟨t, hshift, -⟩ := hsc
    have hcons' : ∀ d s acc mask, ¬ X.MmaIssue source d s acc mask :=
      fun d s acc mask hm => shift_not_mmaIssue hshift hm
    rcases hval with hr | hst | hcp
    · exact .inl (hr.of_finishMma_before hu (tcStep_acyclic hX hg) hX.tcCommit hn hrs.2.2.1 hcons')
    · exact .inr (.inl hst)
    · exact .inr (.inr ((finishMma_cpValue hi).mp hcp))

 theorem readOk_finishMma_shared {K : Kernel} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X) (hu : WarpIssuerUnique L X)
    (hshared : ∀j d s acc mask,X.MmaIssue j d s acc mask → s.aTmem=none)
    {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d s acc mask) (hn : X.async.mmaDone i=false) : ReadOk L A Y := by
  constructor
  · intro load address vals sh j source cell value hl hc hs hw
    have hcons : ∀ d s acc mask, ¬ X.MmaIssue load d s acc mask :=
      fun d s acc mask hm => tld_not_mmaIssue hl hm
    exact hX.tcRead.1 load address vals sh j source cell value hl hc hs
      (hw.of_finishMma hX hg hu hi hn hs.2.2.1 hcons)
  · intro mma index cell pos source value operands hs _ _ _ _
    obtain ⟨d',s',acc',mask',hissue,hcell⟩ := hs
    have hnone := hshared mma d' s' acc' mask' hissue
    simp only [aCell,hnone,Option.bind_none,reduceCtorEq] at hcell

end
end PTX.TcMma
