-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncOrigins
public import Lemmas.Cluster.ClusterBarrierExecution

@[expose] public section

/-! Returns of quiet instructions are waiting-graph sinks.

A quiet event (register request, warp barrier, election, shuffle, ballot, TMEM resource
request) has no independent asynchronous effect, no mbarrier-object action, no cluster-barrier
record, no memory access and no fence. The return of the last such event of a thread therefore has
no outgoing dependency, unless it is a register request already granted. Exact issuer provenance is
used: the coarse `Kind.isTma` classifier also includes register requests. -/

namespace PTX
open AsyncCopy
noncomputable section

/-- Kinds with no async, mbarrier-object or cluster-barrier effect. -/
def Kind.quiet : Kind → Bool
  | .setMaxReg .. | .warpBar .. | .elect .. | .shfl .. | .vote .. | .voteMode ..
  | .tc (.resource ..) => true
  | _ => false

section
variable {L : Launch} {X : Execution} {f : EvId} {pc : Nat} {k : Kind}

private theorem other_kind (hi : X.get f = some ⟨pc,k⟩) (hk : k.quiet = true) {pc' : Nat}
    {k' : Kind} (h : X.get f = some ⟨pc',k'⟩) (hk' : k'.quiet = false) : False := by
  rw [hi] at h
  cases h
  rw [hk] at hk'
  cases hk'

private theorem quiet_no_objectAction (hi : X.get f = some ⟨pc,k⟩) (hk : k.quiet = true)
    (m : Loc) : objectAction X X.async m (.thread f) = none := by
  simp only [objectAction,hi]
  cases k <;> simp_all [Kind.quiet]

private theorem quiet_no_object_before (ht : TmaOk X)
    (hi : X.get f = some ⟨pc,k⟩) (hk : k.quiet = true) (m : Loc) (target : Ref) :
    ¬ MBarrier.Before (X.objects m) (.thread f) target := by
  rintro ⟨a,b,ra,rb,ha,hid,_⟩
  obtain ⟨ho,-⟩ := ((ht.2.2.1 m).2.1 ra (List.mem_of_getElem? ha))
  rw [hid,quiet_no_objectAction hi hk] at ho
  cases ho

private theorem quiet_no_cluster (hcl : ClusterHistoryOk L X)
    (hi : X.get f = some ⟨pc,k⟩) (hk : k.quiet = true) {j : EvId} {b : Bool} :
    ¬ ClusterWaits L X f j true b := by
  have noRecord {c : Nat} {record : ClusterBarrier.Record EvId}
      (hr : record ∈ X.clusters c) (he : f ∈ record.refs) : False := by
    rcases hcl.ref_operation hr he with ⟨pc,op,hp⟩ | ⟨pc,hp⟩
    all_goals exact other_kind hi hk hp rfl
  rintro ⟨_,_,hh⟩
  rcases hh with ⟨c,i,j,record,q,hr,hq,hij,he,hf,_⟩ |
    ⟨hb,_⟩ | ⟨hb,_⟩ | ⟨hb,_⟩
  · exact noRecord (List.mem_of_getElem? hr) he
  all_goals cases hb

/-- A quiet event writes no memory byte: it is neither a store nor an atomic read-modify-write. -/
private theorem quiet_no_memWrites (hi : X.get f = some ⟨pc,k⟩) (hk : k.quiet = true)
    (a : Acc) (bs : List Byte) : ¬ X.MemWrites (.thread f) a bs := by
  rintro (⟨pc',hp⟩ | ⟨old,pc',hp⟩)
  all_goals exact other_kind hi hk hp rfl

/-- A quiet event is no thread fence. -/
private theorem quiet_no_threadFence (hi : X.get f = some ⟨pc,k⟩) (hk : k.quiet = true)
    (sem : FenceSem) (s : MbarScope) : ¬ X.ThreadFence f sem s := by
  rintro ⟨pc',hp⟩
  exact other_kind hi hk hp rfl

/-- A quiet event is the source of no release/acquire synchronization: it writes nothing. -/
private theorem quiet_no_sync (hi : X.get f = some ⟨pc,k⟩) (hk : k.quiet = true) (j : EvId) :
    ¬ synchronizesWith L X f j := by
  rintro ⟨a,b,bs,cs,hw,-,-,-,-,-,-,-,-,-⟩
  exact quiet_no_memWrites hi hk a bs hw

/-- A quiet event starts no fence synchronization: it is neither the release head of a pattern nor
a morally strong `fence.sc`. -/
private theorem quiet_no_fenceSync (hi : X.get f = some ⟨pc,k⟩) (hk : k.quiet = true)
    (j : EvId) : ¬ FenceSync L X f j := by
  rintro (⟨w,r,a,b,bs,cs,se,sf,hw,-,-,hhead,-⟩ | ⟨⟨s,s',hsc,-,-⟩,-⟩)
  · rcases hhead with ⟨rfl,-,-⟩ | ⟨sem,hf,-,-,-⟩
    · exact quiet_no_memWrites hi hk a bs hw
    · exact quiet_no_threadFence hi hk sem se hf
  · exact quiet_no_threadFence hi hk .sc s hsc

/-- A thread event's return starts no stage edge: stage edges start at asynchronous stages. -/
private theorem thread_no_stageOrder (v : AsyncCopy.Ref × Bool) :
    ¬ StageOrder X (.thread f, true) v := by
  rintro (⟨_,hb,_,_⟩ | ⟨_,_,hedge⟩)
  · cases hb
  · exact hedge

/-- A thread event's return starts no issue edge: issue edges start at a thread event's issue. -/
private theorem thread_no_issueStage (v : AsyncCopy.Ref × Bool) :
    ¬ IssueStage X (.thread f, true) v := by
  rintro ⟨hb,_,_⟩
  cases hb

/-- The return of a thread's last quiet event has no outgoing dependency in the existing
execution, unless it is a recorded Tensor Memory allocation-management lane. No absence of unrelated
async work is assumed. -/
theorem quiet_return_sink_of_effects
    (hv : EffectValidity L X) (hcl : ClusterHistoryOk L X) (hi : X.get f = some ⟨pc,k⟩)
    (hk : k.quiet = true) (hlast : f.2+1 = (X.tr f.1).length)
    (hord : ∀ cta j, ¬ Tmem.Pair.Precedes L X cta f j) :
    ∀ v, ¬ Waits L X (.thread f,true) v := by
  intro v
  rintro (⟨_,hb,_,_⟩ | ⟨_,_,i,j,hi',_,hij,hs,hl⟩ | ⟨i,j,hi',_,hb⟩ |
    ⟨hb,_⟩ | ⟨hb,_⟩ | ⟨_,_,hso⟩ | ⟨_,_,m,hb⟩ | ⟨i,j,hi',_,hw⟩ |
    ⟨hb,_⟩ | ⟨hb,_⟩ | ⟨_,_,i,j,hi',_,hsc⟩ | ⟨i,j,hi',_,hr⟩ |
    ⟨_,_,i,j,hi',_,cta,hp⟩ | ⟨_,_,i,j,hi',_,hfs⟩ | ⟨_,_,his⟩)
  · cases hb
  · cases hi'
    rw [← hij] at hl
    omega
  · rcases hb.2.2 with ⟨hb,_⟩ | ⟨hb,_⟩ | ⟨hb,_⟩ <;> cases hb
  · cases hb
  · cases hb
  · exact thread_no_stageOrder _ hso
  · exact quiet_no_object_before hv.tma hi hk m _ hb
  · cases hi'
    exact quiet_no_cluster hcl hi hk hw
  · cases hb
  · cases hb
  · cases hi'
    exact quiet_no_sync hi hk j hsc
  · cases hr.1
  · cases hi'
    exact hord cta j hp
  · cases hi'
    exact quiet_no_fenceSync hi hk j hfs
  · exact thread_no_issueStage _ his

end
end
end PTX
