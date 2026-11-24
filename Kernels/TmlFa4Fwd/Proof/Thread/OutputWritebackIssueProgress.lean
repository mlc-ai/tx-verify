-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OutputWritebackPollProgress
import Lemmas.Step.CpAsyncIssueProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

/-- A writeback cursor retains the actual recorded lane boundary and exit frame. -/
structure WritebackReached (p : Params) (l : Launch) (X : Execution)
    (g batch head tile : Nat) (F : List (Nat × Value)) (ending : Option TState)
    (site : Option WritebackSite) (shuffles votes : Nat) where
  pos : Nat
  before : TState
  state : TState
  positive : 0 < pos
  bounded : pos ≤ (X.tr g).length
  released : pos = (X.tr g).length → Step.Released l X g
  recorded : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before)
  continuation : Run kernel Assumptions.all l g before ((X.tr g).drop pos) ending
  localSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before state
  checkpoint : At state (writebackPc site) (writebackFacts p l batch head tile site)
  saved : Holds state.regs F
  shuffleCount : ((X.tr g).take pos).countP Execution.isShfl = shuffles
  voteCount : ((X.tr g).take pos).countP isFullWarpVote = votes

/-- The four staged boxes followed by their group commit. -/
def writebackIssueSite (stage : Fin 2) (index : Fin 5) : WritebackSite :=
  if hi : index.val < 4 then .store stage ⟨index.val,hi⟩ else .commit stage

private theorem writebackIssueRange (stage : Fin 2) (index : Fin 5) :
    let site := writebackIssueSite stage index
    WritebackPc (writebackPc (some site)) ∧ WritebackPc (writebackPc (some site) + 1) := by
  decide +revert

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch head tile shuffles votes : Nat}
include hp hMax

/-- A prepared box or its commit extends the maximal trace by its actual event. -/
theorem WritebackReached.issueOfMaximal (hg : g < l.threads) (hb : batch < p.batch)
    (hh : head < p.heads) (ht : 256 * tile < p.qLength batch) (stage : Fin 2) (index : Fin 5)
    {F : List (Nat × Value)} (hF : ∀ item ∈ F, item.1 ∉ writebackWrites) {ending : Option TState}
    (cur : WritebackReached p l X g batch head tile F ending
      (some (writebackIssueSite stage index)) shuffles votes) :
    ∃ issued : WritebackReached p l X g batch head tile F ending
        (writebackSuccessor (writebackIssueSite stage index) true) shuffles votes,
      issued.pos = cur.pos+1 ∧
      X.get (g,cur.pos) = some ⟨writebackPc (some (writebackIssueSite stage index)),
        writebackKind p l g batch head tile (writebackIssueSite stage index) true⟩ := by
  let site := writebackIssueSite stage index
  let kind := writebackKind p l g batch head tile site true
  let dest := next cur.state
  have hPc := cur.checkpoint.1
  have hRange := writebackIssueRange stage index
  have hModel : ∀ {s : TState}, WritebackPc s.pc →
      out kernel Assumptions.all l g s = out kernel [] l g s :=
    fun h => epilogue_out_all_eq_nil (.inl ⟨by omega,by omega⟩)
  have hOut := (hModel (hPc.symm ▸ hRange.1)).trans
    (writebackOut hp g site cur.state hb hh ht cur.checkpoint)
  have hNext : Next kernel Assumptions.all l g cur.before cur.state
      (writebackTemplate p l g batch head tile site cur.state) := ⟨cur.localSteps,hOut⟩
  have hFire : ∀ (e : Event) (result : Option TState),
      Fires cur.state.pc (writebackTemplate p l g batch head tile site cur.state) e result ↔
        e = ⟨cur.state.pc,kind⟩ ∧ result = some dest := by
    intro e result
    cases e
    unfold kind site writebackIssueSite
    split <;> rfl
  have hIssue : Step.DeferredTransferIssueEvent ⟨cur.state.pc,kind⟩ := by
    unfold kind site writebackIssueSite
    split
    · exact .inr (.inl ⟨_,_,rfl⟩)
    · exact .inr (.inr rfl)
  obtain ⟨he,hPrefix,hSuffix⟩ := Step.deferred_transfer_issue_of_maximal hMax hg hNext hFire
    hIssue cur.recorded cur.continuation cur.positive cur.bounded cur.released
    (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc (by
      unfold kind site writebackIssueSite
      split <;> rfl)))
  have hFired := (hFire _ _).mpr ⟨rfl,rfl⟩
  obtain ⟨_,v,steps,hStep,hAt,hFrame,_⟩ := writebackStep hp g site hb ht cur.checkpoint hFired
  have hTrue : writebackSucceeded kind = true := by
    unfold kind site writebackIssueSite
    split <;> rfl
  rw [hTrue] at hAt
  have hSaved : Holds v.regs F := by
    apply holdsSchedulerFrame (regs := F.map Prod.fst) cur.saved
    · intro r hr
      obtain ⟨item,hm,rfl⟩ := List.mem_map.mp hr
      exact hFrame item.1 (hF item hm)
    · intro item hm
      exact List.mem_map_of_mem hm
  have hDest : WritebackPc dest.pc := by
    change WritebackPc (cur.state.pc+1)
    rw [hPc]
    exact hRange.2
  have hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) dest v :=
    writebackLiftLocal hModel hDest (run_rtg hStep)
  have hTake := List.take_succ_eq_append_getElem (len_of_get he)
  rw [(List.getElem?_eq_some_iff.mp he).2] at hTake
  have hSh : ((X.tr g).take (cur.pos+1)).countP Execution.isShfl = shuffles := by
    rw [hTake,List.countP_append,cur.shuffleCount]
    unfold kind site writebackIssueSite
    split <;> rfl
  have hVote : ((X.tr g).take (cur.pos+1)).countP isFullWarpVote = votes := by
    rw [hTake,List.countP_append,cur.voteCount]
    unfold kind site writebackIssueSite
    split <;> rfl
  refine ⟨⟨cur.pos+1,dest,v,Nat.succ_pos _,len_of_get he,?_,hPrefix,hSuffix,hLocal,hAt,hSaved,
    hSh,hVote⟩,rfl,?_⟩
  · apply releasedIfLast he
    unfold kind site writebackIssueSite
    split <;> (intro h; cases h)
  · rwa [hPc] at he

/-- All four O boxes and the stage's group commit are actually issued once its acquire succeeds. -/
theorem WritebackReached.stageIssueOfMaximal (hg : g < l.threads) (hb : batch < p.batch)
    (hh : head < p.heads) (ht : 256 * tile < p.qLength batch) (stage : Fin 2)
    {F : List (Nat × Value)} (hF : ∀ item ∈ F, item.1 ∉ writebackWrites) {ending : Option TState}
    (cur : WritebackReached p l X g batch head tile F ending (some (.store stage 0)) shuffles votes)
    :
    ∃ committed : WritebackReached p l X g batch head tile F ending
        (writebackSuccessor (.commit stage) true) shuffles votes,
      committed.pos = cur.pos+5 ∧
      (∀ box : Fin 4, X.TensorStoreIssue (g,cur.pos+box.val) p.oMapAddress
        (writebackStoreSpec p l g batch head tile stage box)) ∧
      X.get (g,cur.pos+4) = some ⟨commitPc stage,.bulkCommit⟩ := by
  obtain ⟨s1,hp1,he0⟩ := cur.issueOfMaximal hp hMax hg hb hh ht stage 0 hF
  obtain ⟨s2,hp2,he1⟩ := s1.issueOfMaximal hp hMax hg hb hh ht stage 1 hF
  obtain ⟨s3,hp3,he2⟩ := s2.issueOfMaximal hp hMax hg hb hh ht stage 2 hF
  obtain ⟨s4,hp4,he3⟩ := s3.issueOfMaximal hp hMax hg hb hh ht stage 3 hF
  obtain ⟨s5,hp5,he4⟩ := s4.issueOfMaximal hp hMax hg hb hh ht stage 4 hF
  refine ⟨s5,by omega,?_,?_⟩
  · intro box
    fin_cases box
    · exact ⟨_,he0⟩
    · exact ⟨_,(by rw [hp1] at he1; exact he1)⟩
    · exact ⟨_,(by rw [hp2,hp1] at he2; exact he2)⟩
    · exact ⟨_,(by rw [hp3,hp2,hp1] at he3; exact he3)⟩
  · rw [show cur.pos+4 = s4.pos by omega]
    exact he4

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
