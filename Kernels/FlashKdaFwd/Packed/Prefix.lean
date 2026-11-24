-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Entry
public import Kernels.FlashKdaFwd.Packed.ElectionTrace
public import Kernels.FlashKdaFwd.Packed.Launch
public import Lemmas.Step.WarpLanes
public import Lemmas.Kernel.Existence

@[expose] public section
namespace FlashKda.Packed.Entry
open PTX PTX.Step
noncomputable section

private def participants := (List.range 160).filter fun g => decide (128 ≤ g)

private theorem member {g : Nat} : g ∈ participants ↔ 128 ≤ g ∧ g < 160 := by
  simp [participants,and_comm]

private def electionEvent (leader : Fin 32) (_ : Nat) : Event := ⟨32,.elect 0xffffffff 0 leader.val⟩

private theorem as_batch (leader : Fin 32) :
    Execution.empty.appendLanes participants (electionEvent leader) =
      Election.initialElection leader := by
  unfold Execution.appendLanes Election.initialElection
  congr
  · funext g
    simp [member,Execution.empty,Election.warpTrace,electionEvent]
  · funext r i
    cases r with
    | «async» _ _ => rfl
    | thread e =>
      by_cases test : e.1 ∈ participants ∧ e.2 = 0 <;> simp [Execution.empty,test]

private theorem rules_wf (base : Nat → Nat → Nat) (L : Launch) (mem : Mem0) (X : Execution) :
    ∀ a ∈ Prologue.assumptions base, a.wf L mem X := by
  intro a ha
  simp only [Prologue.assumptions,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> trivial

theorem consistent_election (base : Nat → Nat → Nat) (L : Launch) (mem : Mem0) (leader : Fin 32)
    (v : BitVec 64) (host : L.params (Prologue.param 15) = some v)
    (block : L.block = 192) (threads : L.ntid = ⟨192,1,1⟩) (ctas : 0 < L.grid)
    (grid : L.clusterGridValid) :
    Consistent L kernel (Prologue.assumptions base) mem (Election.initialElection leader) := by
  have empty : Consistent L kernel (Prologue.assumptions base) mem Execution.empty :=
    consistent_empty grid (rules_wf base L mem _)
  let f := electionEvent leader
  have batch : Execution.empty.appendLanes participants f = Election.initialElection leader :=
    as_batch leader
  have hw : ∀ g ∈ participants, (f g).kind.WarpColl := fun _ _ => trivial
  have value : ∀ e pc k, (Execution.empty.appendLanes participants f).get e = some ⟨pc,k⟩ →
      k.laneValue = true → Execution.empty.get e = some ⟨pc,k⟩ := by
    intro e pc k h hk
    exact (appendLanes_get_kind (fun g hg => (hw g hg).ne (k' := k)
      (by cases k <;> simp_all [Kind.WarpColl,Kind.laneValue]))).mp h
  have exit : ∀ e pc, (Execution.empty.appendLanes participants f).get e = some ⟨pc,.exit⟩ →
      Execution.empty.get e = some ⟨pc,.exit⟩ := fun _ _ h =>
    (appendLanes_get_kind (fun g hg => (hw g hg).ne (k' := .exit) id)).mp h
  rw [← batch]
  apply appendLanes_consistent_lane (ds := participants) (ev := f) empty (List.nodup_range.filter _)
  · intro g hg
    have high := (member.mp hg).2
    unfold Launch.threads
    rw [block]
    omega
  · exact fun g hg => .of_warpColl (hw g hg)
  · intro g _
    right
    rintro ⟨i,s,ts,pc,he⟩
    simp [Execution.get,Execution.empty] at he
  · exact fun g _ => Released.of_get fun q h => by simp [Execution.get,Execution.empty] at h
  · intro g hg
    obtain ⟨lo,hi⟩ := member.mp hg
    let l : Fin 32 := ⟨g-128,by omega⟩
    have pos : 128+l.val = g := by dsimp [l]; omega
    obtain ⟨t,steps,pc,_⟩ := load_warp_election base L l v host block threads
    rw [pos] at steps
    let u := next (setReg (setReg t 3415 (Proof.b32 leader.val)) 3416
      (.pred (laneOf L g == leader.val)))
    exact ⟨{},t,some u,.nil _,steps.steps,_,steps.stop,0,leader.val,by rw [pc]; rfl,rfl⟩
  · intro _ _ j before
    simp [Execution.empty] at before
  · intro g _
    rw [batch]
    exact Election.warp_ready L block leader _
  · exact appendLanes_shflOk_of_not_shfl empty (fun _ _ _ _ _ _ _ _ h => by cases h)
  · rw [batch]
    exact Election.warp_agrees L block ctas leader
  · exact appendLanes_warpBarOk_of_not_warpBar empty (fun _ _ _ _ h => by cases h)
  · exact Execution.voteOk_mono empty.vote le_appendLanes value exit
  · exact Execution.warpValueOk_mono empty.warpValue le_appendLanes value exit
  · exact rules_wf base L mem _

theorem completion_with_leader (base : Nat → Nat → Nat) (L : Launch) (mem : Mem0)
    (post : FinalMem → Prop) (correct : Correct kernel (Prologue.assumptions base) L mem post)
    (leader : Fin 32) (v : BitVec 64) (host : L.params (Prologue.param 15) = some v)
    (block : L.block = 192) (threads : L.ntid = ⟨192,1,1⟩) (ctas : 0 < L.grid)
    (grid : L.clusterGridValid) :
    ∃ X, Consistent L kernel (Prologue.assumptions base) mem X ∧ Complete L X ∧
      ∀ l : Fin 32, X.Elect (128+l.val,0) 32 0xffffffff 0 leader.val := by
  obtain ⟨X,consistent,extendsTrace,finished⟩ :=
    correct.complete_extension (valid_launch L grid block)
      (consistent_election base L mem leader v host block threads ctas grid)
  refine ⟨X,consistent,finished,fun l => Execution.le_get extendsTrace ?_⟩
  have active : 128 ≤ 128+l.val ∧ 128+l.val < 160 := by omega
  simp [Execution.get,Election.initialElection,Election.warpTrace,active]

end
end FlashKda.Packed.Entry
