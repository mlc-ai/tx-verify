-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Election
public import Lemmas.Execution.ExecutionGrowth

@[expose] public section
namespace FlashKda.Packed.Election
open PTX

def warpTrace (leader : Fin 32) (g : Nat) : List Event :=
  if 128 ≤ g ∧ g < 160 then [⟨32,.elect 0xffffffff 0 leader.val⟩] else []

noncomputable def initialElection (leader : Fin 32) : Execution :=
  {Execution.empty with tr := warpTrace leader}

private theorem get_at (leader : Fin 32) {e : EvId} {ev : Event}
    (h : (initialElection leader).get e = some ev) :
    128 ≤ e.1 ∧ e.1 < 160 ∧ e.2 = 0 ∧ ev = ⟨32,.elect 0xffffffff 0 leader.val⟩ := by
  rcases e with ⟨g,i⟩
  by_cases active : 128 ≤ g ∧ g < 160
  · cases i with
    | zero =>
      exact ⟨active.1,active.2,rfl,
        (Option.some.inj (by simpa [Execution.get,initialElection,warpTrace,active] using h :
          some (⟨32,.elect 0xffffffff 0 leader.val⟩ : Event) = some ev)).symm⟩
    | succ i => simp [Execution.get,initialElection,warpTrace,active] at h
  · simp [Execution.get,initialElection,warpTrace,active] at h

private theorem event_at (leader : Fin 32) {e : EvId} {pc mask inst n : Nat}
    (h : (initialElection leader).Elect e pc mask inst n) :
    128 ≤ e.1 ∧ e.1 < 160 ∧ e.2 = 0 ∧ pc = 32 ∧ mask = 0xffffffff ∧ inst = 0 ∧ n = leader.val := by
  obtain ⟨lo,hi,idx,event⟩ := get_at leader h
  cases event
  exact ⟨lo,hi,idx,rfl,rfl,rfl,rfl⟩

theorem warp_ready (L : Launch) (block : L.block = 192) (leader : Fin 32) (e : EvId) :
    Ready L (initialElection leader) e := by
  intro need hn
  cases atEvent : (initialElection leader).get e with
  | none => simp [Needs,atEvent] at hn
  | some ev =>
    obtain ⟨lo,hi,_,rfl⟩ := get_at leader atEvent
    simp only [Needs,atEvent,KindNeeds,List.mem_map,List.mem_filter,List.mem_range] at hn
    obtain ⟨l,⟨hl,_⟩,rfl⟩ := hn
    have pos : warpLane L e.1 l = 128+l := by
      unfold warpLane laneOf
      rw [block,Nat.mod_eq_of_lt (show e.1 < 192 by omega)]
      omega
    have active : 128 ≤ 128+l ∧ 128+l < 160 := by omega
    have mem : (initialElection leader).get (warpLane L e.1 l,0) =
        some ⟨32,.elect 0xffffffff 0 leader.val⟩ := by
      simp [Execution.get,initialElection,warpTrace,pos,active]
    exact ⟨.thread (warpLane L e.1 l,0),⟨_,mem⟩,0,32,leader.val,rfl,mem⟩

theorem warp_agrees (L : Launch) (block : L.block = 192) (ctas : 0 < L.grid) (leader : Fin 32) :
    ElectOk L (initialElection leader) := by
  constructor
  · intro e pc mask inst n ev
    obtain ⟨_,upper,_,_,rfl,_,rfl⟩ := event_at leader ev
    have enough : 192 ≤ L.threads := by
      unfold Launch.threads
      rw [block]
      omega
    exact ⟨by omega, mask_member (Nat.mod_lt _ (by decide)), mask_member leader.isLt⟩
  constructor
  · intro e f pc pc' mask mask' inst n n' a b _
    obtain ⟨_,_,ei,rfl,rfl,_,rfl⟩ := event_at leader a
    obtain ⟨_,_,fi,rfl,rfl,_,rfl⟩ := event_at leader b
    exact ⟨rfl,rfl,rfl,fun same => Prod.ext same (ei.trans fi.symm)⟩
  · intro e f pc pc' mask inst inst' n n' a b _
    exact (event_at leader a).2.2.2.2.2.2.trans (event_at leader b).2.2.2.2.2.2.symm

end FlashKda.Packed.Election
