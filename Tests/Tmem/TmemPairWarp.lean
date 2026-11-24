-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairHistory
public import Core.Assembly.Waiting

namespace PTX.Tests.TmemPairWarp
open Tmem.Pair
noncomputable section

private def L : Launch := { grid := 2, block := 32, clusterSize := 2, params := fun _ => none }
private def dealloc : Event := ⟨0, .tc (.resource .two none (.dealloc 0 32))⟩
private def ownWarp : Execution := {
  tr := fun g => if g < 32 then [dealloc, ⟨1, .exit⟩] else [], rf := fun _ _ => none }
private def request : WarpRequest := {
  cta := 0, warp := 0, indices := fun _ => 0, pc := 0, dst := none, request := .dealloc 0 32 }

private theorem tcK_zero (g : Nat) (hg : g < 32) : ownWarp.TcK (g, 0) 0 :=
  ⟨⟨dealloc, by simp [Execution.get, ownWarp, hg], rfl⟩, by simp⟩

private theorem valid : request.Valid L ownWarp .two := by
  refine ⟨by decide, by decide, ?_, 0, ?_⟩
  · intro lane
    simp [WarpRequest.event, request, L, Execution.get, ownWarp, lane.isLt, dealloc]
  · intro lane
    have he : WarpRequest.event L request lane = (lane.val, 0) := by
      simp [WarpRequest.event, request, L]
    rw [he]
    exact tcK_zero lane.val lane.isLt

-- All local lanes may return while the entire other CTA remains absent: the warp
-- collective is complete, the paired request is not.
example : ∀ lane : Fin 32, ∃ j, ownWarp.TcK (lane.val, j) 0 := by
  intro lane
  exact ⟨0, tcK_zero lane.val lane.isLt⟩
example : request.Valid L ownWarp .two := valid
example : ¬ Covered L ownWarp (0, 0) := by
  rintro ⟨ws, ⟨_, r, hr, _⟩ | ⟨q, hq, _⟩, _⟩
  · cases hr
  · cases hq

private def missing : Execution := {
  tr := fun g => if g = 0 then [dealloc, ⟨1, .exit⟩] else [], rf := fun _ _ => none }

-- Optional peer return does not allow lane zero to skip the other 31 local lanes: the needs of the
-- request name every lane of the warp (DEP-ORDER).
example : ¬ Ready L missing (0, 0) := by
  intro h
  have hn : (Need.node fun x => ∃ j, x = .thread (1, j) ∧ missing.TcK (1, j) 0) ∈
      Needs L missing (0, 0) := by
    have hmem : (1 : Nat) ∈ warpLanes L 0 := by
      simp [warpLanes, warpSize, warpLane, laneOf, L]
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨1, hmem, ?_⟩))
    simp [missing]
  obtain ⟨x, hx, j, rfl, -⟩ := h _ hn
  obtain ⟨ev, he⟩ := hx
  simp [Execution.get, missing] at he

private def mixed : Execution := {
  tr := fun g => if g = 0 then [dealloc] else [dealloc, dealloc], rf := fun _ _ => none }
private def mixedRequest : WarpRequest := {
  request with indices := fun lane => if lane.val = 0 then 0 else 1 }

-- Matching source PCs and operands cannot join different dynamic occurrences.
example : ¬ mixedRequest.Valid L mixed .two := by
  rintro ⟨_, _, _, k, hk⟩
  have h0 := (hk 0).2
  have h1 := (hk 1).2
  have e0 : WarpRequest.event L mixedRequest 0 = (0, 0) := by
    simp [WarpRequest.event, mixedRequest, request, L]
  have e1 : WarpRequest.event L mixedRequest 1 = (1, 1) := by
    simp [WarpRequest.event, mixedRequest, request, L]
  rw [e0] at h0
  rw [e1] at h1
  simp [mixed, isTcColl, dealloc] at h0 h1
  omega

end
end PTX.Tests.TmemPairWarp
