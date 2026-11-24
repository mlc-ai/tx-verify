-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.Waits
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Reg
public import Lemmas.Step.SetMaxNReg

@[expose] public section

/-! # Progress at a register request

A pending thread whose last event is a `setmaxnreg` that not every lane of its warp has matched
(`RegWait`, DEP-SETMAXNREG-RENDEZVOUS) steps (`reg_steps`). In a safe execution some lane of the
warp has no matching request (`Step.missing_member_lane`). Two requests of lanes of one warp match
(`RegMatch`), so that lane has made no request at all, and so it has not exited (`RegExit`): it is
pending. Both premises follow from the safety layer's `Safety.RegFacts`. It is at a state no later
than the requests' time (`RegWaitFacts.before`), while the blocked thread is after it
(`RegWaitFacts.after`), so the lane ranks below the blocked thread. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Two register requests of lanes of one warp match: each is its thread's first, at its warp's
site, with its warpgroup's direction and count (`Safety.RegFacts.request`). -/
def RegMatch (L : Launch) (X : Execution) : Prop :=
  ∀ {e f : EvId} {pc pc' n n' inst inst' : Nat} {inc inc' : Bool}, e.1 < L.threads →
    f.1 < L.threads → SameWarp L e.1 f.1 → SetMaxNReg.Request X e pc inc n inst →
    SetMaxNReg.Request X f pc' inc' n' inst' → SetMaxNReg.SameRequest L X e f

/-- A thread exits after its register request (`Safety.RegFacts.exit`). -/
def RegExit (L : Launch) (X : Execution) : Prop :=
  ∀ {h k pc : Nat}, h < L.threads → X.get (h, k) = some ⟨pc, .exit⟩ →
    1 ≤ SetMaxNReg.ordinal X (h, k)

/-- A thread of the warp of `g` in a given lane. -/
theorem warp_mate (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) {lane : Nat}
    (hl : lane < 32) : ∃ h, h < L.threads ∧ SameWarp L g h ∧ laneOf L h = lane := by
  have hb := hpre.block
  refine ⟨g / L.block * L.block + g % L.block / 32 * 32 + lane, ?_, ?_, ?_⟩
  all_goals simp only [Launch.threads, SameWarp, SameCta, laneOf, hb] at hg ⊢
  · omega
  · refine ⟨⟨hg, ?_, ?_⟩, ?_⟩ <;> omega
  · omega

/-- A thread whose events before `k` count a register request has a request event. -/
theorem request_of_ordinal {h k : Nat} (hk : 1 ≤ SetMaxNReg.ordinal X (h, k)) :
    ∃ j pc inc n inst, X.get (h, j) = some ⟨pc, .setMaxReg inc n inst⟩ := by
  unfold SetMaxNReg.ordinal at hk
  obtain ⟨e, he, hp⟩ := List.countP_pos_iff.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take he)
  obtain ⟨pc, kind⟩ := e
  cases kind with
  | setMaxReg inc n inst => exact ⟨j, pc, inc, n, inst, hj⟩
  | _ => simp [SetMaxNReg.isRequest] at hp

/-- **Progress at a register request.** A pending thread whose last event is a register request
that not every lane of its warp has matched steps: a lane with no request is pending and
earlier. -/
theorem reg_steps (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (hmatch : RegMatch L X) (hexit : RegExit L X) (hw : RegWaitFacts L X)
    (hmax : Maximal L kernel asms mem0 X)
    {g : Nat} (hp : Frame.Pending L X g) (hrel : ¬ Step.Released L X g)
    (hrw : Sched.RegWait L X g) :
    Sched.Steps (timed L) mem0 X (.thread g) := by
  obtain ⟨pc, inc, n, inst, hreq, hm⟩ := hrw
  have hX := hmax.1
  have hg := hp.1
  have hsafe := hs.2 X hX
  have hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .setMaxReg inc n inst⟩ := hreq
  have hlen : 0 < (X.tr g).length := by
    have : (X.tr g).length - 1 < (X.tr g).length := len_of_get hlast
    omega
  have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlen
  obtain ⟨dg, hσg, hgt⟩ := hw.after hg hlast
  rw [Nat.sub_add_cancel hlen] at hσg
  obtain ⟨lane, hl, hmiss⟩ := Step.missing_member_lane hsafe hreq hm
  obtain ⟨h, hh, hwh, hlane⟩ := warp_mate hpre hg hl
  obtain ⟨hno, -⟩ := hmiss h hh hwh hlane
  -- the lane has made no request: a request of it would match `g`'s
  have hnoreq : ∀ j pc' inc' n' inst', X.get (h, j) ≠ some ⟨pc', .setMaxReg inc' n' inst'⟩ := by
    intro j pc' inc' n' inst' hj
    exact hno j (hmatch (e := (g, _)) (f := (h, j)) hg hh hwh hreq hj)
  have hnx : ∀ j pc', X.get (h, j) ≠ some ⟨pc', .exit⟩ := by
    intro j pc' hj
    obtain ⟨j', pc'', inc', n', inst', hj'⟩ := request_of_ordinal (hexit hh hj)
    exact hnoreq j' pc'' inc' n' inst' hj'
  have hph := Sched.pending_of_noExit hX hg hne hh (Sched.cluster_of_sameWarp hwh) hnx
  refine Sched.earlier_steps hmax hrel hph ?_
  have h1 : endTime L X h ≤ Time.regT := by
    exact hw.before hh hnoreq
  rw [endTime_of hσg]
  omega

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
