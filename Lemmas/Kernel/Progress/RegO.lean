-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Reg
public import Lemmas.Kernel.Progress.Bar
public import Lemmas.Kernel.FrameTrackedU

@[expose] public section

/-! # Progress at a register request, for a thread that makes several requests

`Sched.reg_stepsW` assumes every request is its thread's first. A kernel whose threads make
several requests (one per phase) matches requests by ordinal: a lane of the warp that has made no
request of the blocked thread's ordinal (`Step.missing_member_lane`) has not exited when every
exit of a lane follows a request of each ordinal a warp-mate made (`hexit`), so it is pending, and
its time is no later than the blocked thread's state before its request (`hbefore`), which the
state after the request exceeds (`hafter`). -/

namespace PTX.Sched
open PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- **Progress at a register request, by ordinal.** -/
theorem reg_stepsO (hC : ∀ g < L.threads, (M.code g).SoundU) (hs : SafeGoal K A L mem0)
    (htr : Frame.Tracked M.code X) (hb : L.block % 32 = 0)
    (hexit : ∀ {e : EvId} {pc n inst : Nat} {inc : Bool}, e.1 < L.threads →
      SetMaxNReg.Request X e pc inc n inst → ∀ {h j pc' : Nat}, SameWarp L e.1 h →
      X.get (h, j) = some ⟨pc', .exit⟩ → ∃ j' pc'' inc' n' inst',
        SetMaxNReg.Request X (h, j') pc'' inc' n' inst' ∧
          SetMaxNReg.ordinal X (h, j') = SetMaxNReg.ordinal X e)
    (hbefore : ∀ {g h k pc n inst : Nat} {inc : Bool} {d : (M.code g).D}, g < L.threads →
      h < L.threads → SameWarp L g h →
      (∀ j pc' inc' n' inst', X.get (h, j) = some ⟨pc', .setMaxReg inc' n' inst'⟩ →
        SetMaxNReg.ordinal X (h, j) ≠ SetMaxNReg.ordinal X (g, k)) →
      X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩ →
      Frame.stateAt M.code X g k = some (some d) → threadTime M X h ≤ M.time g d)
    (hafter : ∀ {g k pc n inst : Nat} {inc : Bool} {d : (M.code g).D}, g < L.threads →
      X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩ →
      Frame.stateAt M.code X g k = some (some d) →
      (∃ d', Frame.stateAt M.code X g (k + 1) = some (some d') ∧ M.time g d < M.time g d') ∨
        Frame.stateAt M.code X g (k + 1) = none)
    (hmax : Maximal L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    (hrel : ¬ Step.Released L X g) (hrw : RegWait L X g) : Steps M mem0 X (.thread g) := by
  obtain ⟨pc, inc, n, inst, hreq, hm⟩ := hrw
  have hX := hmax.1
  have hg := hp.1
  have hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .setMaxReg inc n inst⟩ := hreq
  have hlen : 0 < (X.tr g).length := by
    have : (X.tr g).length - 1 < (X.tr g).length := len_of_get hlast
    omega
  have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlen
  obtain ⟨dg, hdg⟩ := Frame.state_of_noUbU hC hX htr (safe_noUb (hs.2 X hX)) hlast
  obtain ⟨lane, hl, hmiss⟩ := Step.missing_member_lane (hs.2 X hX) hreq hm
  obtain ⟨h, hh, hwh, hlane⟩ := warp_mate hb hg hl
  obtain ⟨-, hno⟩ := hmiss h hh hwh hlane
  have hnx : ∀ j pc', X.get (h, j) ≠ some ⟨pc', .exit⟩ := by
    intro j pc' hj
    obtain ⟨j', pc'', inc', n', inst', hj', hord⟩ := hexit hg hreq hwh hj
    exact hno j' pc'' inc' n' inst' hj' hord
  have hph := pending_of_noExit hX hg hne hh (cluster_of_sameWarp hwh) hnx
  refine earlier_steps hmax hrel hph ?_
  have h1 := hbefore hg hh hwh hno hlast hdg
  have h2 := threadTime_after hlen hdg (hafter hg hlast hdg)
  omega

end
end PTX.Sched
