-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Reg

@[expose] public section

/-! # Progress at a register request, with a time per warp

`Sched.reg_steps` places every thread without a request no later than one time `T` and every
thread after its request later than `T`. A time table whose warps request at different times
(one warpgroup requests after another's states) gives a time `T g` per thread, equal on the lanes
of a warp (`reg_stepsW`); the proof is `reg_steps`'s with `T g` for `T`. -/

namespace PTX.Sched
open PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- **Progress at a register request, with a time per warp.** A pending thread whose last event
is a register request that not every lane of its warp has matched steps. -/
theorem reg_stepsW (hs : SafeGoal K A L mem0) (hmatch : RegMatch L X) (hexit : RegExit L X)
    (hb : L.block % 32 = 0) (T : Nat → Nat) (hT : ∀ {g h : Nat}, SameWarp L g h → T g = T h)
    (hbefore : ∀ {h : Nat}, h < L.threads →
      (∀ j pc inc n inst, X.get (h, j) ≠ some ⟨pc, .setMaxReg inc n inst⟩) →
      threadTime M X h ≤ T h)
    (hafter : ∀ {g k pc n inst : Nat} {inc : Bool}, g < L.threads →
      X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩ →
      ∃ d, Frame.stateAt M.code X g (k + 1) = some (some d) ∧ T g < M.time g d)
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
  obtain ⟨dg, hσg, hgt⟩ := hafter hg hlast
  rw [Nat.sub_add_cancel hlen] at hσg
  obtain ⟨lane, hl, hmiss⟩ := Step.missing_member_lane (hs.2 X hX) hreq hm
  obtain ⟨h, hh, hwh, hlane⟩ := warp_mate hb hg hl
  obtain ⟨hno, -⟩ := hmiss h hh hwh hlane
  have hnoreq : ∀ j pc' inc' n' inst', X.get (h, j) ≠ some ⟨pc', .setMaxReg inc' n' inst'⟩ := by
    intro j pc' inc' n' inst' hj
    exact hno j (hmatch (e := (g, _)) (f := (h, j)) hg hh hwh hreq hj)
  have hnx : ∀ j pc', X.get (h, j) ≠ some ⟨pc', .exit⟩ := by
    intro j pc' hj
    obtain ⟨j', pc'', inc', n', inst', hj'⟩ := request_of_ordinal (hexit hh hj)
    exact hnoreq j' pc'' inc' n' inst' hj'
  have hph := pending_of_noExit hX hg hne hh (cluster_of_sameWarp hwh) hnx
  refine earlier_steps hmax hrel hph ?_
  have h1 := hbefore hh hnoreq
  rw [threadTime_of hσg, ← hT hwh] at *
  omega

end
end PTX.Sched
