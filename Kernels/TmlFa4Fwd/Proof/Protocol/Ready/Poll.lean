-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.Time
public import Lemmas.Kernel.Progress.Poll
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.SharedSites
import Kernels.TmlFa4Fwd.Proof.Epilogue.Facts
import Lemmas.Kernel.Progress.PollsOn

@[expose] public section

/-! # Progress at the output warp's ready polls

A lane of warp 13 whose state at the end of its trace is the ready poll of stage `st` polls the
stage's ready barrier next, with parity 0 and no successful poll of it so far (`ready_pollsOn`:
the shape table, `Fits` and the ledger `Led` on the thread frame, through the library candidate
`Frame.pollsOn_of_shapeAt`). The barrier's producers are the 128 correction lanes of the CTA (its
initialization count). Their side is the premise `ReadyLag`: the barrier has a state, and while its
phase is even a correction lane of the CTA has not exited and is earlier than the poll. With it the
lane is at an mbarrier wait whose blockers are earlier (`ready_mbarAt`), which
`Sched.mbar_at_steps` turns into a descent step. `ReadyLag` is the conjunction of the unit hand-off
of the ready barriers (plan T3) and the correction warps' times (lane T2); it is proved when the
correction fragment is glued. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Progress
open PTX PTX.Proof PTX.Flow MBarrier

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The correction warps' side of the output warp's ready polls**: in every consistent
execution, the ready barrier of stage `st` of a lane of warp 13 that is at its ready poll of stage
`st` at the end of its trace has a state, and while its phase is even a lane of the CTA has not
exited and is earlier than the poll (`Sched.Lags`). (A lane of a CTA without a tile never polls
the ready barriers, and its CTA's correction lanes exit without arriving on them.) -/
def ReadyLag (p : Params) (L : Launch) (m : Mem0) : Prop :=
  ∀ X, Consistent L kernel Assumptions.all m X → ∀ g (st : Fin 2), g < L.threads →
    Prologue.warpIndex L g = 13 → ∀ (d : Epilogue.D) (n : Cls → Nat),
    Frame.stateAt (thread p L) X g (X.tr g).length = some (some (Epilogue.inj p L g d n)) →
    d.site = .ready st →
    ∃ before, stateBefore (X.objects (Epilogue.readyLoc L g st))
        (X.objects (Epilogue.readyLoc L g st)).length = some before ∧
      (before.phase % 2 = 0 → ∃ y, y < L.threads ∧ y / L.block = g / L.block ∧
        Sched.Lags (timed p L) X y (tailBase p + 2 + 8 * st.val))

/-- The ready polls' instructions: acquiring polls. -/
theorem ready_code (st : Fin 2) : ∃ gd pp b off par sc,
    kernel.code[(Epilogue.Site.ready st).pc]? = some ⟨gd, .mbarWait pp b off par true sc⟩ := by
  fin_cases st
  · exact ⟨_, _, _, _, _, _, Flow.code_2958⟩
  · exact ⟨_, _, _, _, _, _, Flow.code_2972⟩

/-- **A lane of warp 13 at the ready poll of stage `st` polls the stage's ready barrier next**,
with the parity of its successful polls of it (none so far). -/
theorem ready_pollsOn (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 13) {d : Epilogue.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (Epilogue.inj p L g d n)))
    {st : Fin 2} (hs : d.site = .ready st) :
    Sched.PollsOn kernel Assumptions.all L X g (Epilogue.readyLoc L g st) 0 := by
  have hled := (Epilogue.fits hp hX hg hw hσ).2
  have hok : Flow.okPolls (Epilogue.readyLoc L g st) (X.tr g) = 0 := by
    have hc := count hσ (.poll st)
    rw [List.take_length] at hc
    have h0 : n (.poll st) = 0 := by
      rw [(hled.2.2.2.2 st).1]
      simp [Epilogue.acqd, hs]
    simp only [Flow.okPolls]
    rw [← h0, ← hc]
    rfl
  obtain ⟨gd, pp, b, off, par, sc, hc⟩ := ready_code st
  rw [← hs] at hc
  refine strict_pollsOn hp hg hσ rfl
    (P := Epilogue.Ev p L g d) (fun hat hi hc' hf => Epilogue.shape hp hat hi hc' hf) hc
    ?_ ?_
  · intro f hE
    simp only [Epilogue.Ev, hs] at hE
    obtain ⟨ok, h⟩ := hE
    cases h
  · intro l q ok sc' hE
    simp only [Epilogue.Ev, hs] at hE
    obtain ⟨ok', h⟩ := hE
    simp only [Kind.wait.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨rfl, by rw [hok]⟩

/-- **A lane of warp 13 at the ready poll of stage `st` has an earlier blocker** when the poll
fails, in an execution without undefined behaviour. -/
theorem ready_pollBlocked (hp : Pre p L m) (hR : ReadyLag p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hub : ¬ HasUb X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 13) {d : Epilogue.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (Epilogue.inj p L g d n)))
    {st : Fin 2} (hs : d.site = .ready st) : Sched.PollBlocked (timed p L) X g := by
  obtain ⟨before, hstate, hlag⟩ := hR X hX g st hg hw d n hσ hs
  refine Sched.pollBlocked_of (ready_pollsOn hp hX hg hw hσ hs) hstate fun hpar => ?_
  have hok : Flow.okPolls (Epilogue.readyLoc L g st) (X.tr g) = 0 := by
    have hc := count hσ (.poll st)
    rw [List.take_length] at hc
    have h0 : n (.poll st) = 0 := by
      rw [(Epilogue.fits hp hX hg hw hσ).2.2.2.2.2 st |>.1]
      simp [Epilogue.acqd, hs]
    simp only [Flow.okPolls]
    rw [← h0, ← hc]
    rfl
  rw [hok] at hpar
  obtain ⟨y, hy, hcta, hl⟩ := hlag (by omega)
  have hne : X.tr g ≠ [] := by
    intro h0
    rw [h0, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  refine Sched.blk_of_lags hX hub hg hne hσ hy (by rw [hcta]) ?_
  rw [time_inj, Out.time_ready hs]
  exact hl

/-- **The output warp's ready poll as an `MbarAt`** with a blocker time below the lane's, and
the lane's time at least 2 (`Sched.mbar_at_steps`' premises). -/
theorem ready_mbarAt (hp : Pre p L m) (hR : ReadyLag p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hub : ¬ HasUb X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 13) {d : Epilogue.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (Epilogue.inj p L g d n)))
    {st : Fin 2} (hs : d.site = .ready st) :
    ∃ b, Sched.MbarAt (timed p L) m X g b ∧ b < Sched.threadTime (timed p L) X g ∧
      2 ≤ Sched.threadTime (timed p L) X g := by
  have ht : Sched.threadTime (timed p L) X g = tailBase p + 2 + 8 * st.val := by
    rw [Sched.threadTime_of (M := timed p L) hσ, time_inj, Out.time_ready hs]
  refine ⟨_, Sched.mbarAt_of (ready_pollBlocked hp hR hX hub hg hw hσ hs), ?_, ?_⟩ <;>
    rw [ht] <;> omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Progress
