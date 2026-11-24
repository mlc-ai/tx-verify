-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Poll
import Std.Tactic.BVDecide.Normalize.Bool

@[expose] public section

/-! # The correction warps' side of the output warp's ready polls, narrowed

`ReadyLag` (`OutputPoll.lean`) asks, while the ready barrier of stage `st` is in an even phase,
for a correction lane of the CTA that has not exited and is earlier than the output warp's poll
(`tailBase p + 2 + 8 st`). The time half is proved here from the correction warps' time table
(`Cr.time`): a correction lane whose state is a startup state, or a correction state not past its
arrival on that barrier (`preReady st`: the final stage of the stages up to `st`, ending at
`fdone st 1`, and every earlier site of the first pass) with at most `cmax p` collectives, is
earlier (`corr_before`). What remains is `ReadyArrive`, which no longer names a time:

* the ready barrier has a state, and while its phase is even some correction lane of the CTA
  has not exited and sits at such a state (at the end of its trace, followed by the thread
  machine).

It is the unit hand-off of the ready barriers (the barrier counts the 128 correction lanes'
arrivals at `fdone st 1`, plan T3) plus the correction warps' following (`Correction.good` on the
thread frame, lane T1) and the first-pass bound on their collectives (the correction's `Fits`,
which mirrors the output warp's). The correction ledger's closed forms (lane T2, branch
`tmlfa4-corr-proof2`) give the arrival count at each site; they are stated on the correction's
own counted machine and enter here with that following. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Progress
open PTX PTX.Proof PTX.Flow MBarrier

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The correction sites at or before the arrival on the ready barrier of stage `st`. -/
def preReady (st : Fin 2) : Correction.Site → Bool
  | .fbar s | .fsum s | .fmax s | .farr s | .fw s _ | .fld s _ | .fwl s _ | .fst s _ _
  | .fence s | .fdone s _ => decide (s.val ≤ st.val)
  | .lse _ => false
  | s => !Cr.late s

/-- **A correction state at or before its arrival on the ready barrier of stage `st` is earlier
than the output warp's poll of it.** A rescale-round or final-stage state is in a pipeline slot,
before the tail; any other is in a scheduler pass, the first one by `preReady`. -/
theorem corr_before {st : Fin 2} {d : Correction.D} {n : Cls → Nat}
    (hpre : preReady st d.site = true)
    (hc : Cr.round d.site = false → Cr.tailOff d.site = none → collCount n ≤ cmax p) :
    Cr.time p d n < tailBase p + 2 + 8 * st.val := by
  unfold Cr.time
  split
  next st past _ =>
    have := clk_lt_tail (p := p) (a := n (.corr (.nb st)) - if past then 1 else 0)
      (Cr.off_lt st d.site)
    simp only [Cr.slot]
    omega
  next hp0 =>
    obtain ⟨hr, ht⟩ := (Cr.part_none d.site).mp hp0
    have hl : Cr.late d.site = false := by
      obtain ⟨site, v, k⟩ := d
      cases site <;> simp_all [preReady, Cr.round, Cr.tailOff, Cr.late]
    have h2 := primeBase_le_clk p (bmax p + 1) 0
    have h3 := scanBase_le_primeBase p
    simp only [tailBase]
    split
    next l o he =>
      have hol : l = false ∧ o < 8 := by
        obtain ⟨site, v, k⟩ := d
        cases site <;>
          simp only [Cr.endOff, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at he <;>
          obtain ⟨rfl, rfl⟩ := he <;> simpa [Cr.late] using hl
      simp only [endT, hol.1, Bool.false_eq_true, ↓reduceIte]
      omega
    next =>
      have hb : Out.ballots (Cr.toE d.site) ≤ 1 := by
        unfold Out.ballots; split <;> omega
      have hc' : n .shfl + Out.ballots (Cr.toE d.site) ≤ cmax p + 1 := by
        have := hc hr ht
        unfold collCount at this
        omega
      have h1 := pass_lt_prime hc' (Out.coll (Cr.toE d.site))
      simp only [hl, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> omega

/-- A startup state that is no exit is earlier than the tail. -/
theorem start_before {s : Startup.D} (hx : ∀ r, s.site ≠ .enter r) (st : Fin 2) :
    startTime s < tailBase p + 2 + 8 * st.val := by
  have := startTime_lt hx
  have := scanBase_le_tailBase p
  omega

/-- A correction lane `y` at the end of its trace is at a startup state, or at a correction state
at or before its arrival on the ready barrier of stage `st`, with a first-pass count of
collectives when it is outside the rescale rounds and the final stage (in the rounds the rescale
ballots add to the count; there the time does not read it). -/
def CorrPre (p : Params) (L : Launch) (st : Fin 2) (X : Execution) (y : Nat) : Prop :=
  (∃ s n, Frame.stateAt (thread p L) X y (X.tr y).length = some (some (.inl s, n)) ∧
    ∀ r, s.site ≠ .enter r) ∨
  ∃ d n, Frame.stateAt (thread p L) X y (X.tr y).length =
      some (some (.inr ⟨.correction, d⟩, n)) ∧ preReady st d.site = true ∧
      (Cr.round d.site = false → Cr.tailOff d.site = none → collCount n ≤ cmax p)

/-- **The ready barriers' hand-off and the correction warps' following**: in every consistent
execution, the ready barrier of stage `st` of a lane of warp 13 at its ready poll of stage `st`
at the end of its trace has a state, and while its phase
is even a correction lane of the CTA, when the execution has no undefined behaviour, has not
exited and is at a state of `CorrPre`. -/
def ReadyArrive (p : Params) (L : Launch) (m : Mem0) : Prop :=
  ∀ X, Consistent L kernel Assumptions.all m X → ∀ g (st : Fin 2), g < L.threads →
    Prologue.warpIndex L g = 13 → ∀ (d : Epilogue.D) (n : Cls → Nat),
    Frame.stateAt (thread p L) X g (X.tr g).length = some (some (Epilogue.inj p L g d n)) →
    d.site = .ready st →
    ∃ before, stateBefore (X.objects (Epilogue.readyLoc L g st))
        (X.objects (Epilogue.readyLoc L g st)).length = some before ∧
      (before.phase % 2 = 0 → ∃ y, y < L.threads ∧ y / L.block = g / L.block ∧
        (¬ HasUb X → (∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩) ∧ CorrPre p L st X y))

/-- **`ReadyLag` from the hand-off and the following.** -/
theorem readyLag_of (h : ReadyArrive p L m) : ReadyLag p L m := by
  intro X hX g st hg hw d n hσ0 hs0
  obtain ⟨before, hstate, hy⟩ := h X hX g st hg hw d n hσ0 hs0
  refine ⟨before, hstate, fun hph => ?_⟩
  obtain ⟨y, hyt, hcta, hl⟩ := hy hph
  refine ⟨y, hyt, hcta, fun hub => ?_⟩
  obtain ⟨hx, hpre⟩ := hl hub
  refine ⟨hx, ?_⟩
  rcases hpre with ⟨s, n, hσ, hxs⟩ | ⟨d, n, hσ, hpre, hc⟩
  · rw [Sched.threadTime_of (M := timed p L) hσ, time_start]
    exact start_before hxs st
  · rw [Sched.threadTime_of (M := timed p L) hσ]
    exact corr_before hpre hc

end
end PTX.Kernels.TmlFa4Fwd.Proof.Progress
