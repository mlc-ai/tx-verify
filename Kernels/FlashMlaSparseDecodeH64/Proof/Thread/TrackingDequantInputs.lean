-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawReadback
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate
import Lemmas.Flow.Final
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCausalInduction
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry

@[expose] public section

/-! # Actual launches preserve tracking at each dequantizer event -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem actual_dequant_finite {g i : Nat} {d : Wg2.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d))) :
    Wg2.FiniteInput d e := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := (hs g hg).machine.produces (hX.thr g hg) |>.fired_at he hd
  cases o with
  | some u => exact Protocol.RawReadback.actual_finite_input hpre hX hs he hd hf
  | none =>
    obtain ⟨_, _, hFire⟩ := hf
    rcases fires_none_ends hFire with ⟨f, hk⟩ | hk <;>
      cases hSite : d.site <;> simp [Wg2.FiniteInput, hSite, hk]

/-- At a followed concrete step only a softmax role can still need a numerical premise. -/
theorem actual_step_tracked {g i : Nat} {d : Machine.ThreadD} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hsoftmax : ∀ w, Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 w)) →
      Machine.next P L g (.wg0 w) e ≠ some none) :
    Machine.next P L g d e ≠ some none := by
  have hg := Frame.lt_of_get hX he
  cases d with
  | prologue s =>
    exact PrologueRoleTrace.prologue_next_tracked hpre hX (fun h hh => (hs h hh).machine) he hd
  | head =>
    exact PrologueRoleTrace.dispatch_next_tracked hpre hX (fun h hh => (hs h hh).machine) he hd
  | wg0 d => exact hsoftmax d hd
  | mma d => exact MmaTracking.next_tracked hpre hX (hs g hg).machine he hd
  | tma d => exact TmaTracking.next_tracked hpre hX (hs g hg).machine he hd
  | index d => exact Wg1Index.next_tracked hpre hX (fun h hh => (hs h hh).machine) he hd
  | idle s => exact idle_next_tracked s e
  | wg2 d =>
    obtain ⟨o, hf⟩ := (hs g hg).machine.produces (hX.thr g hg) |>.fired_at he hd
    exact Wg2.next_tracked_of_finite hpre hX (hs g hg).machine
      (fun _ _ _ _ hState hGet => actual_dequant_finite hpre hX hs hGet hState) hd he hf
  | done => intro h; cases h

/-- Each non-softmax warp follows every actual event without premises about other warps. -/
theorem tracked_nonsoftmax_wg {g : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hWg : wgOf L g ≠ 0) (k : Nat) :
    Frame.stateAt (Machine.code P L) X g k ≠ some none := by
  have within (i : Nat) (hi : i ≤ (X.tr g).length) :
      Frame.stateAt (Machine.code P L) X g i ≠ some none := by
    intro hBad
    obtain ⟨j, hj, d, e, he, hd, hNext⟩ := prior_dismissal hi hBad
    apply actual_step_tracked hpre hX hs he hd ?_ hNext
    intro w hState
    have hg := Frame.lt_of_get hX he
    exact (hWg (RingRoleGeometry.of_trace hX hg (hs g hg).machine hState)).elim
  by_cases hk : k ≤ (X.tr g).length
  · exact within k hk
  · rw [Frame.stateAt_of_le (by omega)]
    exact within _ le_rfl

/-- Only softmax successors remain in the causal tracking induction. -/
theorem tracked_of_causal_softmax_steps
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hsoftmax : ∀ {g i d e}, X.get (g, i) = some e →
      Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) →
      (∀ w, baseCausality L X w (g, i) → ¬ Dismisses P L X w) →
      Machine.next P L g (.wg0 d) e ≠ some none) :
    Frame.Tracked (Machine.code P L) X := by
  apply tracked_of_causal_steps hX
  intro g i d e he hd hPrior
  exact actual_step_tracked hpre hX hs he hd (fun _ h => hsoftmax he h hPrior)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
