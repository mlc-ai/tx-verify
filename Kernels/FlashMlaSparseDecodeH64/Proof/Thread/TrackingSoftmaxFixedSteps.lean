-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Tracking
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCausalInduction
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
public import Lemmas.Step.CtaBarNamed
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxWriteRegs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingReadGuards

@[expose] public section

/-! # Softmax successors determined by concrete instruction shape -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {g i : Nat} {d : Wg0.D} {e : Event}

private theorem early_load_tracked
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hSite : d.site = .sink ∨ d.site = .lenOrig ∨ d.site = .lenExtra) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  intro hBad
  obtain ⟨start, hLe, first, hMask, _, hFirst⟩ :=
    dismissed_wg0_first_mask_ready hpre hX hs he hd hBad
  obtain ⟨t, _, hFire, hRegion, _⟩ :=
    softmax_write_regs_at_event hX hs hMask hFirst he hLe
  have hPc := (PTX.EventFrame.estep_source_pc hFire).symm.trans (Frame.event_pc hs hX he hd)
  change t.pc = d.site.pc at hPc
  rw [hPc] at hRegion
  rcases hSite with h | h | h <;> rw [h] at hRegion <;> exact (by decide : ¬ _) hRegion

/-- These are the sites that check a numerical value from the current or a prior block. -/
def SoftmaxDataSite : Wg0.Site → Prop
  | .maskRead | .peerRead _ | .maxRead | .rescaleVote | .rescaleFence | .rescaleWait _
  | .lseRead | .oWait _ => True
  | _ => False

/-- Every other softmax instruction follows by its actual event shape and fixed launch inputs. -/
theorem fixed_softmax_next
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hData : ¬ SoftmaxDataSite d.site) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  by_cases hControl : Wg0.ControlSite d.site
  · exact Wg0.control_ne_dismiss hControl
  obtain ⟨o, hf⟩ := (Frame.trace hs hX (Frame.lt_of_get hX he)).fired_at he hd
  cases o with
  | none => simp [Wg0.composed_ending_next hf]
  | some u =>
    cases hSite : d.site <;>
      simp only [hSite, SoftmaxDataSite, Wg0.ControlSite, not_true_eq_false] at hData hControl
    case sink => exact early_load_tracked hpre hX hs he hd (.inl hSite)
    case lenOrig => exact early_load_tracked hpre hX hs he hd (.inr (.inl hSite))
    case lenExtra => exact early_load_tracked hpre hX hs he hd (.inr (.inr hSite))
    case scoreLoad =>
      exact softmax_first_mask_prefix_next hpre hX hs he hd
        (.inr (by rw [hSite]; trivial))
    case exchStore j =>
      obtain ⟨_, hn, _, _⟩ := Wg0.composed_exchange_next hpre hSite hf
      simp [hn]
    case rowMax => simp [Wg0.composed_rowMax_next hpre hSite hf]
    case pStore j => exact Wg0.composed_probabilityStore_ne_dismiss hpre hSite hf
    case lseStore0 => simp [Wg0.composed_halfSumStore_next hpre hSite hf]
    case lseStore => simp [Wg0.composed_lseStore_next hpre (Frame.lt_of_get hX he) hSite hf]
    case oStage j k =>
      exact Wg0.composed_stageStore_ne_dismiss hpre (Frame.lt_of_get hX he) hSite hf

/-- A dismissed softmax prefix identifies the numerical guard that dismissed it. -/
theorem dismissed_softmax_guard
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hWg : wgOf L g = 0) (he : X.get (g, i) = some e)
    (hDismiss : Frame.stateAt (Machine.code P L) X g i = some none) :
    ∃ j < i, ∃ q : Wg0.D, ∃ f,
      X.get (g, j) = some f ∧ Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      SoftmaxDataSite q.site ∧ Execution.isBarId 9 f = false ∧ Dismisses P L X (g, j) := by
  obtain ⟨j, hj, role, f, hf, hState, hn⟩ := prior_dismissal (PTX.len_of_get he).le hDismiss
  have hg := Frame.lt_of_get hX hf
  have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
  cases dismissal_is_consumer hpre hX hs hf hState hn with
  | wg0 q =>
    have hData : SoftmaxDataSite q.site := by
      by_contra hNoData
      exact fixed_softmax_next hpre hX hs hf hState hNoData hn
    have hNoBar : Execution.isBarId 9 f = false := by
      cases hKind : f.kind <;> try simp [Execution.isBarId, hKind]
      case bar id count mode =>
        by_cases hId : id = 9
        · subst id
          obtain ⟨_, hFired⟩ := (Frame.trace hs hX hg).fired_at hf hState
          obtain ⟨other, hEq, hSite, _, _, _⟩ := Wg0BarrierTrace.bar9_fired hpre hFired hKind
          obtain rfl := Machine.ThreadD.wg0.inj hEq
          cases hQ : q.site <;> simp [SoftmaxDataSite, Wg0BarrierTrace.Bar9Site, hQ] at hData hSite
        · cases f
          cases hKind
          simp [hId]
    exact ⟨j, hj, q, f, hf, hState, hData, hNoBar, _, _, hf, hState, hn⟩
  | wg2 d => change wgOf L g = 2 at hRole; omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
