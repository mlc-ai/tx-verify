-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreMaskStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerSuccessor
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerWordsHistory

@[expose] public section

/-! # The peer exchange from actual final QK result cells -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerQkValues

open PTX PTX.Proof PTX.Flow GemmRing Wg0 MachineTracking

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Result cells of the final QK issue of every block reaching a validity-mask load. -/
def QkValues (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ (cta issuer i : Nat) (lane : Fin 128) (d : D),
    MmaIssuer P L X cta issuer →
    Frame.stateAt (Machine.code P L) X (softmax L cta lane) i = some (some (.wg0 d)) →
    d.site = .maskRead → i < (X.tr (softmax L cta lane)).length →
    ScoreMaskStep.QkScoreValues P L X cta issuer d.block lane

private theorem real_of_mask {g i : Nat} {d : D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hv : QkValues P L X)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .maskRead) : RealScores d.ownScores ∧ RealScores d.peerScores := by
  have hg := Frame.lt_of_get hX he
  have hrole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
  change wgOf L g = 0 at hrole
  let cta := ctaOf L g
  obtain ⟨lane, hLane⟩ := softmax_thread hpre (cta := cta) rfl hrole
  obtain ⟨issuer, hIssuer⟩ := exists_issuer (cta := cta) hpre hX (fun g hg => (hs g hg).machine)
  have hlen := PTX.len_of_get he
  rw [hLane] at hd hlen
  exact ScoreMaskStep.real_scores_of_qk_values hpre hX hs hIssuer hd hsite
    (Nat.le_of_lt hlen) (hv cta issuer i lane d hIssuer hd hsite hlen)

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
include hpre hX hs

/-- Both the stored peer words and the reader's own words come from actual QK result cells. -/
theorem real_scores (hv : QkValues P L X) :
    Wg0PeerSuccessor.PeerScoresReal P L X ∧ Wg0PeerSuccessor.OwnScoresReal P L X := by
  have hReal {g i : Nat} {d : D}
      (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
      (hsite : ScoreExchangeSite d.site) : RealScores d.ownScores ∧ RealScores d.peerScores :=
    real_scores_from_mask hd hsite (fun _ _ _ he hm hd =>
      real_of_mask hpre hX hs hv he hm hd)
  exact ⟨fun g i d group hd hsite => (hReal hd (by rw [hsite]; trivial)).2,
    fun g i d group hd hsite => (hReal hd (by rw [hsite]; trivial)).1⟩

/-- The two peer reads proceed once the actual final QK issues supply their result cells. -/
theorem never_dismiss (ht : Frame.Tracked (Machine.code P L) X) (hv : QkValues P L X) {g i : Nat}
    {d : D} {e : Event} {group : Fin 8} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .peerRead group) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  obtain ⟨hpeer, hown⟩ := real_scores hpre hX hs hv
  exact Wg0PeerSuccessor.never_dismiss hpre hX hs ht hpeer hown he hd hsite

/-- The actual precision of the QK cells closes the two peer-read guards. -/
theorem actual_never_dismiss (hv : QkValues P L X) {g i : Nat} {d : D} {e : Event} {group : Fin 8}
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .peerRead group)
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ Dismisses P L X t) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  obtain ⟨hpeer, hown⟩ := real_scores hpre hX hs hv
  exact Wg0PeerSuccessor.actual_never_dismiss hpre hX hs hpeer hown he hd hsite hPrior

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerQkValues
