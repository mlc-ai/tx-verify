-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOMmaCount

@[expose] public section

/-!
# The events of the MMA warp that the S/P/O handshake counts

What the event that fires at an MMA state is, as a count on each barrier of the handshake
(`MmShape` says what the event is; here it is read as "is it a poll of / a commit to this barrier"):

* `mm_okPoll_p`: a successful poll of `p_ready b` exactly at the `pWait` site of an iteration whose
  block `i - 1` is in buffer `b`;
* `mm_commitsTo_s`: a commit to `s_ready b` exactly at the `qkCommit` site of an iteration whose
  block `i` is in buffer `b`;
* `mm_commitsTo_o`, `mm_commitsTo_f`: a commit to `o_done` (`o_final`) exactly at `pvCommit2`
  (`finCommit`).

The barriers are distinct locations (`*_ne_*`): the two buffers of a family, and the families, have
different offsets.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Ring (okW)
open PTX.Kernels.InklingRelDecode.Proof.EvW (MmShape mma_shape sReady pReady oDone oFinal)

noncomputable section
set_option maxRecDepth 100000

/-! ### The barriers, as distinct locations -/

theorem sReady_eq_iff {L : Launch} {c b b' : Nat} : sReady L c b = sReady L c b' ↔ b = b' := by
  simp [sReady, EvW.barLoc, EvW.sReadyOff]

theorem pReady_eq_iff {L : Launch} {c b b' : Nat} : pReady L c b = pReady L c b' ↔ b = b' := by
  simp [pReady, EvW.barLoc, EvW.pReadyOff]

theorem kvEmpty_ne_sReady {L : Launch} {c s b : Nat} (hs : s < 3) (hb : b < 2) :
    EvW.kvEmpty L c s ≠ sReady L c b := by
  simp only [EvW.kvEmpty, sReady, EvW.barLoc, EvW.kvEmptyOff, EvW.sReadyOff, ne_eq, Loc.mk.injEq]
  omega

theorem oDone_ne_sReady {L : Launch} {c b : Nat} (hb : b < 2) : oDone L c ≠ sReady L c b := by
  simp only [oDone, sReady, EvW.barLoc, EvW.oDoneOff, EvW.sReadyOff, ne_eq, Loc.mk.injEq]
  omega

theorem oFinal_ne_sReady {L : Launch} {c b : Nat} (hb : b < 2) : oFinal L c ≠ sReady L c b := by
  simp only [oFinal, sReady, EvW.barLoc, EvW.oFinalOff, EvW.sReadyOff, ne_eq, Loc.mk.injEq]
  omega

theorem kvReady_ne_pReady {L : Launch} {c s b : Nat} (hs : s < 3) (hb : b < 2) :
    EvW.kvReady L c s ≠ pReady L c b := by
  simp only [EvW.kvReady, pReady, EvW.barLoc, EvW.kvReadyOff, EvW.pReadyOff, ne_eq, Loc.mk.injEq]
  omega

theorem kvEmpty_ne_oDone {L : Launch} {c s : Nat} (hs : s < 3) :
    EvW.kvEmpty L c s ≠ oDone L c := by
  simp only [EvW.kvEmpty, oDone, EvW.barLoc, EvW.kvEmptyOff, EvW.oDoneOff, ne_eq, Loc.mk.injEq]
  omega

theorem sReady_ne_oDone {L : Launch} {c b : Nat} (hb : b < 2) : sReady L c b ≠ oDone L c := by
  simp only [oDone, sReady, EvW.barLoc, EvW.oDoneOff, EvW.sReadyOff, ne_eq, Loc.mk.injEq]
  omega

theorem oFinal_ne_oDone {L : Launch} {c : Nat} : oFinal L c ≠ oDone L c := by
  simp only [oDone, oFinal, EvW.barLoc, EvW.oDoneOff, EvW.oFinalOff, ne_eq, Loc.mk.injEq]
  omega

theorem kvEmpty_ne_oFinal {L : Launch} {c s : Nat} (hs : s < 3) :
    EvW.kvEmpty L c s ≠ oFinal L c := by
  simp only [EvW.kvEmpty, oFinal, EvW.barLoc, EvW.kvEmptyOff, EvW.oFinalOff, ne_eq, Loc.mk.injEq]
  omega

theorem sReady_ne_oFinal {L : Launch} {c b : Nat} (hb : b < 2) : sReady L c b ≠ oFinal L c := by
  simp only [oFinal, sReady, EvW.barLoc, EvW.oFinalOff, EvW.sReadyOff, ne_eq, Loc.mk.injEq]
  omega

theorem oDone_ne_oFinal {L : Launch} {c : Nat} : oDone L c ≠ oFinal L c := by
  simp only [oDone, oFinal, EvW.barLoc, EvW.oDoneOff, EvW.oFinalOff, ne_eq, Loc.mk.injEq]
  omega

variable {Q : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {u : TState} {e : Event}

/-! ### What the fired event is -/

/-- **The event of an MMA state, as a count of `p_ready` polls.** -/
theorem mm_okPoll_p (hpre : Pre Q L mem0) (hg : g < L.threads) {d : Mma.D} {P : Loader.Pro}
    (hF : (WComp.code L g Q).toMachine.Fired (some (.mma d P)) e (some u)) {b : Nat}
    (hb : b < 2) :
    okPoll (pReady L (g / L.block) b) e =
      (decide (d.site = .pWait ∧ (d.i - 1) % 2 = b) && okW e) := by
  have hsh := mma_shape hpre hg hF
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site <;> simp only [MmShape] at hsh
  case kvWait =>
    obtain ⟨ok, rfl⟩ := hsh
    cases ok <;> simp [okPoll, sourceWaitSuccess, okW, kvReady_ne_pReady (s := i % 3) (by omega) hb]
  case pWait =>
    obtain ⟨ok, rfl⟩ := hsh
    cases ok <;> simp [okPoll, sourceWaitSuccess, okW, pReady_eq_iff]
  all_goals first
    | obtain ⟨_, _, rfl, -⟩ := hsh
    | obtain ⟨_, _, rfl⟩ := hsh
    | obtain ⟨_, rfl⟩ := hsh
    | obtain rfl := hsh
    | obtain ⟨_, _, _, _, _, _, rfl⟩ := hsh
  all_goals simp [okPoll, sourceWaitSuccess, okW]

/-- The same for an event of a step: one that fires, or one that ends the thread. -/
theorem mm_okPoll_p_step (hpre : Pre Q L mem0) (hg : g < L.threads) {d : Mma.D}
    {P : Loader.Pro}
    (hev : (∃ u, (WComp.code L g Q).toMachine.Fired (some (.mma d P)) e (some u)) ∨ Ends e)
    {b : Nat} (hb : b < 2) :
    okPoll (pReady L (g / L.block) b) e =
      (decide (d.site = .pWait ∧ (d.i - 1) % 2 = b) && okW e) := by
  rcases hev with ⟨u, hF⟩ | hend
  · exact mm_okPoll_p hpre hg hF hb
  · obtain ⟨pc, k⟩ := e
    have hk : ∀ l p ok acq sc, k ≠ Kind.wait l p ok acq sc := by
      rcases hend with ⟨f, h⟩ | h <;> intro l p ok acq sc hh <;> simp only at h <;> subst h <;>
        cases hh
    have h1 : okPoll (pReady L (g / L.block) b) ⟨pc, k⟩ = false :=
      okPoll_notWait (fun l p ok acq sc h => hk l p ok acq sc h)
    have h2 : okW ⟨pc, k⟩ = false := by
      cases k <;> first | rfl | exact absurd rfl (hk _ _ _ _ _)
    rw [h1, h2]
    simp

/-- **The event of an MMA state, as a count of commits to `s_ready`.** -/
theorem mm_commitsTo_s (hpre : Pre Q L mem0) (hg : g < L.threads) {d : Mma.D} {P : Loader.Pro}
    (hF : (WComp.code L g Q).toMachine.Fired (some (.mma d P)) e (some u)) {b : Nat}
    (hb : b < 2) :
    commitsTo (sReady L (g / L.block) b) e = decide (d.site = .qkCommit ∧ d.i % 2 = b) := by
  have hsh := mma_shape hpre hg hF
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site <;> simp only [MmShape] at hsh
  case qkCommit =>
    subst hsh
    simp [commitsTo, EvW.commitSpec, sReady_eq_iff]
  case pvCommit1 =>
    subst hsh
    simp [commitsTo, EvW.commitSpec, kvEmpty_ne_sReady (s := (i - 1) % 3) (by omega) hb]
  case pvCommit2 =>
    subst hsh
    simp [commitsTo, EvW.commitSpec, oDone_ne_sReady hb]
  case finCommit =>
    subst hsh
    simp [commitsTo, EvW.commitSpec, oFinal_ne_sReady hb]
  all_goals first
    | obtain ⟨_, _, rfl, -⟩ := hsh
    | obtain ⟨_, _, rfl⟩ := hsh
    | obtain ⟨_, rfl⟩ := hsh
    | obtain rfl := hsh
    | obtain ⟨_, _, _, _, _, _, rfl⟩ := hsh
  all_goals simp [commitsTo]

/-- **The event of an MMA state, as a count of commits to `o_done`.** -/
theorem mm_commitsTo_o (hpre : Pre Q L mem0) (hg : g < L.threads) {d : Mma.D} {P : Loader.Pro}
    (hF : (WComp.code L g Q).toMachine.Fired (some (.mma d P)) e (some u)) :
    commitsTo (oDone L (g / L.block)) e = decide (d.site = .pvCommit2) := by
  have hsh := mma_shape hpre hg hF
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site <;> simp only [MmShape] at hsh
  case qkCommit =>
    subst hsh
    simp [commitsTo, EvW.commitSpec, sReady_ne_oDone (b := i % 2) (by omega)]
  case pvCommit1 =>
    subst hsh
    simp [commitsTo, EvW.commitSpec, kvEmpty_ne_oDone (s := (i - 1) % 3) (by omega)]
  case pvCommit2 =>
    subst hsh
    simp [commitsTo, EvW.commitSpec]
  case finCommit =>
    subst hsh
    simp [commitsTo, EvW.commitSpec, oFinal_ne_oDone]
  all_goals first
    | obtain ⟨_, _, rfl, -⟩ := hsh
    | obtain ⟨_, _, rfl⟩ := hsh
    | obtain ⟨_, rfl⟩ := hsh
    | obtain rfl := hsh
    | obtain ⟨_, _, _, _, _, _, rfl⟩ := hsh
  all_goals simp [commitsTo]

/-- **The event of an MMA state, as a count of commits to `o_final`.** -/
theorem mm_commitsTo_f (hpre : Pre Q L mem0) (hg : g < L.threads) {d : Mma.D} {P : Loader.Pro}
    (hF : (WComp.code L g Q).toMachine.Fired (some (.mma d P)) e (some u)) :
    commitsTo (oFinal L (g / L.block)) e = decide (d.site = .finCommit) := by
  have hsh := mma_shape hpre hg hF
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site <;> simp only [MmShape] at hsh
  case qkCommit =>
    subst hsh
    simp [commitsTo, EvW.commitSpec, sReady_ne_oFinal (b := i % 2) (by omega)]
  case pvCommit1 =>
    subst hsh
    simp [commitsTo, EvW.commitSpec, kvEmpty_ne_oFinal (s := (i - 1) % 3) (by omega)]
  case pvCommit2 =>
    subst hsh
    simp [commitsTo, EvW.commitSpec, oDone_ne_oFinal]
  case finCommit =>
    subst hsh
    simp [commitsTo, EvW.commitSpec]
  all_goals first
    | obtain ⟨_, _, rfl, -⟩ := hsh
    | obtain ⟨_, _, rfl⟩ := hsh
    | obtain ⟨_, rfl⟩ := hsh
    | obtain rfl := hsh
    | obtain ⟨_, _, _, _, _, _, rfl⟩ := hsh
  all_goals simp [commitsTo]

end
end PTX.Kernels.InklingRelDecode.Proof.SO
