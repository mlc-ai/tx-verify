-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Common.LdWait

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow

/-- The Tensor Memory load has no reduction or packing. Its successors keep only control
registers already present before the load, all outside the returned register vector. -/
noncomputable def loadOk (before after : Site) (hook : Bool) : Bool :=
  Assumptions.tcLdDataflowSites.contains before.pc == hook &&
    match kernel.code[before.pc]? with
    | some ⟨none, .tcLd ds _ .s32x32b none⟩ =>
      (liveAt after).all (fun r => !ds.contains r && (liveAt before).contains r)
    | _ => false

theorem load_of_ok {s dst : Site} {hook : Bool} (h : loadOk s dst hook = true) :
    ∃ ds ta, kernel.code[s.pc]? = some ⟨none, .tcLd ds ta .s32x32b none⟩ ∧
      Assumptions.all.any (·.tcLdWait s.pc) = hook ∧
      (liveAt dst).all (fun r => !ds.contains r && (liveAt s).contains r) = true := by
  simp only [loadOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hw, hf⟩ := h
  split at hf
  · exact ⟨_, _, ‹_›, (Assumptions.tcLdWait_iff _).trans hw, hf⟩
  · cases hf

/-- Reduce only the decoded instruction named by the row. -/
scoped macro "load_row " src:term " via " lookup:term : tactic =>
  `(tactic| (
    unfold loadOk
    have h : kernel.code[Site.pc $src]? = _ := $lookup
    rw [h]
    decide +kernel))

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
