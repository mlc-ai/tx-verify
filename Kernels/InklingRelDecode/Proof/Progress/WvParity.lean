-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WySoft
public import Kernels.InklingRelDecode.Proof.Interface.WvAnchor

@[expose] public section

/-!
# `MmaParity`: the MMA warp's polls at its end state have the parity of its successful polls

A lane of the MMA warp at its poll of `kv_ready (i % 3)` (`kvWait`) has made `i / 3` successful
polls of it, and at its poll of `p_ready ((i - 1) % 2)` (`pWait`) `(i - 1) / 2` (the counts of the
anchored run at the end of the trace, `Wv.mma_polls_le`); these are the parities `PollAt` names.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Progress

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0}

/-- **`Wy.MmaParity`.** -/
theorem mmaParity_of (hpre : Pre Q L mem0)
    (hF : ∀ X, Consistent L kernel asms mem0 X → ThreadFacts Q L mem0 X)
    (hR : ∀ X, Consistent L kernel asms mem0 X → RoleReads L X) : Wy.MmaParity Q L mem0 := by
  intro X g d P m par hX hg hσ hat
  have hs : d.site ≠ .setMaxReg := by
    rcases hat with ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> rw [h] <;> nofun
  obtain ⟨hp, hk⟩ := Proof.Wv.mma_polls_le hpre hX (hF X hX) (hR X hX) le_rfl hσ hs
  rw [List.take_length] at hp hk
  rcases hat with ⟨hw, rfl, rfl⟩ | ⟨hw, rfl, rfl⟩
  · rw [hk _ (Nat.mod_lt _ (by omega))]
    have h1 : Ring.Mm.polled d = d.i := by simp [Ring.Mm.polled, hw]
    rw [h1, Ring.below_of_slot (by omega) rfl, Nat.mod_mod]
  · rw [hp _ (Nat.mod_lt _ (by omega))]
    have h1 : SO.Mm.pPolled d = d.i - 1 := by simp [SO.Mm.pPolled, hw]
    rw [h1, SO.below2_of_buf (by omega) rfl, Nat.mod_mod]

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wv
