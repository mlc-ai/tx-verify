-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.RsElect
public import Kernels.InklingRelDecode.Proof.Interface.RdQkBack

@[expose] public section

/-!
# The MMA lane at a QK or PV step led every election

`Interface.lead_of_pv0` and `lead_of_finCommit` give `ElectLead` for a lane at PV step 0 and at the
`o_final` commit. A lane at any step `j` of the QK half or of the PV half is the successor, eight
or fewer events later, of the election that returned its lane: `lead_of_qk`, `lead_of_pv`, by
induction on `j` (the step `j + 1` follows step `j`, step `0` follows the election).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The step into QK step `j`: from the election (step 0) or from step `j - 1`. -/
theorem next_qk {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d)) {j : Fin 8}
    (hs : d.site = .qk j) :
    (j.val = 0 ∧ ∃ mask inst ld, e.kind = .elect mask inst ld ∧ ld = laneOf L g) ∨
      (0 < j.val ∧ ∃ j' : Fin 8, j'.val + 1 = j.val ∧ d0.site = .qk j') := by
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp at hs; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       first
         | (left; simp only [Mma.Site.qk.injEq] at hs; subst hs
            exact ⟨rfl, _, _, _, by assumption, by omega⟩)
         | (right; simp only [Mma.Site.qk.injEq] at hs; subst hs
            rename_i j' hj hh
            exact ⟨Nat.succ_pos _, j', rfl, by rw [hj]⟩))

/-- **The MMA lane at a QK step led every election.** -/
theorem lead_of_qk (hX : Consistent L kernel asms mem0 X) :
    ∀ (n : Nat) {k : Nat} {d : Mma.D} {P : Loader.Pro} {j : Fin 8}, j.val = n →
      k < (X.tr g).length → St Q L X g k = some (some (.w (.mma d P))) → d.site = .qk j →
      ElectLead L g (X.tr g) := by
  intro n
  induction n with
  | zero =>
    intro k d P j hj hk hσ hs
    obtain ⟨k0, e, d0, hadj, hg0, he, hs0, hn⟩ :=
      mma_state_pred_adj hX hk hσ (by rw [hs]; nofun)
    rcases next_qk hn hs with ⟨-, mask, inst, ld, hke, hld⟩ | ⟨hpos, -⟩
    · refine electLead_of_elected hX ⟨e, List.mem_of_getElem?
        (show (X.tr g)[k0]? = some e from he), mask, inst, ?_⟩
      rw [hke, hld]
    · omega
  | succ n ih =>
    intro k d P j hj hk hσ hs
    obtain ⟨k0, e, d0, hadj, hg0, he, hs0, hn⟩ :=
      mma_state_pred_adj hX hk hσ (by rw [hs]; nofun)
    rcases next_qk hn hs with ⟨hz, -⟩ | ⟨-, j', hj', hs'⟩
    · omega
    · exact ih (j := j') (by omega) (by omega) hs0 hs'

/-- **The MMA lane at the QK commit led every election.** -/
theorem lead_of_qkCommit (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k : Nat} {d : Mma.D} {P : Loader.Pro}
    (hk : k < (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.mma d P))))
    (hs : d.site = .qkCommit) : ElectLead L g (X.tr g) := by
  obtain ⟨k', d', hadj, hσ', hs', -⟩ := exists_qk7 hpre hX hf hk hσ hs
  exact lead_of_qk hX 7 (j := 7) rfl (by omega) hσ' hs'

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
