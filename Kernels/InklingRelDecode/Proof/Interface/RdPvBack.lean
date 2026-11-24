-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.RdElect

@[expose] public section

/-!
# The MMA warp's last PV MMA of an iteration, from the `o_done` commit

The PV analogue of `exists_qk7`: the state at the site `pvCommit2` of iteration `i` is preceded by
`pvCommit1` and, before it, by step 7 of the PV half of the same iteration (`exists_pv7_commit2`,
two events before, with the same Tensor Memory base and `num_iters` and an MMA event), and a lane at
any PV step led every election (`lead_of_pv`, `lead_of_pvCommit2`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}

/-- The state before `pvCommit2` is `pvCommit1` of the same iteration. -/
theorem next_pvCommit2 {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d))
    (hs : d.site = .pvCommit2) :
    d0.site = .pvCommit1 ∧ d.i = d0.i ∧ d.tm = d0.tm ∧ d.n = d0.n := by
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all)

/-- The state before `pvCommit1` is step 7 of the PV half of the same iteration. -/
theorem next_pvCommit1 {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d))
    (hs : d.site = .pvCommit1) :
    d0.site = .pv 7 ∧ d.i = d0.i ∧ d.tm = d0.tm ∧ d.n = d0.n := by
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       rename_i j hj hh
       refine ⟨?_, rfl, rfl, rfl⟩
       have : j = 7 := Fin.ext (by omega)
       rw [hj, this])

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The step into PV step `j`: from the election (step 0) or from step `j - 1`. -/
theorem next_pv {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d)) {j : Fin 8}
    (hs : d.site = .pv j) :
    (j.val = 0 ∧ ∃ mask inst ld, e.kind = .elect mask inst ld ∧ ld = laneOf L g) ∨
      (0 < j.val ∧ ∃ j' : Fin 8, j'.val + 1 = j.val ∧ d0.site = .pv j') := by
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp at hs; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       first
         | (left; simp only [Mma.Site.pv.injEq] at hs; subst hs
            exact ⟨rfl, _, _, _, by assumption, by omega⟩)
         | (right; simp only [Mma.Site.pv.injEq] at hs; subst hs
            rename_i j' hj hh
            exact ⟨Nat.succ_pos _, j', rfl, by rw [hj]⟩))

/-- **The MMA lane at a PV step led every election.** -/
theorem lead_of_pv (hX : Consistent L kernel asms mem0 X) :
    ∀ (n : Nat) {k : Nat} {d : Mma.D} {P : Loader.Pro} {j : Fin 8}, j.val = n →
      k < (X.tr g).length → St Q L X g k = some (some (.w (.mma d P))) → d.site = .pv j →
      ElectLead L g (X.tr g) := by
  intro n
  induction n with
  | zero =>
    intro k d P j hj hk hσ hs
    obtain ⟨k0, e, d0, hadj, hg0, he, hs0, hn⟩ :=
      mma_state_pred_adj hX hk hσ (by rw [hs]; nofun)
    rcases next_pv hn hs with ⟨-, mask, inst, ld, hke, hld⟩ | ⟨hpos, -⟩
    · refine electLead_of_elected hX ⟨e, List.mem_of_getElem?
        (show (X.tr g)[k0]? = some e from he), mask, inst, ?_⟩
      rw [hke, hld]
    · omega
  | succ n ih =>
    intro k d P j hj hk hσ hs
    obtain ⟨k0, e, d0, hadj, hg0, he, hs0, hn⟩ :=
      mma_state_pred_adj hX hk hσ (by rw [hs]; nofun)
    rcases next_pv hn hs with ⟨hz, -⟩ | ⟨-, j', hj', hs'⟩
    · omega
    · exact ih (j := j') (by omega) (by omega) hs0 hs'

/-- **The last PV MMA of an iteration.** The state at `pvCommit2` at event `k` has the state at
PV step 7 of the same iteration two events before it, with the same Tensor Memory base and
`num_iters` and an MMA event, and the lane led every election. -/
theorem exists_pv7_commit2 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k : Nat} {d : Mma.D} {P : Loader.Pro}
    (hk : k < (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.mma d P))))
    (hs : d.site = .pvCommit2) :
    ElectLead L g (X.tr g) ∧
      ∃ (k' : Nat) (d' d1 : Mma.D), k' + 2 = k ∧ St Q L X g k' = some (some (.w (.mma d' P))) ∧
        d'.site = .pv 7 ∧ d'.i = d.i ∧ d'.tm = d.tm ∧ d'.n = d.n ∧
        St Q L X g (k' + 1) = some (some (.w (.mma d1 P))) ∧ d1.site = .pvCommit1 ∧
        ∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩ := by
  obtain ⟨k1, e1, d1, hadj1, hg1, he1, hs1, hn1⟩ :=
    mma_state_pred_adj hX hk hσ (by rw [hs]; nofun)
  obtain ⟨h1, hi1, htm1, hnn1⟩ := next_pvCommit2 hn1 hs
  obtain ⟨k2, e2, d2, hadj2, hg2, he2, hs2, hn2⟩ :=
    mma_state_pred_adj hX (by omega) hs1 (by rw [h1]; nofun)
  obtain ⟨h2, hi2, htm2, hnn2⟩ := next_pvCommit1 hn2 h1
  have hlead : ElectLead L g (X.tr g) := lead_of_pv hX 7 (j := 7) rfl (by omega) hs2 h2
  have hk1 : k1 = k2 + 1 := by omega
  refine ⟨hlead, k2, d2, d1, by omega, hs2, h2, by omega, by omega, by omega,
    by rw [← hk1]; exact hs1, h1, ?_⟩
  obtain ⟨pc, dst, sp, acc, mask, h⟩ := mma_issue_event hpre hX hf hg2 he2 hs2 (.inr ⟨7, h2⟩)
  exact ⟨pc, dst, sp, acc, mask, by rw [he2, h]⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
