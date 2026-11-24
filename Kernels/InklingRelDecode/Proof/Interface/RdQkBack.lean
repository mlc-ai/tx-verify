-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.RsMmaBack

@[expose] public section

/-!
# The MMA warp's last QK MMA of an iteration (backward from its commit)

The QK analogue of `Interface.exists_pv7`: an MMA-warp state at the site `qkCommit` of iteration
`i` is preceded, at the previous event, by the state at step 7 of the QK half of iteration `i`,
with the same Tensor Memory base and `num_iters`, and that event is an MMA. The commit follows
step 7 and nothing else (`Mma.qkNext`), so no election premise is needed.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}

/-- **One step of the MMA machine, backwards, into the QK commit.** The state before the QK commit
is step 7 of the QK half of the same iteration, with the same Tensor Memory base and
`num_iters`. -/
theorem next_qkCommit {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d))
    (hs : d.site = .qkCommit) :
    d0.site = .qk 7 ∧ d.i = d0.i ∧ d.tm = d0.tm ∧ d.n = d0.n := by
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       rename_i j hj hh
       simp only at hs
       refine ⟨?_, rfl, rfl, rfl⟩
       have : j = 7 := Fin.ext (by omega)
       rw [hj, this])

/-- **The last QK MMA of an iteration.** An MMA-warp state of thread `g` at an event, at the
site `qkCommit` of iteration `i`, has the state at step 7 of the QK half of that iteration one
event before it, with the same Tensor Memory base and `num_iters` and an MMA event. -/
theorem exists_qk7 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k : Nat} {d : Mma.D} {P : Loader.Pro}
    (hk : k < (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.mma d P))))
    (hs : d.site = .qkCommit) :
    ∃ (k' : Nat) (d' : Mma.D), k' + 1 = k ∧ St Q L X g k' = some (some (.w (.mma d' P))) ∧
      d'.site = .qk 7 ∧ d'.i = d.i ∧ d'.tm = d.tm ∧ d'.n = d.n ∧
      ∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩ := by
  have hsite : d.site ≠ .setMaxReg := by rw [hs]; nofun
  obtain ⟨k0, e, d0, hadj, hg0, he, hs0, hn⟩ := mma_state_pred_adj hX hk hσ hsite
  obtain ⟨h7, hi, htm, hnn⟩ := next_qkCommit hn hs
  refine ⟨k0, d0, hadj, hs0, h7, hi.symm, htm.symm, hnn.symm, ?_⟩
  obtain ⟨pc, dst, sp, acc, mask, h⟩ := mma_issue_event hpre hX hf hg0 he hs0 (.inl ⟨7, h7⟩)
  exact ⟨pc, dst, sp, acc, mask, by rw [he, h]⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
