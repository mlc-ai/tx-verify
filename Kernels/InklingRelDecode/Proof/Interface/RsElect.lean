-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.RsMmaBack
public import Lemmas.Flow.ElectMask
public import Lemmas.Flow.ElectLead
public import Kernels.InklingRelDecode.Proof2.Lib.Elect

@[expose] public section

/-!
# The MMA warp's lane leads every election

Each of the kernel's `elect.sync` instructions names the immediate `-1` as its member mask
(`electMaskOk`, decided on the decoded code), so every election event of a consistent execution
carries the full mask (`elect_full`, `electMask_full`; as for FlashAttn-4's `ElectFull`). A thread
that has an election returning its own lane then led every election of its trace
(`Lemmas.Flow.electLead_or_nonLead`): the MMA warp's thread at PV step 0 or at `finCommit` has such
an election, the one before it (the successor of `pvElect` or `finElect` is `pv 0` or `finCommit`
only for the lane the election returned). `ElectLead L g (X.tr g)` is the premise of
`Interface.exists_pv7` and `fin_iter`, so those two take no premise on the election.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The step into PV step 0 is the successor of an election that returned the thread's lane. -/
theorem next_pv0 {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d))
    (hs : d.site = .pv 0) : ∃ mask inst ld, e.kind = .elect mask inst ld ∧ ld = laneOf L g := by
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp at hs; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       exact ⟨_, _, _, by assumption, by omega⟩)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The step into `finCommit` is the successor of an election that returned the thread's lane. -/
theorem next_finCommit {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d))
    (hs : d.site = .finCommit) :
    ∃ mask inst ld, e.kind = .elect mask inst ld ∧ ld = laneOf L g := by
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp at hs; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       exact ⟨_, _, _, by assumption, by omega⟩)

/-- **The MMA lane at PV step 0 led every election.** -/
theorem lead_of_pv0 (hX : Consistent L kernel asms mem0 X) {k : Nat} {d : Mma.D}
    {P : Loader.Pro} (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site = .pv 0) :
    ElectLead L g (X.tr g) := by
  obtain ⟨k0, e, d0, hadj, hg0, he, hs0, hn⟩ :=
    mma_state_pred_adj hX hk hσ (by rw [hs]; nofun)
  obtain ⟨mask, inst, ld, hke, hld⟩ := next_pv0 hn hs
  refine electLead_of_elected hX ⟨e, List.mem_of_getElem? (show (X.tr g)[k0]? = some e from he),
    mask, inst, ?_⟩
  rw [hke, hld]

/-- **The MMA lane at `finCommit` led every election.** -/
theorem lead_of_finCommit (hX : Consistent L kernel asms mem0 X) {k : Nat} {d : Mma.D}
    {P : Loader.Pro} (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site = .finCommit) :
    ElectLead L g (X.tr g) := by
  obtain ⟨k0, e, d0, hadj, hg0, he, hs0, hn⟩ :=
    mma_state_pred_adj hX hk hσ (by rw [hs]; nofun)
  obtain ⟨mask, inst, ld, hke, hld⟩ := next_finCommit hn hs
  refine electLead_of_elected hX ⟨e, List.mem_of_getElem? (show (X.tr g)[k0]? = some e from he),
    mask, inst, ?_⟩
  rw [hke, hld]

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
