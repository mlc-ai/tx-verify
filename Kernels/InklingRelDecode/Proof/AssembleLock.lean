-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.AssembleBase
public import Kernels.InklingRelDecode.Proof.Interface.Lk2Agree
public import Kernels.InklingRelDecode.Proof.Protocol.LkBar
public import Kernels.InklingRelDecode.Proof.Protocol.LkB0
public import Kernels.InklingRelDecode.Proof.Protocol.MmBcast

@[expose] public section

/-!
# The lockstep of the lanes of a warp, from the base and the softmax premise

`Interface.Lk.LaneAgree` (the agreement of two lanes of a warp at their synchronizing events on what
steers the branch to the next one) splits into the softmax region's lazy-rescale decision
(`LaneAgreeSm`) and every other row (`LaneAgreeRest`, `Interface.Lk.laneAgreeRest_of`). Here
`LaneAgreeRest` is built from `Base` (`RoleReads`, `NumWordRead`, `BaseWordRead`, and
`NumPreRead`, which is `Interface.numPreRead_of_p2` like `NumWordRead`), so
the one premise left for the lockstep is `LaneAgreeSm`. From `LaneAgree`:

* `Base.barLanes`: `Safety.Protocol.barLanes` (`Bar.barLanes_of_agree`);
* `Base.barAligned`: `Safety.Protocol.barAligned` (the divergence half is
  `Bar.barDivergent_not_of_agree`, the exit half `Bar.barExited_not`, which needs no agreement).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Assemble
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (b : Base Q L mem0 X)
include hpre hX b

omit b in
/-- **`NumPreRead`** (`Interface.numPreRead_of_p2`). -/
theorem Base.numPreRead : NumPreRead Q L X :=
  numPreRead_of_p2 hpre hX

/-- **Every broadcast of warp 7 receives 7** (`Mb.mmaBcast_of`). -/
theorem Base.mmaBcast : Mma.MmaBcast L X :=
  Mb.mmaBcast_of hpre hX b.facts b.tmpl (Base.roleReads hpre hX)
    (Interface.baseWordRead_of hpre hX)
    (Base.numWordRead hpre hX)

/-- **No MMA state is at a skip site** (`Interface.not_skip`). -/
theorem Base.noSkip : Lk.NoSkip Q L X := by
  intro g a d P hg hσ
  have hB := Base.mmaBcast hpre hX b
  by_cases ha : a ≤ (X.tr g).length
  · exact not_skip hX (bcast_of_mma b.facts.roleWarp hB hg ha hσ) hσ
  · have he := Frame.stateAt_of_le (C := code L Q) (X := X) (g := g) (k := a) (by omega)
    have hσ' : St Q L X g (X.tr g).length = some (some (.w (.mma d P))) := by
      rw [St] at hσ ⊢
      rw [← he]
      exact hσ
    exact not_skip hX (bcast_of_mma b.facts.roleWarp hB hg le_rfl hσ') hσ

/-- **The non-softmax rows of the agreement premise** (`Interface.Lk.laneAgreeRest_of`). -/
theorem Base.laneAgreeRest : Lk.LaneAgreeRest Q L X :=
  Lk.laneAgreeRest_of hpre hX b.facts (Base.roleReads hpre hX)
    (Lk.bar0Counters_of hpre hX b.facts (Interface.baseWordRead_of hpre hX)
      (Base.numWordRead hpre hX) (Base.numPreRead hpre hX)) (Base.noSkip hpre hX b)

/-- **The agreement premise**, from the softmax region's half. -/
theorem Base.laneAgree (hsm : Lk.LaneAgreeSm Q L X) : Lk.LaneAgree Q L X :=
  Lk.laneAgree_of hsm (Base.laneAgreeRest hpre hX b)

/-- **`Safety.Protocol.barLanes`.** -/
theorem Base.barLanes (hsm : Lk.LaneAgreeSm Q L X) : ¬ Safety.BarLaneMismatch L X :=
  Bar.barLanes_of_agree hpre hX b.facts.sound b.facts.tracked (Base.laneAgree hpre hX b hsm)

/-- **`Safety.Protocol.barAligned`.** -/
theorem Base.barAligned (hsm : Lk.LaneAgreeSm Q L X) :
    ¬ AlignedClass.bar.Divergent L kernel X ∧ ¬ AlignedClass.bar.Exited L kernel X :=
  ⟨Bar.barDivergent_not_of_agree hpre hX b.facts.sound b.facts.tracked
      (Base.laneAgree hpre hX b hsm),
    Bar.barExited_not hpre hX b.facts.sound b.facts.tracked⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Assemble
