-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PrefixAll
public import Kernels.InklingRelDecode.Proof.Interface.ClassSm
public import Kernels.InklingRelDecode.Proof.Interface.PrefixDone
public import Kernels.InklingRelDecode.Proof.Interface.ScNum
public import Kernels.InklingRelDecode.Proof.Interface.FootRoleAll
public import Kernels.InklingRelDecode.Proof.Interface.FootRoleRead
public import Kernels.InklingRelDecode.Proof.Thread.FootRole
public import Kernels.InklingRelDecode.Proof.Interface.ShapeWords
public import Kernels.InklingRelDecode.Proof.Interface.ShapeOdone
public import Kernels.InklingRelDecode.Proof.Interface.ClassCopyPage
public import Kernels.InklingRelDecode.Proof.Protocol.IpTmAlloc
public import Kernels.InklingRelDecode.Proof2.Safety.Bar1Exit
public import Kernels.InklingRelDecode.Proof2.Safety.Box
public import Kernels.InklingRelDecode.Proof.Interface.InputRead

@[expose] public section

/-!
# The base of the assembly: the thread layer's facts and the value facts proved from them

From the tracking of the machines (`Interface.tracked_holds`) and `TmplOk` (`Interface.tmplOk`)
this file builds, for a consistent execution `X`:

* `Interface.ThreadFacts`;
* `GoodP` at every present event (`Interface.goodP_of_tracked`: the read-only input assumption
  gives the launch bytes at every read of an input byte, `Interface.launchRead_of_wf`);
* `Bar1Exits` (`Proof2.bar1Exits`, from the dependency order on the second tree's role table);
* `RoleReads` (`roleReads_of_p2`) and `NumWordRead` (`numWordRead_of_p2`), from the second
  tree's role table, `AllocWordZero` (`Tmem1.allocWordZero`) and `BaseWordRead`
  (`Interface.baseWordRead_of`).

So `RoleReads`, `BaseWordRead` and `NumWordRead` are consequences of the assumptions and the
tracking.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Assemble
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The facts the assembly builds on, for one consistent execution.** -/
structure Base (Q : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop where
  prem : Premises Q L X
  facts : ThreadFacts Q L mem0 X
  tmpl : ∀ g < L.threads, (threadCode L g Q).TmplOk
  goodP : ∀ e, Present X e → GoodP Q L mem0 X e
  bar1 : Bar1Exits L X

/-- **`Base`** from the tracking and `TmplOk`; `Bar1Exits` is proved from the dependency order
(`Proof2.bar1Exits`). -/
theorem base_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (ht : Frame.Tracked (code L Q) X) : Base Q L mem0 X :=
  ⟨premises_of_prefix hpre hX hT ht, threadFacts hpre smOb hX (premises_of_prefix hpre hX hT ht),
    hT, goodP_of_tracked hpre hX ht, (fun hf hp hc hex => Proof2.bar1Exits hpre hX hf hp hc hex)⟩

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (b : Base Q L mem0 X)
include hpre hX b

omit b in
/-- **`RoleReads`** is a consequence of the role byte protocol: the first load of a worker's role
byte returns an index below 3, a later one returns 3 (`roleReads_of_p2`, from the second tree's
role table). -/
theorem Base.roleReads : RoleReads L X :=
  roleReads_of_p2 hpre hX

omit b in
/-- **`NumWordRead`** (`numWordRead_of_p2`). -/
theorem Base.numWordRead : NumWordRead Q L X :=
  numWordRead_of_p2 hpre hX

/-- **`Safety.OdoneWait`** (`Interface.odoneWait`). -/
theorem Base.odoneWait : Safety.OdoneWait Q L X := Interface.odoneWait hpre hX b.facts

omit b in
/-- **`Safety.BoxInBounds`** (`Proof2.box_in_bounds`, on the second tree's role table). -/
theorem Base.boxInBounds : Safety.BoxInBounds X :=
  fun he => Proof2.box_in_bounds hpre hX he

end
end PTX.Kernels.InklingRelDecode.Proof.Assemble
