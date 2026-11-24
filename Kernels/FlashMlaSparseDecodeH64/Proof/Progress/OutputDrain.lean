-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Closing
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputReadOrder
public import Lemmas.Step.StoreDone
import Kernels.FlashMlaSparseDecodeH64.Proof.Geometry.Maps
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.OutputStoreFacts
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressGuard
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites

public section

/-! # Progress of actual output store effects -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem spec_valid (hpre : Pre P L mem0) (g : Nat) (j : Fin 4) :
    TensorStore.Valid (g / L.block) (outputSpec P L g j) := by
  refine ⟨Geometry.mapO_valid_of_pre hpre, ?_, ?_, rfl, rfl, ?_⟩
  · intro axis
    fin_cases axis <;> simp [outputSpec, outputOrigin]
  · intro ys hy
    cases hy
  · have ha : L.sharedBase % 1024 = 0 := hpre.sharedBase ▸ hpre.sharedAlignment
    change (L.sharedBase + tmaSrc j.val (warpOf L g)) % 128 = 0
    unfold tmaSrc groupOff stageBase stageTileBytes
    omega

private theorem output_store_input (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    {i : EvId} {address : Nat} {sp : TensorStore.Spec} (hi : X.TensorStoreIssue i address sp) :
    TensorStore.Valid (i.1 / L.block) sp ∧
      PTX.Step.StoreDone.VisibleReadSources L X i sp ∧ sp.reduce = none := by
  obtain ⟨g, i⟩ := i
  have hog := (hs g (Frame.lt_of_get hX hi.choose_spec)).machine
  obtain ⟨d, j, hd, hj⟩ := GlobalWrites.outputTile_site
    hs hX ht hi
  obtain ⟨_, rfl⟩ := Wg0OutputTrace.tileSpec hpre hX hog hi hd hj
  have hw := Wg0OutputControl.outputWarp hX hog hi.choose_spec hd hj
  refine ⟨spec_valid hpre g j, ?_, rfl⟩
  intro slot dest _
  obtain ⟨s, rfl⟩ := (Result.tensorOutputSlot_bijective P L g j).2 slot
  obtain ⟨w, b, _, a, _, _, _, _, _, _, _, hwr, _, hcov, hbefore⟩ :=
    Protocol.OutputReadOrder.of_prefix_issue hpre hX (fun g hg => (hs g hg).machine) ht hi hd hj s
  rw [Result.outputSlot_shared hpre j s hw]
  refine ⟨⟨.thread (w, b), a, _, .inl hwr, hcov, .direct hbefore⟩, ?_⟩
  intro w a bytes hwrite hcover _
  exact OutputStoreFacts.covered_byte hX hwrite hcover rfl

variable (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hmax hs ht

/-- Every issued output store has finished both its shared reads and global writes in
a safe maximal execution whose thread states are tracked. -/
theorem output_full_done (hsafe : ¬ Unsafe L kernel Assumptions.all mem0 X) {i : EvId}
    {address : Nat} {sp : TensorStore.Spec} (hi : X.TensorStoreIssue i address sp) :
    ∃ o, X.tensorStores i = some o ∧ o.effects.fullDone = true := by
  classical
  by_contra hnot
  obtain ⟨hvalid, hsource, hstore⟩ := output_store_input hpre hmax.1 hs ht hi
  exact hmax.not_grows (PTX.Step.StoreDone.pending_issue_visible_of_effects hmax.1
    (fun {_ _} hc hle htr hin hnotify => Interface.all_wf_effects hc hle htr hin hnotify)
    ⟨address, hi⟩ hvalid hnot hsource
    (sync_guarded hmax.1 hsafe) hstore)

/-- Every selected output issue has finished its shared reads, as required to return. -/
theorem output_reads_drained (hsafe : ¬ Unsafe L kernel Assumptions.all mem0 X) {i : EvId}
    (hi : TensorStore.Selected Assumptions.storeDrain.storeReadsBeforeExit X i) :
    X.AsyncPresent i .readsDone := by
  obtain ⟨tag, address, sp, he, _⟩ := hi
  obtain ⟨o, ho, hd⟩ := output_full_done hpre hmax hs ht hsafe
    (i := i) (address := address) (sp := sp) ⟨tag, he⟩
  exact ⟨o, ho, ((hmax.1.store i o ho).2.2.complete hd).1⟩

/-- A released thread cannot remain at its final return once its output stores have drained. -/
theorem return_not_pending_of_output (hsafe : ¬ Unsafe L kernel Assumptions.all mem0 X) {g : Nat}
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    {d : Machine.ThreadD}
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    (hsite : ClosingProgress.ReturnSite d) : False :=
  return_not_pending hmax hs hub hp hrel
    (fun _ _ hi => output_reads_drained hpre hmax hs ht hsafe hi) hd hsite

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
