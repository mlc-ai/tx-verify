-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.OutputGeometry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.NotClc
public import Lemmas.Kernel.StoreDrain

@[expose] public section

/-! # Tensor-store issues and footprints of the output epilogue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0OutputTrace

open PTX PTX.Flow Wg0

set_option maxRecDepth 100000 in
private theorem output_sites :
    OpPcsFast kernel.code tensorStoreOp tensorStores = true := by
  decide +kernel

/-- Every actual tensor-store issue is covered by the source-read drain assumption. -/
theorem selected {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {i : EvId} {a : Nat} {sp : TensorStore.Spec}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.TensorStoreIssue i a sp) :
    TensorStore.Selected Assumptions.storeDrain.storeReadsBeforeExit X i := by
  obtain ⟨site, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  rcases ((hs i.1 hg).produces (hX.thr i.1 hg)).fired he with
    ⟨state, o, hstate, hfired⟩ | ⟨_, _, _, hbad⟩
  · cases state with
    | none => exact ((ht i.1 i.2 hg) hstate).elim
    | some d =>
      obtain ⟨t, ⟨hat, _⟩, hf⟩ := hfired
      change (Machine.code P L i.1).AtD d t at hat
      change Fires t.pc (match kernel.code[(Machine.code P L i.1).pc d]? with
        | some ins => eventTmpl Assumptions.all L i.1 t ins.op
        | none => .ub .pcOutOfRange) ⟨site, .tensorStore a sp⟩ o at hf
      cases hc : kernel.code[(Machine.code P L i.1).pc d]? with
      | none =>
        rw [hc] at hf
        exact (by cases hf.1)
      | some ins =>
        rw [hc] at hf
        have hp : site = t.pc := fires_pc hf
        rw [hat.1] at hp
        have hm := OpPcsFast.mem output_sites hc (fires_tensorStore_op hf rfl)
        rw [← hp] at hm
        exact ⟨site, a, sp, he, List.contains_iff_mem.mpr hm⟩
  · cases hbad

/-- When a tensor-store issuer has exited, the lifetime of its shared source reads is proved
through the kernel's selected-read drain assumption. -/
theorem readsFinished {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {i finish : EvId} {a : Nat} {sp : TensorStore.Spec} {cta : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.TensorStoreIssue i a sp) (hbefore : TraceBefore X i finish)
    (hexit : OwnerExit L X cta finish) :
    SharedFinished L kernel Assumptions.all X (.async i .readsDone) cta := by
  have ha : Assumptions.storeDrain ∈ Assumptions.all := by simp [Assumptions.all]
  exact SharedFinished.of_storeReadsDrained ha hbefore (selected hX hs ht hi) hexit
    (hX.asm Assumptions.storeDrain ha)

private theorem slotAt_output {P : Params} {L : Launch} {g : Nat} (j : Fin 4)
    (s : Result.OutputSlot) :
    TensorTransfer.slotAt (outputSpec P L g j).descriptor s.1.val s.2.1.val s.2.2.val =
      some (Result.tensorOutputSlot P L g j s) := by
  unfold TensorTransfer.slotAt
  obtain ⟨hx, hy, hb⟩ := Result.outputShape P L g j
  rw [dite_eq_left (show s.1.val < _ by rw [hx]; exact s.1.isLt),
    dite_eq_left (show s.2.1.val < _ by rw [hy]; exact s.2.1.isLt),
    dite_eq_left (show s.2.2.val < _ by rw [hb]; exact s.2.2.isLt)]
  rfl

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat} {a : Nat}
    {sp : TensorStore.Spec} {j : Fin 4} {d : D} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (hi : X.TensorStoreIssue (g, k) a sp)
    (hd : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d)))
include hpre hX hs hi hd

/-- An actual output issue uses the designated tensor map and the tile's descriptor. -/
theorem tileSpec (hj : d.site = .tmaStore j) :
    a = P.param1Base + 512 ∧ sp = outputSpec P L g j := by
  obtain ⟨site, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  have hq : qOf L g < P.s_q := Wg1Mma.queryOf_lt hpre hg
  have hb : eOf L g < P.b := Wg1Mma.batchOf_lt hpre hg
  obtain ⟨o, hf⟩ := (hs.produces (hX.thr g hg)).fired_at he hd
  have hf0 : (Wg0.code P L g).toMachine.Fired (some d) ⟨site, .tensorStore a sp⟩ o := by
    obtain ⟨t, ⟨hat, hinv⟩, hf⟩ := hf
    refine ⟨t, ⟨⟨hat.1, hat.2.1, ?_, hat.2.2.2⟩, hinv⟩, hf⟩
    have hacc := hat.2.2.1
    change t.acc = Machine.ThreadD.acc P L g (.wg0 d) at hacc
    simpa [Machine.ThreadD.acc, Wg0.code, siteAcc, hj] using hacc
  have ho : o.isSome := by
    obtain ⟨t, _, hf⟩ := hf0
    change Fires t.pc ((Wg0.code P L g).tmpl (some d) t) ⟨site, .tensorStore a sp⟩ o at hf
    generalize (Wg0.code P L g).tmpl (some d) t = tm at hf
    cases tm <;>
      simp only [Fires] at hf <;> aesop
  obtain ⟨u, rfl⟩ := Option.isSome_iff_exists.mp ho
  have hk := fired_outputTile hpre hj hq hb hf0
  exact Kind.tensorStore.inj hk

/-- A descriptor slot at an actual output issue reads the corresponding staging byte and writes
the corresponding logical output byte. -/
theorem tileFootprint (hj : d.site = .tmaStore j) (hw : warpOf L g < 2) (s : Result.OutputSlot) :
    let column := tmaX j.val (warpOf L g) + s.1.val
    a = P.param1Base + 512 ∧
      TensorStore.readLoc sp s.1.val s.2.1.val s.2.2.val =
        some (shLoc L g (stageOff s.2.1.val column + s.2.2.val)) ∧
      TensorStore.writeLoc sp s.1.val s.2.1.val s.2.2.val =
        some ((oLoc P (eOf L g) (qOf L g) s.2.1.val column).at s.2.2.val) := by
  obtain ⟨rfl, rfl⟩ := tileSpec hpre hX hs hi hd hj
  refine ⟨rfl, ?_, ?_⟩
  · simpa only [TensorStore.readLoc, slotAt_output, Option.map_some] using
      congrArg some (Result.outputSlot_shared hpre j s hw)
  · have hg : g < L.threads := by
      obtain ⟨_, he⟩ := hi
      exact Frame.lt_of_get hX he
    have hq : qOf L g < P.s_q := Wg1Mma.queryOf_lt hpre hg
    have hb : eOf L g < P.b := Wg1Mma.batchOf_lt hpre hg
    simpa only [TensorStore.writeLoc, slotAt_output, Option.bind_some] using
      Result.outputSlot_destination P L g j s hw hq hb

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0OutputTrace
