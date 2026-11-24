-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.MmaDrainTmemA
public import Lemmas.TensorStore.TensorStoreCompleteConsistentFiniteWrites

@[expose] public section

/-! # An MMA whose operand bytes have a visible write completes

`MmaDrainTmemA.lean` completes an MMA whose shared operand bytes have a write every other write of
the byte is ordered with. Here it suffices that some write of each byte is ordered before the read
(`OperandVisible`): the read takes a latest such write. -/

namespace PTX
open AsyncCopy MmaSources

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {sel : Nat → Bool}

/-- The shared operand bytes of the MMAs that have not read their operands have visible writes. -/
def OperandVisible (L : Launch) (X : Execution) : Prop :=
  TcMma.WarpIssuerUnique L X ∧ ∀ i d sp acc mask, X.MmaIssue i d sp acc mask →
    X.async.mmaOperands i = none → TcMma.Valid sp.descriptor ∧
    ∀ isB k loc, X.MmaFootprint i isB k loc →
      (∃ w a bs, X.MemWrites w a bs ∧ a.Covers loc ∧
        ByteCausality L X loc w (.async i (.mmaRead isB k))) ∧
      ∀ w a bs, X.MemWrites w a bs → a.Covers loc →
        ByteCausality L X loc w (.async i (.mmaRead isB k)) → ∃ v, wbyte a bs loc = some v

/-- An MMA without its operands, with its predecessors complete, completes. -/
theorem unstarted_mma_visible
    (hAsm : ∀ i values ra rb, X.le (X.finishMma i values ra rb) →
      ∀ a ∈ A, a.wf L mem0 (X.finishMma i values ra rb))
    (hX : Consistent L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandVisible L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d sp acc mask) (hnone : X.async.mmaOperands i = none)
    (hready : TcMma.CompletionReady L X i) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  classical
  obtain ⟨hwu, hall⟩ := hos
  obtain ⟨hv, hsrc⟩ := hall i d sp acc mask hi hnone
  have hlatest : ∀ isB k loc, X.MmaFootprint i isB k loc → ∃ src : ByteSource X, src.loc = loc ∧
      ∀ w a bs, X.MemWrites w a bs → a.Covers loc →
        ByteCausality L X loc w (.async i (.mmaRead isB k)) →
        ¬ ByteCausality L X loc src.ref w := by
    intro isB k loc hf
    obtain ⟨hex, hb⟩ := hsrc isB k loc hf
    obtain ⟨w, a, bs, v, hw, hc, -, -, hmax⟩ :=
      exists_storeProgress_latest_visible hX hsg hex hb
    exact ⟨⟨loc, w, a, bs, hw, hc⟩, rfl, hmax⟩
  choose src hloc horder using hlatest
  let pick : Bool → Nat → Option (ByteSource X) := fun isB k =>
    if h : ∃ loc, X.MmaFootprint i isB k loc then some (src isB k h.choose h.choose_spec)
    else none
  have hpick : ∀ isB k e, pick isB k = some e →
      ∃ h : ∃ loc, X.MmaFootprint i isB k loc, e = src isB k h.choose h.choose_spec := by
    intro isB k e he
    by_cases h : ∃ loc, X.MmaFootprint i isB k loc
    · simp only [pick, dite_eq_left h, Option.some.injEq] at he
      exact ⟨h, he.symm⟩
    · simp only [pick, dite_eq_right h, reduceCtorEq] at he
  have hp : PickFootprint X i pick := by
    refine ⟨fun isB k loc hf => ?_, fun isB k e he => ?_⟩
    · have h : ∃ loc, X.MmaFootprint i isB k loc := ⟨loc, hf⟩
      refine ⟨_, dite_eq_left h, ?_⟩
      rw [hloc]
      exact mmaFootprint_loc_unique h.choose_spec hf
    · obtain ⟨h, rfl⟩ := hpick isB k e he
      rw [hloc]
      exact h.choose_spec
  choose tm htm using MmaSources.aSourceByte_exists hX hsg hinj i
  have hn : X.async.mmaDone i = false := by
    cases hd : X.async.mmaDone i with
    | false => rfl
    | true =>
      have hs := hX.tma.2.1.2 i hd
      simp [Snapshot.mmaStarted, hnone] at hs
  have hle := le_finishMma_unstarted
    (values := pickOperands (TcMma.Operand.a.bytes sp.descriptor)
      (TcMma.Operand.b.bytes sp.descriptor) pick tm)
    (ra := pickSource pick false) (rb := pickSource pick true) hnone
  have hhid : Hidden L (X.finishMma i (pickOperands (TcMma.Operand.a.bytes sp.descriptor)
      (TcMma.Operand.b.bytes sp.descriptor) pick tm) (pickSource pick false)
      (pickSource pick true)) := by
    apply finishMma_hidden hX hle hn
    intro isB k loc hf w a bs hw hc hvis
    obtain ⟨e, he, hl⟩ := hp.1 isB k loc hf
    subst hl
    rw [pickSource_read he]
    obtain ⟨h, rfl⟩ := hpick isB k e he
    have h2 := horder isB k _ h.choose_spec w a bs hw
    rw [hloc] at hc hvis ⊢
    exact h2 hc hvis
  have hc := consistent_finishMma hX hi hn hready hv (pickOperands_lengths pick tm).1
    (pickOperands_lengths pick tm).2 (pickOperands_rf hX hle hp) (finishMma_noFuture hX hle hn)
    hhid
    (TcMma.readOk_finishMma_tmemA hX hsg hwu hap hi hn
      fun _ _ _ _ _ ha hs hw hpos => pickOperands_aRead hi hp htm ha hs hw hpos)
    (hAsm i _ _ _ hle)
  obtain ⟨pc, hget⟩ := hi
  obtain ⟨hg, hlen⟩ := issuer_thread hX hget
  exact ⟨_, hc, hle, finishMma_size hg hlen hn⟩

/-- **A maximal execution has completed every MMA** when the shared operand bytes of each MMA that
has not read its operands have visible writes. -/
theorem Maximal.mma_all_done_visible (hA : Assumption.WfStep sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandVisible L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d sp acc mask) : X.async.mmaDone i = true := by
  cases hn : X.async.mmaDone i with
  | true => rfl
  | false =>
    have hAsm : ∀ i values ra rb, X.le (X.finishMma i values ra rb) →
        ∀ a ∈ A, a.wf L mem0 (X.finishMma i values ra rb) :=
      fun _ _ _ _ hle => hA.quiet hmax.1 hle rfl (Execution.noNewRead_of_tr rfl)
    obtain ⟨m, ⟨d', s', a', m', hissue, hdone⟩, hmin⟩ := Proof.ProgressDescent.exists_minimal_of
      (p := fun m => ∃ d s acc mask, X.MmaIssue (i.1, m) d s acc mask ∧
        X.async.mmaDone (i.1, m) = false) id ⟨i.2, d, sp, acc, mask, hi, hn⟩
    have hready : TcMma.CompletionReady L X (i.1, m) := by
      intro p hp
      obtain ⟨hthread, hlt, -, ⟨pd, ps, pa, pmask, -, -, -, -, hpissue, -⟩, -⟩ :=
        TcMma.completionPrecedes_iff.mp hp
      cases hv : X.async.mmaDone p with
      | true => rfl
      | false =>
        have hid : p = (i.1, p.2) := Prod.ext hthread rfl
        have := hmin p.2 ⟨pd, ps, pa, pmask, hid ▸ hpissue, hid ▸ hv⟩
        simp only [id] at this hlt
        omega
    refine (hmax.not_grows ?_).elim
    cases ho : X.async.mmaOperands (i.1, m) with
    | none => exact unstarted_mma_visible hAsm hmax.1 hsg hos hap hinj hissue ho hready
    | some ops =>
      exact started_mma_inOrder hA hmax.1
        (by simp only [Snapshot.mmaStarted, ho, Option.isSome_some]) hdone hready

end

end PTX
