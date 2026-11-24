-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.DrainInOrder
public import Lemmas.Tcgen05.MmaSourcesTmemA
public import Lemmas.Tcgen05.MmaFinishTmemA
public import Lemmas.Tcgen05.MmaFinishConsistent

@[expose] public section

/-! # A maximal execution has completed every MMA, with A possibly in Tensor Memory

A proof tool, for kernels whose MMAs may read operand A from Tensor Memory and whose assumptions
constrain executions only up to in-order commit delivery and new reads (`Assumption.WfStep`). An
MMA that has not completed is completed by a counted consistent extension: complete the earliest
unfinished MMA of its thread, whose same-thread predecessors have completed
(`TcMma.CompletionReady`).
Completing an MMA performs no commit arrive-on and adds no read, so the assumptions' constraints
hold of the extension (`Assumption.WfStep.quiet`).

* An MMA that has read its operands only computes (`started_mma_inOrder`).
* An MMA that has not read them reads each shared byte from a source write
  (`OperandByteSourcesT`, needed only while the MMA has not read its operands; `OperandSourcesT`
  is its base-model form), and each Tensor Memory A byte
  as the byte of its source value in the execution (`unstarted_mma_tmemA`). The source value is
  unique when each MMA's output layout is injective (`TcMma.LayoutInjective`). The new results
  create no new A source for any MMA when no MMA's A cell is written by an MMA with the same
  accumulator (`TcMma.ATmemApart`): an A source is then ordered before its reader by an observed
  completion, and its value does not depend on the completed MMA.

So a maximal execution has completed every MMA (`Maximal.mma_all_done_tmemA`). -/

namespace PTX

open AsyncCopy MmaSources

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {sel : Nat → Bool}

/-- The MMAs' shared operand bytes have sources: each warp issues its MMAs from one thread, each
MMA has a valid instruction descriptor, and each byte of its shared footprint (operand B, and
operand A when it is in shared memory) has a write that every other write of the byte precedes,
or that follows the MMA's read of it. -/
def OperandSourcesT (L : Launch) (X : Execution) : Prop :=
  TcMma.WarpIssuerUnique L X ∧ ∀ i d sp acc mask, X.MmaIssue i d sp acc mask →
    TcMma.Valid sp.descriptor ∧ ∀ isB k loc, X.MmaFootprint i isB k loc →
      ∃ src : ByteSource X, src.loc = loc ∧ ∀ w a bs, X.MemWrites w a bs → a.Covers loc →
        w = src.ref ∨ modelCausality L X loc w src.ref ∨ modelCausality L X loc
            (.async i (.mmaRead isB k)) w

/-- A source for each shared operand byte of an MMA that has not yet read its operands, allowing
observed commit edges before the source. -/
def OperandByteSourcesT (L : Launch) (X : Execution) : Prop :=
  TcMma.WarpIssuerUnique L X ∧ ∀ i d sp acc mask, X.MmaIssue i d sp acc mask →
    X.async.mmaOperands i = none → TcMma.Valid sp.descriptor ∧
    ∀ isB k loc, X.MmaFootprint i isB k loc →
      ∃ src : ByteSource X, src.loc = loc ∧ ∀ w a bs, X.MemWrites w a bs → a.Covers loc →
        w = src.ref ∨ ByteCausality L X loc w src.ref ∨ ByteCausality L X loc
            (.async i (.mmaRead isB k)) w

theorem OperandSourcesT.byteSources (h : OperandSourcesT L X) : OperandByteSourcesT L X := by
  refine ⟨h.1, fun i d sp acc mask hi _ => ⟨(h.2 i d sp acc mask hi).1, ?_⟩⟩
  intro isB k loc hf
  obtain ⟨src, hl, ho⟩ := (h.2 i d sp acc mask hi).2 isB k loc hf
  exact ⟨src, hl, fun w a bs hw hc => (ho w a bs hw hc).imp_right
    (Or.imp ByteCausality.direct ByteCausality.direct)⟩

/-- An MMA with its operands read and its predecessors complete completes. -/
theorem started_mma_inOrder (hA : Assumption.WfStep sel L K mem0 A)
    (hX : Consistent L K A mem0 X) {i : EvId}
    (hs : X.async.mmaStarted i = true) (hn : X.async.mmaDone i = false)
    (hready : TcMma.CompletionReady L X i) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨values, hv⟩ : ∃ values, X.async.mmaOperands i = some values := by
    cases hh : X.async.mmaOperands i with
    | none => simp [Snapshot.mmaStarted, hh] at hs
    | some values => exact ⟨values, rfl⟩
  obtain ⟨ev, hi⟩ : ∃ ev, X.get i = some ev := by
    rcases hX.tma.2.1.1 i hs with ⟨d, s, accum, mask, operands, ⟨pc, hi⟩, _⟩ |
      ⟨c, operands, ⟨pc, hi⟩, _⟩ | ⟨s, operands, ⟨pc, hi⟩, _⟩
    · exact ⟨_, hi⟩
    · exact ⟨_, hi⟩
    · exact ⟨_, hi⟩
  obtain ⟨hg, hlen⟩ := issuer_thread hX hi
  exact ⟨X.completeMma i,
    consistent_completeMma hX hs hn hready (hA.quiet hX (X.le_completeMma i) rfl
        (Execution.noNewRead_of_tr rfl)),
    X.le_completeMma i, completeMma_size hv hg hlen hn⟩

/-- An MMA without its operands, with its predecessors complete, completes: it reads each shared
byte from its source write and each Tensor Memory A byte as its source value. -/
theorem unstarted_mma_tmemA_of_byte_sources
    (hAsm : ∀ i values ra rb, X.le (X.finishMma i values ra rb) →
      ∀ a ∈ A, a.wf L mem0 (X.finishMma i values ra rb))
    (hX : Consistent L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandByteSourcesT L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d sp acc mask) (hnone : X.async.mmaOperands i = none)
    (hready : TcMma.CompletionReady L X i) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  classical
  obtain ⟨hwu, hall⟩ := hos
  obtain ⟨hv, hsrc⟩ := hall i d sp acc mask hi hnone
  choose src hloc horder using hsrc
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
  have hord : ∀ isB k e, pick isB k = some e → ∀ w a bs, X.MemWrites w a bs →
      a.Covers e.loc → w = e.ref ∨ ByteCausality L X e.loc w e.ref ∨
        ByteCausality L X e.loc (.async i (.mmaRead isB k)) w := by
    intro isB k e he w a bs hw hc
    obtain ⟨h, rfl⟩ := hpick isB k e he
    rw [hloc] at hc ⊢
    exact horder isB k _ _ w a bs hw hc
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
  have hc := consistent_finishMma hX hi hn hready hv (pickOperands_lengths pick tm).1
    (pickOperands_lengths pick tm).2 (pickOperands_rf hX hle hp) (finishMma_noFuture hX hle hn)
    (pickOperands_hidden_of_byte_order hX hsg hle hn hp hord)
    (TcMma.readOk_finishMma_tmemA hX hsg hwu hap hi hn
      fun _ _ _ _ _ ha hs hw hpos => pickOperands_aRead hi hp htm ha hs hw hpos)
    (hAsm i _ _ _ hle)
  obtain ⟨pc, hget⟩ := hi
  obtain ⟨hg, hlen⟩ := issuer_thread hX hget
  exact ⟨_, hc, hle, finishMma_size hg hlen hn⟩

/-- An unstarted MMA can use sources justified by base-model ordering. -/
theorem unstarted_mma_tmemA (hA : Assumption.WfStep sel L K mem0 A)
    (hX : Consistent L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandSourcesT L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d sp acc mask) (hnone : X.async.mmaOperands i = none)
    (hready : TcMma.CompletionReady L X i) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  unstarted_mma_tmemA_of_byte_sources (fun _ _ _ _ hle => hA.quiet hX hle rfl
    (Execution.noNewRead_of_tr rfl))
    hX hsg hos.byteSources hap hinj hi hnone hready

/-- **An unfinished MMA extends the execution.** Complete the earliest unfinished MMA of its
thread: its predecessors have completed. -/
theorem pending_mma_tmemA_of_byte_sources
    (hAsm : ∀ i values ra rb, X.le (X.finishMma i values ra rb) →
      ∀ a ∈ A, a.wf L mem0 (X.finishMma i values ra rb))
    (hComplete : ∀ i, X.async.mmaStarted i = true → X.async.mmaDone i = false →
      TcMma.CompletionReady L X i →
      ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L)
    (hX : Consistent L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandByteSourcesT L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d sp acc mask) (hn : X.async.mmaDone i = false) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
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
  cases ho : X.async.mmaOperands (i.1, m) with
  | none =>
    exact unstarted_mma_tmemA_of_byte_sources hAsm hX hsg hos hap hinj hissue ho hready
  | some ops =>
    exact hComplete (i.1, m) (by simp only [Snapshot.mmaStarted, ho, Option.isSome_some])
      hdone hready

/-- The base-model source condition is sufficient to complete an unfinished MMA. -/
theorem pending_mma_tmemA (hA : Assumption.WfStep sel L K mem0 A)
    (hX : Consistent L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandSourcesT L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d sp acc mask) (hn : X.async.mmaDone i = false) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  pending_mma_tmemA_of_byte_sources (fun _ _ _ _ hle => hA.quiet hX hle rfl
    (Execution.noNewRead_of_tr rfl))
    (fun _ => started_mma_inOrder hA hX) hX hsg hos.byteSources hap hinj hi hn

/-- **A maximal execution has completed every MMA**, with A in shared or Tensor Memory, when the
shared operand bytes have sources (`OperandSourcesT`), each MMA's output layout is injective, and
no MMA's Tensor Memory A cell is written by an MMA with the same accumulator
(`TcMma.ATmemApart`). -/
theorem Maximal.mma_all_done_tmemA (hA : Assumption.WfStep sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandSourcesT L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d sp acc mask) : X.async.mmaDone i = true := by
  cases hn : X.async.mmaDone i with
  | true => rfl
  | false => exact (hmax.not_grows (pending_mma_tmemA hA hmax.1 hsg hos hap hinj hi hn)).elim

/-- **A maximal execution has completed every MMA** when the shared operand bytes of each MMA
that has not read its operands have sources ordered by byte causality (`OperandByteSourcesT`). -/
theorem Maximal.mma_all_done_tmemA_of_byte_sources (hA : Assumption.WfStep sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandByteSourcesT L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d sp acc mask) : X.async.mmaDone i = true := by
  cases hn : X.async.mmaDone i with
  | true => rfl
  | false =>
    exact (hmax.not_grows (pending_mma_tmemA_of_byte_sources
      (fun _ _ _ _ hle => hA.quiet hmax.1 hle rfl (Execution.noNewRead_of_tr rfl))
      (fun _ => started_mma_inOrder hA hmax.1) hmax.1 hsg hos hap hinj hi hn)).elim

end

end PTX
