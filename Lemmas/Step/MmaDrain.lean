-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Drain
public import Lemmas.Tcgen05.MmaSources
public import Lemmas.Tcgen05.MmaFinishConsistent
public import Lemmas.Tcgen05.TcReadFinishMma

@[expose] public section

/-! # A maximal execution has completed every MMA whose operands have sources

A proof tool. An MMA that has not completed is completed by a counted consistent extension:
complete the earliest unfinished MMA of its thread, whose same-thread predecessors have
completed (`TcMma.CompletionReady`). If it has read its operands, the completion only computes
(`consistent_completeMma`); otherwise its operand bytes are read from source writes
(`OperandSources`: RF from the writes, coherence from their order, the Tensor Memory reads from
shared operands issued by one thread per warp). So a maximal execution has completed every MMA
(`Maximal.mma_all_done`). -/

namespace PTX

open AsyncCopy MmaSources

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The MMAs' operands have sources: each warp issues its MMAs from one thread, and each MMA has
an `nA`-byte operand A and an `nB`-byte operand B in shared memory, each byte with a write that
every other write of the byte precedes, or that follows the MMA's read of it. -/
def OperandSources (L : Launch) (X : Execution) (nA nB : Nat) : Prop :=
  TcMma.WarpIssuerUnique L X ∧ ∀ i d sp acc mask, X.MmaIssue i d sp acc mask →
    TcMma.Valid sp.descriptor ∧ TcMma.Operand.a.bytes sp.descriptor = nA ∧
    TcMma.Operand.b.bytes sp.descriptor = nB ∧ sp.aTmem = none ∧
    (∀ isB k loc, X.MmaFootprint i isB k loc → k < if isB then nB else nA) ∧
    ∀ isB (k : Fin (if isB then nB else nA)), ∃ src : ByteSource X,
      X.MmaFootprint i isB k.val src.loc ∧
      ∀ w a bs, X.MemWrites w a bs → a.Covers src.loc →
        w = src.ref ∨ modelCausality L X src.loc w src.ref ∨
          modelCausality L X src.loc (.async i (.mmaRead isB k.val)) w

/-- An MMA with its operands read and its predecessors complete completes. -/
theorem started_mma (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X) {i : EvId}
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
  exact ⟨X.completeMma i, consistent_completeMma hX hs hn hready (fun a ha => hA a ha _),
    X.le_completeMma i, completeMma_size hv hg hlen hn⟩

/-- An MMA without its operands, with its predecessors complete, completes: it reads each operand
byte from its source write. -/
theorem unstarted_mma {nA nB : Nat} (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X)
    (hsg : SyncGuarded L K X)
    (hos : OperandSources L X nA nB) {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hi : X.MmaIssue i d sp acc mask) (hnone : X.async.mmaOperands i = none)
    (hready : TcMma.CompletionReady L X i) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨hwu, hall⟩ := hos
  obtain ⟨hv, ha, hb, -, hbound, hsrc⟩ := hall i d sp acc mask hi
  choose source hfoot horder using hsrc
  have hn : X.async.mmaDone i = false := by
    cases hd : X.async.mmaDone i with
    | false => rfl
    | true =>
      have hs := hX.tma.2.1.2 i hd
      simp [Snapshot.mmaStarted, hnone] at hs
  have hle := le_finishMma_unstarted (values := newOperands source) (ra := newSource source false)
    (rb := newSource source true) hnone
  have hc := consistent_finishMma hX hi hn hready hv
    ((newOperands_lengths source).1.trans ha.symm) ((newOperands_lengths source).2.trans hb.symm)
    (newOperands_rf hX source hle hfoot) (finishMma_noFuture hX hle hn)
    (newOperands_hidden hX hsg source hle hn hfoot hbound horder)
    (TcMma.readOk_finishMma_shared hX hsg hwu (fun j d s acc mask hj =>
      (hall j d s acc mask hj).2.2.2.1)
      hi hn)
    (fun a ha => hA a ha _)
  obtain ⟨pc, hget⟩ := hi
  obtain ⟨hg, hlen⟩ := issuer_thread hX hget
  exact ⟨_, hc, hle, finishMma_size hg hlen hn⟩

/-- **An unfinished MMA extends the execution.** Complete the earliest unfinished MMA of its
thread: its predecessors have completed. -/
theorem pending_mma {nA nB : Nat} (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X)
    (hsg : SyncGuarded L K X)
    (hos : OperandSources L X nA nB) {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hi : X.MmaIssue i d sp acc mask) (hn : X.async.mmaDone i = false) :
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
  | none => exact unstarted_mma hA hX hsg hos hissue ho hready
  | some ops =>
    exact started_mma hA hX (by simp only [Snapshot.mmaStarted, ho, Option.isSome_some]) hdone
      hready

/-- **A maximal execution has completed its MMAs**, when their operands have sources. -/
theorem Maximal.mma_all_done {nA nB : Nat} (hA : Assumption.WfFree L mem0 A)
    (hmax : Maximal L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandSources L X nA nB)
    {i : EvId} {d : Nat}
    {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat} (hi : X.MmaIssue i d sp acc mask) :
    X.async.mmaDone i = true := by
  cases hn : X.async.mmaDone i with
  | true => rfl
  | false => exact (hmax.not_grows (pending_mma hA hmax.1 hsg hos hi hn)).elim

end

end PTX
