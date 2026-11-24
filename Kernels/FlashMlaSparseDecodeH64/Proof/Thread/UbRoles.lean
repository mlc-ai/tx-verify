-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbIndexData
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbDequantData
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbTmaGather
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbPrologueReturn
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbPrologue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaCoordinateRef

public section

/-! # Composition of the live event obligations of the role machines -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbRoles

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The live event-template obligations at the reached states of an execution reduce to the
softmax and MMA roles. -/
theorem templates (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    {g : Nat} (hg : g < L.threads) (hWg0 : (Wg0.code P L g).TmplOk)
    (hMma : (Wg1Mma.code P L g).TmplOk) {i : Nat} {d : Machine.ThreadD}
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d)) {t : TState} {ins : Instr}
    (ha : (Machine.code P L g).AtD d t) (hi : (Machine.code P L g).inv d)
    (hc : kernel.code[(Machine.code P L g).pc d]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  cases d
  case prologue s => exact UbPrologue.prologue_tmpl_ok hpre ha hc f
  case head => exact UbPrologue.head_tmpl_ok hpre ha hc f
  case wg0 d => exact hWg0 d t ins ha hi hc f
  case mma d => exact hMma d t ins ha hi hc f
  case tma d =>
    exact UbTma.tmpl_ok hpre hX.cluster.1 hg ha hi hc
      (fun _ hk j => TmaCoordinateRef.issue_words hpre hX hs hd hk j) f
  case index d => exact UbIndex.tmpl_ok hpre hg ha hi hc f
  case idle s => exact UbPrologue.idle_tmpl_ok hpre ha hc f
  case wg2 d => exact UbDequant.tmpl_ok hpre ha hi hc f
  case done =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    intro he
    cases he

/-- A returned event of the represented softmax role preserves the representation. -/
@[expose] def SoftmaxContinues (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g i d e}, X.get (g, i) = some e →
    Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) →
    ¬ Ends e → Machine.next P L g (.wg0 d) e ≠ none

/-- A returned event of the represented MMA role preserves the representation. -/
@[expose] def MmaContinues (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g i d e}, X.get (g, i) = some e →
    Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)) →
    ¬ Ends e → Machine.next P L g (.mma d) e ≠ none

/-- The continuation obligations reduce to the softmax and MMA roles. -/
theorem next_live (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hResources : ¬ Tmem.Pair.ResourceUnsafe L X)
    (hWg0 : SoftmaxContinues P L X) (hMma : MmaContinues P L X)
    {g i : Nat} {d : Machine.ThreadD} {e : Event} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hReturns : ¬ Ends e) : Machine.next P L g d e ≠ none := by
  cases d
  case prologue s => exact UbPrologue.prologue_next_live hpre hX hs ht hResources he hd hReturns
  case head => exact UbPrologue.head_next_live hpre hX hs he hd
  case wg0 d => exact hWg0 he hd hReturns
  case mma d => exact hMma he hd hReturns
  case tma d => exact UbTma.next_live hpre hX hs he hd hReturns
  case index d => exact UbIndex.next_live hpre hX hs he hd hReturns
  case idle s =>
    cases s
    case loadTopk => exact UbPrologue.idle_length_next_live hpre hX hs he hd (.inl rfl)
    case loadExtra => exact UbPrologue.idle_length_next_live hpre hX hs he hd (.inr rfl)
    case sync => exact UbPrologue.idle_sync_next_live hpre hX hs he hd
    case exit => simp [Machine.next, Thread.next]
  case wg2 d => exact UbDequant.next_live hpre hX hs he hd hReturns
  case done => exact (hReturns (UbPrologue.done_ends hX hs he hd)).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbRoles
