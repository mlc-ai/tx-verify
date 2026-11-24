-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.MmaOperandObservations
public import Lemmas.Async.AsyncMBarrier
import Lemmas.Order.Order

@[expose] public section

/-! # An observed MMA has performed its operand reads

A proof tool. A wait that observes an MMA's completion (`AsyncObserved … .mmaDone`) observed the
notification of a commit tracking it, which requires the MMA's completion (`CommitOk`); a
completed MMA has started, with its operand bytes recorded (`TcEffectsOk`), so every byte of
its operand footprint has a recorded read (`TcEffectsOk.mma_read_exists`): the read stage is
present (`observed_mmaRead`). -/

namespace PTX

noncomputable section

/-- An in-scope acquire of an MMA's completion ends its shared source read before a
covering plain store in the acquiring thread. -/
theorem completed_mma_source_before_store {L : Launch} {X : Execution}
    {i w f : EvId} {isB : Bool} {index : Nat} {l : Loc}
    {d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    {a : Acc} {bs : List Byte}
    (hi : X.MmaIssue i d s acc mask) (hr : X.MmaFootprint i isB index l)
    (hFinish : AsyncFinished L X i (.mmaRead isB index) w)
    (hSame : w.1 = f.1) (hLt : w.2 < f.2) (hBefore : baseCausality L X w f)
    (hShared : l.space = .shared) (hw : X.Writes f a bs) (hc : a.Covers l) :
    ByteCausality L X l (.async i (.mmaRead isB index)) (.thread f) := by
  have hFoot : AsyncCovers X i (.mmaRead isB index) l :=
    ⟨{loc := l, size := 1}, false, ⟨rfl, rfl, hr⟩,
      Acc.covers_at (k := 0) (show 0 < 1 by decide)⟩
  exact .direct ⟨hFoot, w, hFinish, .inr
    ⟨hShared, .inr ⟨hSame, hLt, d, s, acc, mask, hi⟩, hBefore, a, bs, hw, hc⟩⟩

/-- **An MMA observed complete has read each byte of its operands.** -/
theorem observed_mmaRead {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) {i w : EvId} {acq : Bool} {ws : MbarScope}
    {d : Nat} {s : TcMma.OperandSpec} {accum : Bool} {mask : List Nat} {isB : Bool}
    {index : Nat} {l : Loc} (hi : X.MmaIssue i d s accum mask)
    (hl : s.byteLoc (if isB then .b else .a) index = some l)
    (h : AsyncCopy.AsyncObserved X i .mmaDone w acq ws) :
    X.AsyncPresent i (.mmaRead isB index) := by
  obtain ⟨c, _, rank, _, htrack, _, _, hn, _⟩ := h.mma
  have hd := (hX.tcCommit c rank hn).2 i htrack
  have hst := hX.tma.2.1.2 i hd
  obtain ⟨operands, ho⟩ := Option.isSome_iff_exists.mp hst
  obtain ⟨b, hr, -⟩ := hX.tma.2.1.mma_read_exists hi ho hl
  exact ⟨l, b, hr⟩

/-- A write already ordered before the copy's recorded shared-byte read precedes the ordinary
overwrite after the acquire that observed completion of that read. -/
theorem ByteCausality.before_copy_overwrite {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X)
    {src : AsyncCopy.Ref} {cp wait dst : EvId} {c : TcCopy.Spec} {l : Loc} {index : Nat}
    {a out : Acc} {vs bytes : List Byte} (hs : l.space = .shared)
    (hw : X.MemWrites src a vs) (hc : a.Covers l)
    (hi : X.CpIssue cp c) (hr : X.MmaFootprint cp false index l)
    (hp : ByteCausality L X l src (.async cp (.mmaRead false index)))
    (hf : AsyncFinished L X cp (.mmaRead false index) wait) (hn : po X wait dst)
    (ho : X.Writes dst out bytes) (hd : out.Covers l) :
    ByteCausality L X l src (.thread dst) := by
  rcases hf with ⟨kind, hvis, _⟩ | ⟨scope, hobs, hscope⟩
  · cases kind with
    | cpAsync => contradiction
    | bulk mode => cases mode <;> contradiction
  · have hdone : X.AsyncPresent cp .mmaDone := by
      obtain ⟨commit, _, rank, _, htrack, _, _, hnotify, _⟩ := hobs.mma
      exact (hX.tcCommit commit rank hnotify).2 cp htrack
    exact .commitOperand hs ⟨a, hw.intent, hc⟩
      (.inr ⟨rfl, rfl, ⟨c, hi⟩, out, bytes, ho, hd⟩)
      (hX.tma.2.1.cp_read_of_complete hi hdone hr) hp ⟨scope, hobs, hscope⟩ hn
      ⟨out, .inl ⟨true, (show X.MemWrites (.thread dst) out bytes from .inl ho).intent⟩, hd⟩

end

end PTX
