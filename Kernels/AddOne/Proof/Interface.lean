-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.AddOne.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
public import Lemmas.Kernel.Goals

@[expose] public section

/-! # The interface between the thread layer and the conclusions

The layers above the threads see a thread only through `ThreadFacts`: its machine follows it
(`tracked`), and what its events are. Thread `g` reads `A[g]` (`accA`) as its first event and
writes the sum (`incr`) of the value the read's bytes rebuild to back into `A[g]` as its second;
its undefined behaviour follows a read whose bytes give no 4-byte sum; it exits only after the
write. The thread layer proves `ThreadFacts` (`Thread/Facts.lean`). -/

namespace PTX.Kernels.AddOne.Proof
open PTX

/-- The footprint of thread `g`'s element of `A`. -/
def accA (A g : Nat) : Acc := { loc := ⟨.global, 0, A + 4 * g⟩, size := 4 }

/-- The read of `A[g]` returning `bs`, and the write of `w` to `A[g]`. -/
def rdE (A g : Nat) (bs : List (Option Byte)) : Event := ⟨Flow.load_0, .rd (accA A g) bs⟩
def wrE (A g : Nat) (w : Value) : Event := ⟨Flow.store_0, .wr (accA A g) w.toBytes⟩

/-- Per-thread facts of an execution. -/
structure ThreadFacts (L : Launch) (A : Nat) (X : Execution) : Prop where
  /-- Every thread is followed by its machine at each of its events. -/
  tracked : Frame.Tracked (code L A) X
  /-- Every event is a read, a write, an exit or undefined behaviour. -/
  kinds : ∀ {i : EvId} {e : Event}, X.get i = some e →
    (∃ a bs, e.kind = .rd a bs) ∨ (∃ a bs, e.kind = .wr a bs) ∨ e.kind = .exit ∨
      ∃ f, e.kind = .ub f
  /-- A read is thread `g`'s first event, the read of `A[g]`. -/
  reads : ∀ {g k pc : Nat} {a : Acc} {bs : List (Option Byte)},
    X.get (g, k) = some ⟨pc, .rd a bs⟩ → k = 0 ∧ a = accA A g
  /-- A write is thread `g`'s second event: the write to `A[g]` of the sum of the value the
  bytes of its read rebuild to. The store writes the value of its source, which is that sum
  unless the source is wider than the access (`storeValue`). -/
  writes : ∀ {g k pc : Nat} {a : Acc} {bs : List Byte}, X.get (g, k) = some ⟨pc, .wr a bs⟩ →
    k = 1 ∧ a = accA A g ∧
      ∃ rb v w w', X.get (g, 0) = some (rdE A g rb) ∧ rebuild 3 rb = .ok v ∧
        incr L g v = .ok w ∧ storeValue 32 w = .ok w' ∧ bs = w'.toBytes
  /-- Undefined behaviour follows a read whose bytes give no 4-byte sum. -/
  ub : ∀ {g k pc : Nat} {f : Fault}, X.get (g, k) = some ⟨pc, .ub f⟩ →
    ∃ rb, X.get (g, 0) = some (rdE A g rb) ∧
      ∀ v w, rebuild 3 rb = .ok v → incr L g v = .ok w → w.bytes ≠ 4
  /-- A thread exits after its write. -/
  exit_write : ∀ {g k pc : Nat}, X.get (g, k) = some ⟨pc, .exit⟩ →
    ∃ pc' a bs, X.get (g, 1) = some ⟨pc', .wr a bs⟩

end PTX.Kernels.AddOne.Proof
