-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyDynamic.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
public import Lemmas.Kernel.Goals

@[expose] public section

/-! # The interface between the thread layer and the conclusions

The layers above the threads see a thread only through `ThreadFacts`: its machine follows it
(`tracked`), and what its events are. Thread `g < N` reads `A[g]` (`accA`) as its first event and
writes the value the read's bytes rebuild to into `B[g]` (`accB`) as its second; its undefined
behaviour follows a read whose bytes are not one 4-byte value; it exits only after the write. The
thread layer proves `ThreadFacts` (`Thread/Facts.lean`). -/

namespace PTX.Kernels.CopyDynamic.Proof
open PTX

/-- The footprints of thread `g`'s element of `A` and of `B`. -/
def accA (A g : Nat) : Acc := { loc := ⟨.global, 0, A + 4 * g⟩, size := 4 }
def accB (B g : Nat) : Acc := { loc := ⟨.global, 0, B + 4 * g⟩, size := 4 }

/-- The read of `A[g]` returning `bs`, and the write of `v` to `B[g]`. -/
def rdE (A g : Nat) (bs : List (Option Byte)) : Event := ⟨Flow.load_0, .rd (accA A g) bs⟩
def wrE (B g : Nat) (v : Value) : Event := ⟨Flow.store_0, .wr (accB B g) v.toBytes⟩

/-- Per-thread facts of an execution. -/
structure ThreadFacts (L : Launch) (A B N : Nat) (X : Execution) : Prop where
  /-- Every thread is followed by its machine at each of its events. -/
  tracked : Frame.Tracked (code L A B N) X
  /-- Every event is a read, a write, an exit or undefined behaviour. -/
  kinds : ∀ {i : EvId} {e : Event}, X.get i = some e →
    (∃ a bs, e.kind = .rd a bs) ∨ (∃ a bs, e.kind = .wr a bs) ∨ e.kind = .exit ∨
      ∃ f, e.kind = .ub f
  /-- A read is thread `g`'s first event, the read of `A[g]`, for `g < N`. -/
  reads : ∀ {g k pc : Nat} {a : Acc} {bs : List (Option Byte)},
    X.get (g, k) = some ⟨pc, .rd a bs⟩ → k = 0 ∧ g < N ∧ a = accA A g
  /-- A write is thread `g`'s second event, for `g < N`: the write to `B[g]` of the value of
  its source, which is the value the bytes of its read rebuild to unless the source is wider than
  the access (`storeValue`). -/
  writes : ∀ {g k pc : Nat} {a : Acc} {bs : List Byte}, X.get (g, k) = some ⟨pc, .wr a bs⟩ →
    k = 1 ∧ g < N ∧ a = accB B g ∧
      ∃ rb v w, X.get (g, 0) = some (rdE A g rb) ∧ rebuild 3 rb = .ok v ∧
        storeValue 32 v = .ok w ∧ bs = w.toBytes
  /-- Undefined behaviour follows a read whose bytes are not one 4-byte value. -/
  ub : ∀ {g k pc : Nat} {f : Fault}, X.get (g, k) = some ⟨pc, .ub f⟩ →
    g < N ∧ ∃ rb, X.get (g, 0) = some (rdE A g rb) ∧ ∀ v, rebuild 3 rb = .ok v → v.bytes ≠ 4
  /-- A thread `g < N` exits after its write. -/
  exit_write : ∀ {g k pc : Nat}, X.get (g, k) = some ⟨pc, .exit⟩ → g < N →
    ∃ pc' a bs, X.get (g, 1) = some ⟨pc', .wr a bs⟩

end PTX.Kernels.CopyDynamic.Proof
