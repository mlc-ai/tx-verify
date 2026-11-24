-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Premises

@[expose] public section

/-!
# Events, writers and the dependency step

`Present X e`: `e` is an event of the execution; `refEvent r`: the event that issued the write
`r`. `Dep X a b` is one step of program order and reads-from: `a` is before `b` in its thread, or
`b` reads a byte from a write issued by `a`. The value facts about a shared word use it to name the
writer of a byte a read returns (`FootRoleRead`); no induction runs along it: the machines are
followed by an induction along each thread's events (`Interface.weakTracked_of`), with the launch
bytes from the read-only input assumption.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The event that issued a thread or asynchronous write. -/
def refEvent : AsyncCopy.Ref → EvId
  | .thread e => e
  | .async i _ => i

/-- The event `e` is an event of the execution. -/
def Present (X : Execution) (e : EvId) : Prop := ∃ ev, X.get e = some ev

/-- **One dependency step**: `a` is earlier than `b` in the trace of one thread, or `b` is an event
that reads a byte from a write that `a` issued. -/
def Dep (X : Execution) (a b : EvId) : Prop :=
  Present X a ∧ Present X b ∧
    ((a.1 = b.1 ∧ a.2 < b.2) ∨
      ∃ (r : AsyncCopy.Ref) (acc : Acc) (bs : List (Option Byte)) (i : Nat),
        X.MemReads (.thread b) acc bs ∧ X.rf (.thread b) i = some r ∧ refEvent r = a)

theorem Dep.left {a b : EvId} (h : Dep X a b) : Present X a := h.1

theorem Dep.right {a b : EvId} (h : Dep X a b) : Present X b := h.2.1

theorem Dep.po {a b : EvId} (ha : Present X a) (hb : Present X b) (h1 : a.1 = b.1)
    (h2 : a.2 < b.2) : Dep X a b := ⟨ha, hb, Or.inl ⟨h1, h2⟩⟩

theorem Dep.rf {b : EvId} {r : AsyncCopy.Ref} {acc : Acc} {bs : List (Option Byte)} {i : Nat}
    (hb : Present X b) (hr : Present X (refEvent r)) (h1 : X.MemReads (.thread b) acc bs)
    (h2 : X.rf (.thread b) i = some r) : Dep X (refEvent r) b :=
  ⟨hr, hb, Or.inr ⟨r, acc, bs, i, h1, h2, rfl⟩⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
