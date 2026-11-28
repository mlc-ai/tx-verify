-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.Phase

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow PTX.Sched PTX.MbarRing

def arrivalLane (L : Launch) (c : Nat) (b : Fin 2) :=
  c * L.block + if b = 0 then 0 else 192

noncomputable def copyLane (L : Launch) (X : Execution) (c : Nat) (b : Fin 3) :=
  leader L X c (if b = 2 then 6 else b.val)

/-- Number due from each producer for the first n uses. The two preloading
warps supply four copies each, the elected loader supplies all eight on reuse. -/
def dueArr (δ n : Nat) (b : Fin 2) := if b = 0 then min δ n else n - δ
def dueCp (δ n : Nat) (b : Fin 3) := if b = 2 then 8*(n-δ) else 4 * min δ n

/-- W, P: a producer owes its due events before exit and by its waiter's scheduled time. -/
def Due (Q : Params) (L : Launch) (X : Execution) (g y : Nat) (p : Event → Bool) (n : Nat) :=
  (∀ k pc, X.get (y,k) = some ⟨pc,.exit⟩ → n ≤ (X.tr y).countP p) ∧
    (threadTime (schedule Q L) X g ≤ threadTime (schedule Q L) X y → n ≤ (X.tr y).countP p)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
