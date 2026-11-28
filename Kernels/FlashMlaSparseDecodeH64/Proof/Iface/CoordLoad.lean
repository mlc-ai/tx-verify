-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.DqValue

@[expose] public section

/-! # The TMA lane's coordinate loads and gathers: vocabulary

The pcs of the TMA lane's load of coordinate quadruple `q` (`ld.shared.v4.b32`, four events) and
of its gather `q` (`cp.async.bulk.tensor` gather4 with the column origin and the four row words),
the word a read event returns (`rdVal`), the four words of the last load of quadruple `q` before an
event (`coordWords`), and a word as the signed 32-bit coordinate a gather records (`wordInt`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

/-- The pc of the load of coordinate quadruple `q`. -/
def coordLoadPc (q : Nat) : Nat :=
  if q = 0 then 2250 else if q = 1 then 2254 else 2254 + 3 * q

/-- The pc of the gather of quadruple `q`. -/
def gatherPc (q : Nat) : Nat := if q = 15 then 2303 else 2259 + 3 * q

/-- The word a read event returns: its bytes rebuilt (the default when they do not rebuild). -/
def rdVal (e : Event) : Value :=
  match e.kind with
  | .rd _ bs => (rebuild 3 bs).toOption.getD (.pred false)
  | _ => .pred false

/-- The four words of the last load of quadruple `q` before event `k` of thread `g`. -/
def coordWords (X : Execution) (g k q : Nat) : List Value :=
  (lastAt X g k (coordLoadPc q) 4).map rdVal

/-- A 32-bit word as the signed coordinate a gather records. -/
def wordInt : Value → Int
  | .bits 32 z => (BitVec.ofNat 32 (truncBits 32 z).toNat).toInt
  | _ => 0

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
