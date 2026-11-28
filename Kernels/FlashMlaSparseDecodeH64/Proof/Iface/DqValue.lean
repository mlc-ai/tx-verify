-- SPDX-License-Identifier: Apache-2.0
-- iface: DqValid producer=D status=proved domain=consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Spec

@[expose] public section

/-! # Warpgroup 2's loads: the words read and valid data

The vocabulary of the dequantizer's value export (`dq_store_value`, `Dequant/Export/Value.lean`):
the pcs of a lane's scale loads (`dqScalePc r`, one `ld.shared.v4.b32`: four events), raw loads
(`dqRawPc r s`, `ld.shared.b64`) and chunk stores (`dqStorePc r s`, `st.shared.b128`); the word the
bytes of a read rebuild to (`readWord`); a thread's last events at a pc before an event
(`lastAt`); the raw word and the sixteen scale bytes (element 0 lowest) such loads read
(`rawWordOf`, `scaleWordOf`); and valid data before an event (`DqValid`: every raw word read is
a 64-bit word of e4m3 bytes other than NaN (`0x7f`, `0xff`), every scale element a 32-bit word
of bytes below 255).

`DqValid` is the validity guard itself, a trace predicate defined on every execution (domain
`consistent`); the statements that assume it are `valid-rows`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

/-- The pc of row `r`'s scale load (`ld.shared.v4.b32`, four elements). -/
def dqScalePc (r : Nat) : Nat := 2695 + 225 * r
/-- The pc of row `r`'s raw load `s` (`ld.shared.b64`). -/
def dqRawPc (r s : Nat) : Nat :=
  if s = 0 then 2729 + 225 * r else if s = 1 then 2737 + 225 * r else 2760 + 225 * r + 24 * (s - 2)
/-- The pc of row `r`'s chunk store `s` (`st.shared.b128`). -/
def dqStorePc (r s : Nat) : Nat := 2752 + 225 * r + 24 * s - (if s = 7 then 1 else 0)

/-- The `n`-bit word a value is. -/
def bitsWord (n : Nat) : Value → Option Nat
  | .bits m x => if m = n ∧ x.toNat < 2 ^ n then some x.toNat else none
  | _ => none

/-- The `n`-bit word the bytes of a read event rebuild to. -/
def readWord (n : Nat) (e : Event) : Option Nat :=
  match e.kind with
  | .rd _ bs => (rebuild 3 bs).toOption.bind (bitsWord n)
  | _ => none

/-- The last `n` elements of a list. -/
def lastN {α : Type} (n : Nat) (l : List α) : List α := l.drop (l.length - n)

/-- The last `n` events of thread `g` at pc `p` before its event `k`, in trace order. -/
def lastAt (X : Execution) (g k p n : Nat) : List Event :=
  lastN n (((X.tr g).take k).filter fun e => decide (e.pc = p))

/-- The raw word one load read. -/
def rawWordOf : List Event → Nat
  | [e] => (readWord 64 e).getD 0
  | _ => 0

/-- The sixteen scale bytes four loads read, element 0 lowest. -/
def scaleWordOf : List Event → Nat
  | [e0, e1, e2, e3] =>
    (readWord 32 e0).getD 0 + 256 ^ 4 * ((readWord 32 e1).getD 0 +
      256 ^ 4 * ((readWord 32 e2).getD 0 + 256 ^ 4 * (readWord 32 e3).getD 0))
  | _ => 0

/-- **Valid data** before event `k` of thread `g`: each raw load read a 64-bit word of e4m3 bytes
other than NaN, each scale load a 32-bit word of bytes below 255. -/
def DqValid (X : Execution) (g k : Nat) : Prop :=
  ∀ j < k, ∀ e, X.get (g, j) = some e →
    (∀ r s, r < 4 → s < 8 → e.pc = dqRawPc r s →
      ∃ x, readWord 64 e = some x ∧ ∀ i < 8, x / 256 ^ i % 256 ≠ 127 ∧ x / 256 ^ i % 256 ≠ 255) ∧
    (∀ r, r < 4 → e.pc = dqScalePc r →
      ∃ w, readWord 32 e = some w ∧ ∀ i < 4, w / 256 ^ i % 256 < 255)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
