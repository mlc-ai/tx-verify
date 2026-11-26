-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Arith32WordW
public import Lemmas.Flow.Step.ShapeTc

/-! # `w32k_norm`, and the named barrier whose count is the block's size

Promoted from FlashMLA's `Proof/Lib/Word.lean` (lane L2's G17, with `shape_barSyncN_block` of
G8'): `w32k_norm` is `w32_norm` with the forms of `Arith32WordWide` (`and.b32` with `-64`/`-4`,
`max.s32`, `neg.s32` on small words), and `w32k_close` closes an equation of words by it and then
by their numbers. Checked on FlashMLA's shapes: a length rounded down to a multiple of 64, a
signed maximum of two bounded values, and a ring slot's index.

`shape_barSyncN_block` is the named barrier whose count register holds the block's size — the case
`shape_barSyncNR` excludes (`hnb`) and `barTmpl` writes as `.bar id none .sync`. -/

namespace PTX.Tests.WordW
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

/-- A length rounded down to a multiple of 64 (`and.b32 %r, %r, -64`). -/
example (n : Nat) (hn : n < 2 ^ 32) : andi (W n) (-64) = W (n - n % 64) :=
  andi_W_neg64 hn

/-- A rounded-down length, closed by the word forms (`w32k_close`): the mask `-64` and the
subtraction that follows it are one modulo. -/
example (n : Nat) (hn : n < 2 ^ 32) : sub32 (W n) (andi (W n) (-64)) = W (n % 64) := by
  rw [andi_W_neg64 hn]
  w32k_close

/-- The signed maximum of two bounded values, as the numbers' maximum. -/
example (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    max32 (W a) (W b) = W (max a b) :=
  max32_W ha hb

/-- The mask `-4` of a ring slot, the form the slot update uses. -/
example (s : Nat) (hs : s < 2 ^ 32) : andi (W s) (-4) = W (s - s % 4) :=
  andi_W_neg4 hs

/-- The named barrier with the block's size as its count: the shape of `barrier.sync %r, %r` on a
count that equals the block, where `barTmpl` omits the count. -/
example {pc : Nat} {t : TState} {e : Event} {o : Option TState} {P : Event → Prop}
    {A : List Assumption} {L : Launch} {g : Nat} {a b : Opnd} {al : Bool} {id n : BitVec 64}
    (hf : Fires pc (eventTmpl A L g t (.barSyncN a b al)) e o)
    (ha : readBits L g t 32 a = .ok id) (hid : id.toNat < 16)
    (hb : readBits L g t 32 b = .ok n) (hn : n.toNat = L.block) (hn32 : L.block % 32 = 0)
    (hP : P ⟨pc, .bar id.toNat none .sync⟩) : P e :=
  shape_barSyncN_block hf ha hid hb hn hn32 hP

/-- And `site_shape` tries it after the count-carrying forms. -/
example : True := trivial

end PTX.Tests.WordW
