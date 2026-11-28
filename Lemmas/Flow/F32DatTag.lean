-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedSingleG
public import Lemmas.Flow.FmaTotal

@[expose] public section

/-! # An `.f32` datum of four bytes that is no slice has the tag `dat32`

`F32Dat` alone does not give `TagF.dat32` (`Dat32` also needs four bytes and no slice of a wider
value: a slice of an opaque payload can classify as an `.f32`), and a bit pattern's `.bits 32` is
stronger than both; `TagF.sat` lets a `.bits 32` register serve a `dat32` use, not the reverse. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof

theorem dat32_ok_of_f32Dat {v : Value} (h : F32Dat v) (hb : v.bytes = 4)
    (hs : ∀ w o n, v ≠ .slice w o n) : TagF.dat32.ok (some v) :=
  ⟨v, rfl, h, hb, hs⟩

end PTX.Flow.TyG
