-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Mul2NVal

@[expose] public section

/-! # The packed product on pairs that read as extended reals

`floatE_mul2N_reads`: `mul.f32x2` (no rounding modifier) on two pairs whose `pairRead` is given is
the pair of the products' words (as `floatE_mul2N_fin` for pairs of numbers). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

theorem floatE_mul2N_reads {va vb : Value} {x0 x1 y0 y1 z0 z1 : EReal}
    (hx : pairRead va = some (.ok (x0, x1))) (hy : pairRead vb = some (.ok (y0, y1)))
    (hz0 : mulEReal x0 y0 = some z0) (hz1 : mulEReal x1 y1 = some z1) :
    floatE mul2NI [va, vb] = .ok (.pair (erealValue .f32 z0) (erealValue .f32 z1)) := by
  simp only [floatE, idealVal, hx, hy, bindRead, hz0, hz1, pure, Except.pure]

end
end PTX.Flow
