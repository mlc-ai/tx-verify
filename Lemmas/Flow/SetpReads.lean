-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.W0Reads
public import Lemmas.Flow.SetpCore

@[expose] public section

/-! # The comparison of two values that read as extended reals

`setpE_reads`: the comparison `setp.<cmp>.f32` of two operands whose `readEReal` is given is the
comparison of the extended reals (as `setpE_fin` for numbers). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

theorem setpE_reads {c : FCmp} {cmp : Cmp} {fz : Bool} {va vb : Value} {x y : EReal}
    (hc : c = .ord cmp ∨ c = .unord cmp) (hx : readEReal .f32 va = some (.ok x))
    (hy : readEReal .f32 vb = some (.ok y)) :
    setpE c fz va vb = .ok (erealCompare cmp x y) := by
  have hbase : fcmpBase c = some cmp := by rcases hc with rfl | rfl <;> rfl
  simp only [setpE, idealSetp, hbase, hx, hy, bindRead, pure, Except.pure]

end
end PTX.Flow
