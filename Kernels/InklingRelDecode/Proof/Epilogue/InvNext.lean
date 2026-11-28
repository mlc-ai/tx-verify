-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Steps.Base

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
open PTX PTX.Flow PTX.Proof

theorem inv_next {e L g d dn ev} (hi : Inv e (g%L.block) d)
    (move : next e L g d ev=some (some dn)) : Inv e (g%L.block) dn := by
  obtain ⟨s,v⟩ := d
  cases s <;> simp only [next] at move
  all_goals repeat' split at move
  all_goals cases move
  all_goals first | trivial | exact hi.1 | exact first_inv .. | exact store_inv _ hi _

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
