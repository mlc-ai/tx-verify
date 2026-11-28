-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Cnt

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open Control

/-- The sites of the rescale of the accumulator: from the `o_done` poll to the wait for the
rescale store. -/
def Site.late : Site → Bool
  | .waitO | .bar22 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10 | .bar23 | .ldL | .shfl11
  | .shfl12 | .ldO | .waitLdO | .bar24 | .stO | .waitStO => true
  | _ => false

/-- The first iteration goes directly from the reduction to P publication.
Consequently the O poll, and with it every site of the rescale (the load and the store of the
accumulator), can occur only on a later iteration. -/
structure Ref (t : Nat) (d : D) (c : Cnt) : Prop where
  ledger : c = counts t d
  late : d.site.late = true → 0 < d.i

theorem Ref.oWait {t d c} (r : Ref t d c) : d.site = .waitO → 0 < d.i :=
  fun h => r.late (by rw [h]; rfl)

theorem initial_ref (t : Nat) : Ref t {} ⟨0,0,0⟩ :=
  ⟨by simp [counts,Site.afterO,Site.afterS],nofun⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax
