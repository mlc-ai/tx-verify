-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.StoreSpan

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control

set_option maxRecDepth 100000

theorem store_fence_span {p L g v} (st : Fin 2) : StoreSpan p L g v st 15 1 := by
  have table : ∀ st, spanOk (.fst st 15 1) (.fence st) = true ∧
      (liveAt (.fence st)).all (liveAt (.fst st 15 1)).contains = true := by decide +kernel
  refine copy_span (s := .fst st 15 1) (dst := .fence st) (p := p) (L := L) (g := g)
    (v := v) (k := 3) (table st).1 (table st).2 ?_
  exact fun _ _ => rfl

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
