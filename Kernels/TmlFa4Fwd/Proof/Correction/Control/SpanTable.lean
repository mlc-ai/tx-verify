-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Span

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control

set_option maxRecDepth 100000

theorem fld_span (st : Fin 2) (j : Fin 16) :
    spanOk (.fld st j) (.fwl st j) = true := by
  revert st j
  decide +kernel

theorem rldw_span (st : Fin 2) (c : Fin 8) :
    spanOk (.rldw st c) (.rst st c) = true ∧
    (liveAt (.rst st c)).all (liveAt (.rldw st c)).contains = true := by
  revert st c
  decide +kernel

theorem fwl_span (st : Fin 2) (j : Fin 16) :
    spanOk (.fwl st j) (.fst st j 0) = true ∧
    (liveAt (.fst st j 0)).all (liveAt (.fwl st j)).contains = true := by
  revert st j
  decide +kernel

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
