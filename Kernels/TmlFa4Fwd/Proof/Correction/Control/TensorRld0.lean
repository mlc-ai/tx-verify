-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorTable
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part126
import Kernels.TmlFa4Fwd.Flow.Code.Part127
import Kernels.TmlFa4Fwd.Flow.Code.Part128

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control

set_option maxRecDepth 100000

private theorem row0 : loadOk (.rld 0 0) (.rldw 0 0) true = true := by
  load_row (.rld 0 0) via Flow.code_8012

private theorem row1 : loadOk (.rld 0 1) (.rldw 0 1) true = true := by
  load_row (.rld 0 1) via Flow.code_8039

private theorem row2 : loadOk (.rld 0 2) (.rldw 0 2) true = true := by
  load_row (.rld 0 2) via Flow.code_8065

private theorem row3 : loadOk (.rld 0 3) (.rldw 0 3) true = true := by
  load_row (.rld 0 3) via Flow.code_8091

private theorem row4 : loadOk (.rld 0 4) (.rldw 0 4) true = true := by
  load_row (.rld 0 4) via Flow.code_8117

private theorem row5 : loadOk (.rld 0 5) (.rldw 0 5) true = true := by
  load_row (.rld 0 5) via Flow.code_8143

private theorem row6 : loadOk (.rld 0 6) (.rldw 0 6) true = true := by
  load_row (.rld 0 6) via Flow.code_8169

private theorem row7 : loadOk (.rld 0 7) (.rldw 0 7) true = true := by
  load_row (.rld 0 7) via Flow.code_8195

theorem rld_table0 (c : Fin 8) : loadOk (.rld 0 c) (.rldw 0 c) true = true := by
  fin_cases c
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
