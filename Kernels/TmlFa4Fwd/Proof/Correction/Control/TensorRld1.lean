-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorTable
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part129
import Kernels.TmlFa4Fwd.Flow.Code.Part130
import Kernels.TmlFa4Fwd.Flow.Code.Part131

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control

set_option maxRecDepth 100000

private theorem row0 : loadOk (.rld 1 0) (.rldw 1 0) true = true := by
  load_row (.rld 1 0) via Flow.code_8231

private theorem row1 : loadOk (.rld 1 1) (.rldw 1 1) true = true := by
  load_row (.rld 1 1) via Flow.code_8258

private theorem row2 : loadOk (.rld 1 2) (.rldw 1 2) true = true := by
  load_row (.rld 1 2) via Flow.code_8284

private theorem row3 : loadOk (.rld 1 3) (.rldw 1 3) true = true := by
  load_row (.rld 1 3) via Flow.code_8310

private theorem row4 : loadOk (.rld 1 4) (.rldw 1 4) true = true := by
  load_row (.rld 1 4) via Flow.code_8336

private theorem row5 : loadOk (.rld 1 5) (.rldw 1 5) true = true := by
  load_row (.rld 1 5) via Flow.code_8362

private theorem row6 : loadOk (.rld 1 6) (.rldw 1 6) true = true := by
  load_row (.rld 1 6) via Flow.code_8388

private theorem row7 : loadOk (.rld 1 7) (.rldw 1 7) true = true := by
  load_row (.rld 1 7) via Flow.code_8414

theorem rld_table1 (c : Fin 8) : loadOk (.rld 1 c) (.rldw 1 c) true = true := by
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
