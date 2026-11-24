-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorTable
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Flow.Code.Part138
import Kernels.TmlFa4Fwd.Flow.Code.Part139
import Kernels.TmlFa4Fwd.Flow.Code.Part140
import Kernels.TmlFa4Fwd.Flow.Code.Part141

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control

set_option maxRecDepth 100000

private theorem row0 : loadOk (.fld 1 0) (.fwl 1 0) false = true := by
  load_row (.fld 1 0) via Flow.code_8776

private theorem row1 : loadOk (.fld 1 1) (.fwl 1 1) false = true := by
  load_row (.fld 1 1) via Flow.code_8795

private theorem row2 : loadOk (.fld 1 2) (.fwl 1 2) false = true := by
  load_row (.fld 1 2) via Flow.code_8814

private theorem row3 : loadOk (.fld 1 3) (.fwl 1 3) false = true := by
  load_row (.fld 1 3) via Flow.code_8833

private theorem row4 : loadOk (.fld 1 4) (.fwl 1 4) false = true := by
  load_row (.fld 1 4) via Flow.code_8851

private theorem row5 : loadOk (.fld 1 5) (.fwl 1 5) false = true := by
  load_row (.fld 1 5) via Flow.code_8868

private theorem row6 : loadOk (.fld 1 6) (.fwl 1 6) false = true := by
  load_row (.fld 1 6) via Flow.code_8885

private theorem row7 : loadOk (.fld 1 7) (.fwl 1 7) false = true := by
  load_row (.fld 1 7) via Flow.code_8902

private theorem row8 : loadOk (.fld 1 8) (.fwl 1 8) false = true := by
  load_row (.fld 1 8) via Flow.code_8919

private theorem row9 : loadOk (.fld 1 9) (.fwl 1 9) false = true := by
  load_row (.fld 1 9) via Flow.code_8936

private theorem row10 : loadOk (.fld 1 10) (.fwl 1 10) false = true := by
  load_row (.fld 1 10) via Flow.code_8953

private theorem row11 : loadOk (.fld 1 11) (.fwl 1 11) false = true := by
  load_row (.fld 1 11) via Flow.code_8970

private theorem row12 : loadOk (.fld 1 12) (.fwl 1 12) false = true := by
  load_row (.fld 1 12) via Flow.code_8987

private theorem row13 : loadOk (.fld 1 13) (.fwl 1 13) false = true := by
  load_row (.fld 1 13) via Flow.code_9004

private theorem row14 : loadOk (.fld 1 14) (.fwl 1 14) false = true := by
  load_row (.fld 1 14) via Flow.code_9021

private theorem row15 : loadOk (.fld 1 15) (.fwl 1 15) false = true := by
  load_row (.fld 1 15) via Flow.code_9038

theorem fld_table1 (c : Fin 16) : loadOk (.fld 1 c) (.fwl 1 c) false = true := by
  fin_cases c
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
