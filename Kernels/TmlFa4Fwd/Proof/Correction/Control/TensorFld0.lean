-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorTable
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part133
import Kernels.TmlFa4Fwd.Flow.Code.Part134
import Kernels.TmlFa4Fwd.Flow.Code.Part135
import Kernels.TmlFa4Fwd.Flow.Code.Part136

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control

set_option maxRecDepth 100000

private theorem row0 : loadOk (.fld 0 0) (.fwl 0 0) false = true := by
  load_row (.fld 0 0) via Flow.code_8480

private theorem row1 : loadOk (.fld 0 1) (.fwl 0 1) false = true := by
  load_row (.fld 0 1) via Flow.code_8499

private theorem row2 : loadOk (.fld 0 2) (.fwl 0 2) false = true := by
  load_row (.fld 0 2) via Flow.code_8518

private theorem row3 : loadOk (.fld 0 3) (.fwl 0 3) false = true := by
  load_row (.fld 0 3) via Flow.code_8537

private theorem row4 : loadOk (.fld 0 4) (.fwl 0 4) false = true := by
  load_row (.fld 0 4) via Flow.code_8555

private theorem row5 : loadOk (.fld 0 5) (.fwl 0 5) false = true := by
  load_row (.fld 0 5) via Flow.code_8572

private theorem row6 : loadOk (.fld 0 6) (.fwl 0 6) false = true := by
  load_row (.fld 0 6) via Flow.code_8589

private theorem row7 : loadOk (.fld 0 7) (.fwl 0 7) false = true := by
  load_row (.fld 0 7) via Flow.code_8606

private theorem row8 : loadOk (.fld 0 8) (.fwl 0 8) false = true := by
  load_row (.fld 0 8) via Flow.code_8623

private theorem row9 : loadOk (.fld 0 9) (.fwl 0 9) false = true := by
  load_row (.fld 0 9) via Flow.code_8640

private theorem row10 : loadOk (.fld 0 10) (.fwl 0 10) false = true := by
  load_row (.fld 0 10) via Flow.code_8657

private theorem row11 : loadOk (.fld 0 11) (.fwl 0 11) false = true := by
  load_row (.fld 0 11) via Flow.code_8674

private theorem row12 : loadOk (.fld 0 12) (.fwl 0 12) false = true := by
  load_row (.fld 0 12) via Flow.code_8691

private theorem row13 : loadOk (.fld 0 13) (.fwl 0 13) false = true := by
  load_row (.fld 0 13) via Flow.code_8708

private theorem row14 : loadOk (.fld 0 14) (.fwl 0 14) false = true := by
  load_row (.fld 0 14) via Flow.code_8725

private theorem row15 : loadOk (.fld 0 15) (.fwl 0 15) false = true := by
  load_row (.fld 0 15) via Flow.code_8742

theorem fld_table0 (c : Fin 16) : loadOk (.fld 0 c) (.fwl 0 c) false = true := by
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
