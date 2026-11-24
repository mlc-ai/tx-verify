-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.QxValues
public import Kernels.InklingRelDecode.Proof.Result.QxQTile
public import Kernels.InklingRelDecode.Proof.Result.QxElems
public import Kernels.InklingRelDecode.Proof.Result.QxEpi
public import Kernels.InklingRelDecode.Proof.Result.QxSource

@[expose] public section

/-! # The result layer's `Qx` files

`QxValues` (`values_of`: `CompletedValues` of every MMA from `ElemPrem`), `QxQTile` (`qk_a_real`:
the A elements of every QK MMA, every row), `QxElems` (`ElemRest`, `elemPrem_of`), `QxEpi`
(`epiLoad_of`: the epilogue's load check from the source of its load and the `f32` results),
`QxSource` (`tcSource_of`: the read sources, given `SourceRest`). -/
