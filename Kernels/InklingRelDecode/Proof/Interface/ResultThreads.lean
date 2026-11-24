-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvWMma
public import Kernels.InklingRelDecode.Proof.Thread.BrEmpty
public import Kernels.InklingRelDecode.Proof.Thread.EpiValue
public import Kernels.InklingRelDecode.Proof.Thread.EvDEpiMeans

@[expose] public section

/-! # The thread-layer modules the `Result` layer reads

The MMA warp's event shape, the epilogue's value tables and the empty-split branch. The result
layer imports them through this module. -/
