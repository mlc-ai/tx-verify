-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.QxEpiLoad
public import Kernels.InklingRelDecode.Proof.Protocol.FrSm
public import Kernels.InklingRelDecode.Proof.Interface.FrEpi
public import Kernels.InklingRelDecode.Proof.Interface.FrTcData

@[expose] public section

/-! # What the result layer's `Qx` files use of the protocol and thread layers

The epilogue's load check from `f32` words (`Epi.loadOk_of_fl`), the reciprocal as an `f32`
number (`Epi.prm_inv_fl`), the statement of the check (`Interface.Lk.EpiLoadOk`) and the states of
the `tcgen05.ld` events (`Interface.Lk.tcld_event`). -/
