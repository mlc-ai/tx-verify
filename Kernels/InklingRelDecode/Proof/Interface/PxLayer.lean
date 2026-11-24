-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.HsAll
public import Kernels.InklingRelDecode.Proof.Protocol.Lk5Final
public import Kernels.InklingRelDecode.Proof.Protocol.Lk5MRead
public import Kernels.InklingRelDecode.Proof.Protocol.IpTmSmBase
public import Kernels.InklingRelDecode.Proof.Thread.FrNn
public import Kernels.InklingRelDecode.Proof.Protocol.PxAll

@[expose] public section

/-! # What the result layer's `Px` files use of the protocol and thread layers

The rescale stores' coordinates (`Hs.ost_of`, `Hs.stRdv_of`), the scratch words and decisions of
every iteration (`Lk.decAgree_every`, `Lk.ldL_value`), the softmax region's Tensor Memory base
(`Rs.smBaseZero`) and the `f32` word of `1.0` (`Sm.valFloat_b32_one'`). -/
