-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.QyKv
public import Kernels.InklingRelDecode.Proof.Result.QyPRead
public import Kernels.InklingRelDecode.Proof.Result.QyOBase
public import Kernels.InklingRelDecode.Proof.Result.QyElems
public import Kernels.InklingRelDecode.Proof.Result.QyLoad
public import Kernels.InklingRelDecode.Proof.Result.QySmOLoad

@[expose] public section

/-! # The result layer's `Qy` files

All on every consistent execution, without `Complete`:

* `QyKv`: `elemB_of` (`Qx.ElemRest.b`), the K/V bytes of every MMA from the copy
  `Wz.KvCopiesF` names and its spec;
* `QyPRead`: `pReadSrcF` (the read source of a PV MMA's A cell, every row), `pvA_of`
  (`Qx.ElemRest.pvA`), `aSource_of` (`Qx.SourceRest.a`);
* `QyOBase`: `oBaseF`, `oBase_of` (`Qx.ElemRest.oBase`, restated with the MMA's event);
* `QyElems`: `elemRest_of`, `LdSmRest`, `sourceRest_of`;
* `QyLoad`: `sPstAfterF` (`Rd.SPstAfter`), `sLoadSrcF`, `oLoadSrcF` (the sources of the S load
  and the rescale load, every row), `ldSm_of` (`Qy.LdSmRest`, `Qx.SourceRest.ldSm`);
* `QySmOLoad`: `smOLoad_of` (`Interface.Lk.SmOLoadOk`: the products of the O rescale have
  outcomes). -/
