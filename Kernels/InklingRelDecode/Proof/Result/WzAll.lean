-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.WzOperand
public import Kernels.InklingRelDecode.Proof.Result.WzKvCopies

@[expose] public section

/-! # The `Wz` files of the result layer

* `WzOperand`: `OperandSourcesT` from `QTileF` and `KvCopiesF`, and `qTileF_of`;
* `WzKvCopies`: `kvCopiesF_of`, the copies of a block an issued MMA reads. -/
