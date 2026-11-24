-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.LpCopy
public import Kernels.InklingRelDecode.Proof.Result.LpProCopy

@[expose] public section

/-!
# The KV copies of every block (umbrella)

* `LpCopy`: the loader's half of `KvCopies` (`Lp.loader_copy_exists`, blocks `num_pre ≤ i`);
* `LpProCopy`: the prologue's half (`Lp.pro_copy_exists`, blocks `i < num_pre`) and
  `Lp.kvCopies_of : Result.Mma.KvCopies Q L X`.
-/
