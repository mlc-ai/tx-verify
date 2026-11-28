-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.UbPrefix
public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
import Kernels.InklingRelDecode.Proof.Common.Table
import Lemmas.Kernel.Followed

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow

@[no_expose] def Follow (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g, g < L.threads → ∀ k, Frame.FollowedAt (thread Q L) (guardedTable Q L) X g k

end PTX.Kernels.InklingRelDecode.Proof
