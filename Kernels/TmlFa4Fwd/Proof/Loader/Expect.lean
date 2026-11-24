-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Ledger
public import Kernels.TmlFa4Fwd.Proof.Loader.ShapeAll

@[expose] public section

/-! # What a loader event must return -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

/-- What an event at a counted state must return: a value of the site's kind. -/
def Expect (dn : D × (Cnt → Nat)) (e : Event) : Prop := (ret dn.1).accepts e

end PTX.Kernels.TmlFa4Fwd.Proof.Loader
