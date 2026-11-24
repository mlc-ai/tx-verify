-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Ideal
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position

@[expose] public section

/-! # The picked tile is the CTA's -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof

theorem picked_cta {p : Params} {L : Launch} {g h R : Nat} {b : BitVec 64}
    (hc : g / L.block = h / L.block) (hP : Epilogue.Picked p L g R b) :
    Epilogue.Picked p L h R b :=
  Epilogue.Picked.cta hc hP

end PTX.Kernels.TmlFa4Fwd.Proof
