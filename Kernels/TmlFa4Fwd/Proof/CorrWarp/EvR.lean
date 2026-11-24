-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Sim
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Shape

@[expose] public section

/-! # The shapes of the correction warps' scheduler reads, with their addresses -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen)

noncomputable section

/-- The used-K read's address: the chosen request's word of the used-K array. -/
def ukAddr (p : Params) (d : D) : BitVec 64 :=
  truncBits 64 (Epilogue.vbits (Epilogue.addrS p.usedKBase (chosen d.v.sc))) + BitVec.ofInt 64 0

/-- The reads' shapes with their addresses. -/
def EvR (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .word _ | .q0 | .q1 => Epilogue.Ev p L g (toE d) e
  | .uk => (∃ bs, e.kind = .rd (Epilogue.wordAcc (ukAddr p d).toNat) bs) ∨ ∃ f, e.kind = .ub f
  | _ => True

end
end PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
