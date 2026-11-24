-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Shape
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Sim
import Kernels.TmlFa4Fwd.Flow.Code.Part048
import Kernels.TmlFa4Fwd.Flow.Code.Part049
import Kernels.TmlFa4Fwd.Flow.Code.Part052
import Kernels.TmlFa4Fwd.Flow.Code.Part119
import Kernels.TmlFa4Fwd.Proof.Softmax.Shape

@[expose] public section

/-! # The addresses of the softmax warps' launch-word reads

As the correction warps' `EvR` (`CorrWarp/Read.lean`): the softmax warps' shape table states a
scheduler read without its address (`rdOrUb`); `EvR` is a second shape table for the scan's reads,
the chosen request's two reads (the output warp's shapes of `toE d`) and the used-K read
(`ukAddr`), and says nothing at other sites. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

/-- The used-K read's address: the chosen request's word of the used-K array. -/
def ukAddr (p : Params) (d : D) : BitVec 64 :=
  truncBits 64 (Epilogue.vbits (Epilogue.addrS p.usedKBase (chosen d.v.sc))) + BitVec.ofInt 64 0

/-- The reads' shapes with their addresses. -/
def EvR (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .word _ | .q0 | .q1 => Epilogue.Ev p L g (toE d) e
  | .uk => (∃ bs, e.kind = .rd (Epilogue.wordAcc (ukAddr p d).toNat) bs) ∨ ∃ f, e.kind = .ub f
  | _ => True

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option hygiene false in
/-- The shape obligations of the reads that the theorem's `hs` admits. -/
local macro "rd_shape" : tactic => `(tactic|
  site_shape s skip_by (simp at hs)
    unfolding [EvR, Epilogue.Ev, Epilogue.rdAddr, ukAddr, toE, epi, Epilogue.vbits]
    reg_vals [valueOf, values, valuesStart, valuesRole, valuesScan, valuesSelect,
      valuesSelect2, valuesReq, valuesTile, Epilogue.partials, Epilogue.loopRegs,
      Epilogue.lanePreds, lookupLit, livePc]
    addr_by (soft_addr))

theorem shapeR_word (_hp : Pre p L m) (d : D) (hk : d.k = 0) (ha : d.acc = []) (k : Epilogue.Scan)
    (hs : d.site = .word k) : (code p L g).ShapeAt (EvR p L g) d := by
  obtain ⟨s, v, k', acc⟩ := d
  cases hk
  cases ha
  cases k <;> rd_shape

theorem shapeR_req (_hp : Pre p L m) (d : D) (hk : d.k = 0) (ha : d.acc = [])
    (hs : d.site = .q0 ∨ d.site = .q1 ∨ d.site = .uk) : (code p L g).ShapeAt (EvR p L g) d := by
  obtain ⟨s, v, k', acc⟩ := d
  cases hk
  cases ha
  rd_shape

end
end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
