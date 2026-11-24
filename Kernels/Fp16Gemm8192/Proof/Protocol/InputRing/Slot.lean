-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Objects
public import Lemmas.Protocol.RingSlot

@[expose] public section

/-! # The input ring's slots as ring slots

Slot `s` of cluster `cluster`: the producers are the loader warps (warp 11) of the cluster's
two CTAs, each polling the empty barrier in its own CTA; the consumers are the two MMA warps
(warps 8 and 9) of the leader CTA, polling the full barrier; consumer `b`'s notification
to producer `a` is the arrival its commit makes on CTA `a`'s empty barrier. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.InputRing
open PTX MBarrier AsyncCopy

noncomputable section

def producerThread (L : Launch) (cluster : Nat) (a : Fin 2) (g : Nat) : Bool :=
  decide (g / L.block = 2 * cluster + a.val ∧ g % L.block / 32 = 11)

def consumerThread (L : Launch) (cluster : Nat) (b : Fin 2) (g : Nat) : Bool :=
  decide (g / L.block = 2 * cluster ∧ g % L.block / 32 = 8 + b.val)

def notification (L : Launch) (cluster : Nat) (a : Fin 2) (b : Fin 2) (r : Record Ref) : Bool :=
  match r.id with
  | .async i (.tcNotify rank) =>
    consumerThread L cluster b i.1 && decide (rank = a.val ∧ r.action = .arrive 1 0)
  | _ => false

/-- Slot `s` of cluster `cluster`. -/
def slot (L : Launch) (cluster : Nat) (s : Fin 4) : MbarRing.RingSlot 2 2 1 where
  full _ := Bar.loc L (2 * cluster) ⟨.input, s.val, true⟩
  empty a := Bar.loc L (2 * cluster + a.val) ⟨.input, s.val, false⟩
  owner _ := 0
  producer := producerThread L cluster
  consumer := consumerThread L cluster
  notification := notification L cluster

end
end PTX.Kernels.Fp16Gemm8192.Proof.InputRing
