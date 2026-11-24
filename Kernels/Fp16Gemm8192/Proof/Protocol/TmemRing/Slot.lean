-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Rings
public import Lemmas.Protocol.RingSlot
public import Lemmas.Order.CausalThreadCount

@[expose] public section

/-! # The accumulator ring's buffers as ring slots

Buffer `j` of cluster `cluster`: the producer is MMA warp `8 + j` of the leader CTA, polling
the buffer's empty barrier; the 256 consumers are the threads of warps `4 j` to `4 j + 3` of
both CTAs, consumer `b` being thread `b % 128` of them in CTA `2 * cluster + b / 128`, which
polls the full barrier of its CTA (`owner b = b / 128`). Consumer `b`'s notification is its
own arrival on the empty barrier. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.TmemRing
open PTX MBarrier AsyncCopy

noncomputable section

def producerThread (L : Launch) (cluster : Nat) (j : Fin 2) (g : Nat) : Bool :=
  decide (g / L.block = 2 * cluster ∧ g % L.block / 32 = 8 + j.val)

/-- Consumer `b` of buffer `j`. -/
def consumerOf (L : Launch) (cluster : Nat) (j : Fin 2) (b : Fin 256) : Nat :=
  (2 * cluster + b.val / 128) * L.block + 128 * j.val + b.val % 128

/-- Buffer `j` of cluster `cluster`. -/
def slot (L : Launch) (cluster : Nat) (j : Fin 2) : MbarRing.RingSlot 1 256 2 where
  full k := Bar.loc L (2 * cluster + k.val) ⟨.acc, j.val, true⟩
  empty _ := Bar.loc L (2 * cluster) ⟨.acc, j.val, false⟩
  owner b := ⟨b.val / 128, by omega⟩
  producer _ := producerThread L cluster j
  consumer b g := decide (g = consumerOf L cluster j b)
  notification _ b := threadArrival (consumerOf L cluster j b)

/-- Consumer `b`'s CTA. -/
theorem consumerOf_div {L : Launch} (hb : 256 ≤ L.block) (cluster : Nat) (j : Fin 2)
    (b : Fin 256) : consumerOf L cluster j b / L.block = 2 * cluster + b.val / 128 := by
  have := j.isLt
  have := b.isLt
  simp only [consumerOf, Nat.add_assoc]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
    Nat.zero_add]

/-- Consumer `b`'s thread index in its CTA. -/
theorem consumerOf_mod {L : Launch} (hb : 256 ≤ L.block) (cluster : Nat) (j : Fin 2)
    (b : Fin 256) : consumerOf L cluster j b % L.block = 128 * j.val + b.val % 128 := by
  have := j.isLt
  have := b.isLt
  simp only [consumerOf, Nat.add_assoc]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

/-- The consumers of a buffer are distinct threads, when a CTA has at least 256 threads. -/
theorem consumerOf_inj {L : Launch} (hb : 256 ≤ L.block) {cluster : Nat} {j : Fin 2}
    {b q : Fin 256} (h : consumerOf L cluster j b = consumerOf L cluster j q) : b = q := by
  have h1 := consumerOf_div hb cluster j b
  have h2 := consumerOf_mod hb cluster j b
  rw [h, consumerOf_div hb] at h1
  rw [h, consumerOf_mod hb] at h2
  have := b.isLt
  have := q.isLt
  exact Fin.ext (by omega)

/-- A thread of warps `4 j` to `4 j + 3` of the cluster's CTAs is a consumer of buffer `j`. -/
theorem consumerOf_of {L : Launch} {cluster : Nat} {j : Fin 2} {g : Nat}
    (hc : g / L.block / 2 = cluster) (hw : g % L.block / 32 / 4 = j.val) :
    consumerOf L cluster j ⟨(g / L.block - 2 * cluster) * 128 + g % L.block % 128, by omega⟩ = g :=
      by
  have := j.isLt
  simp only [consumerOf]
  have h1 : (g / L.block - 2 * cluster) * 128 + g % L.block % 128 < 256 := by omega
  have h2 : ((g / L.block - 2 * cluster) * 128 + g % L.block % 128) / 128 = g / L.block - 2 *
    cluster := by omega
  have h3 : ((g / L.block - 2 * cluster) * 128 + g % L.block % 128) % 128 = g % L.block % 128 := by
    omega
  rw [h2, h3]
  have := Nat.div_add_mod g L.block
  have : 2 * cluster + (g / L.block - 2 * cluster) = g / L.block := by omega
  rw [this]
  have : g % L.block = 128 * j.val + g % L.block % 128 := by omega
  rw [Nat.add_assoc, ← this, Nat.mul_comm]
  exact Nat.div_add_mod g L.block

end
end PTX.Kernels.Fp16Gemm8192.Proof.TmemRing
