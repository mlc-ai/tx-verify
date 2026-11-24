-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Actors
public import Kernels.Fp16Gemm8192.Proof.Interface
public import Lemmas.Protocol.Poller

@[expose] public section

/-! # The actors of the input ring's records

The input objects of a slot, the role of a selected thread that polls one of them, and the one
thread of each selector that polls successfully (`producerOf`, `consumerOf`): a selector's
records are that thread's, since any two of its threads that poll successfully are one
(`Actors.producer_unique`, `Actors.consumer_unique`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace InputRing

section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The producer thread of selector `a` that polls slot `s`'s empty barrier successfully. -/
def producerOf (L : Launch) (X : Execution) (c : Nat) (s : Fin 4) (a : Fin 2) : Nat :=
  pollerOf X (producerThread L c a) ((slot L c s).empty a) ((2 * c + a.val) * L.block + 352)

/-- The consumer thread of selector `b` that polls slot `s`'s full barrier successfully. -/
def consumerOf (L : Launch) (X : Execution) (c : Nat) (s : Fin 4) (b : Fin 2) : Nat :=
  pollerOf X (consumerThread L c b) ((slot L c s).full 0) ((2 * c) * L.block + 32 * (8 + b.val))

theorem producerOf_thread (hpre : Pre P L mem0) (c : Nat) (s : Fin 4) (a : Fin 2) :
    producerThread L c a (producerOf L X c s a) = true :=
  pollerOf_sel (by simp only [producerThread, decide_eq_true_eq, hpre.block]; omega)

theorem consumerOf_thread (hpre : Pre P L mem0) (c : Nat) (s : Fin 4) (b : Fin 2) :
    consumerThread L c b (consumerOf L X c s b) = true := by
  have := b.isLt
  exact pollerOf_sel (by simp only [consumerThread, decide_eq_true_eq, hpre.block]; omega)

/-- A producer thread of selector `a` that polls slot `s`'s empty barrier successfully is
`producerOf`. -/
theorem producerOf_eq (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {s : Fin 4} {a : Fin 2} {g j pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hprod : producerThread L c a g = true)
    (he : X.get (g, j) = some ⟨pc, .wait ((slot L c s).empty a) p true acq sc⟩) :
    g = producerOf L X c s a :=
  pollerOf_eq (fun hg hh he he' => producer_unique hX ht hg hh he he' rfl rfl) hprod he

/-- A consumer thread of selector `b` that polls slot `s`'s full barrier successfully is
`consumerOf`. -/
theorem consumerOf_eq (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {s : Fin 4} {b : Fin 2} {g j pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hcons : consumerThread L c b g = true)
    (he : X.get (g, j) = some ⟨pc, .wait ((slot L c s).full 0) p true acq sc⟩) :
    g = consumerOf L X c s b :=
  pollerOf_eq (fun hg hh he he' => consumer_unique hX ht hg hh he he' rfl rfl) hcons he

/-- Two threads of CTAs `2c` and `2c + 1`, and a shared byte of one of those CTAs, are in one
`cta_group::2` pair (EXT-PAIR-ASYNC). -/
theorem pairAsync_of_pair (hpre : Pre P L mem0) {a b : Nat} {l : Loc} (hsh : l.space = .shared)
    (ha : a < L.threads) (hb : b < L.threads)
    (hlc : l.cta = a / L.block ∨ l.cta = b / L.block) (hab : a / L.block / 2 = b / L.block / 2) :
    PairAsync L l a b := by
  have hga : a / L.block < L.grid := by
    unfold Launch.threads at ha
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact ha)
  have hgb : b / L.block < L.grid := by
    unfold Launch.threads at hb
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hb)
  have hlg : l.cta < L.grid := by rcases hlc with h | h <;> omega
  refine ⟨hsh, (sameCtaGroup_iff L .two _ _).2 ⟨⟨hga, hgb, ?_⟩, ?_⟩,
    (sameCtaGroup_iff L .two _ _).2 ⟨⟨hga, hlg, ?_⟩, ?_⟩⟩ <;>
    simp only [clusterOfCta_eq hpre, rankOfCta_eq hpre, CtaGroup.size] <;> omega

end

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
