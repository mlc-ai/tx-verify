-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Batches
public import Kernels.FlashKdaFwd.Packed.Activation
public import Kernels.FlashKdaFwd.Packed.StateMap
public import Core.Assembly.Correctness

@[expose] public section
namespace FlashKda.Packed
open PTX Sequence Batches Chunk
noncomputable section

structure Problem where
  sequences : Nat
  heads : Nat
  length : Nat → Nat
  query : Nat → Nat → Nat → Row 128
  key : Nat → Nat → Nat → Row 128
  logDecay : Nat → Nat → Nat → Row 128
  betaLogit : Nat → Nat → Nat → ℝ
  value : Nat → Nat → Nat → Fin 128 → ℝ
  initial : Nat → Nat → Fin 128 → Row 128
  scale : ℝ
  outputBase : Nat
  stateBase : Nat

def Problem.tokens (p : Problem) (seq head : Nat) (v : Fin 128) : Tokens 128 where
  key := p.key seq head
  query := p.query seq head
  logDecay := p.logDecay seq head
  value t := p.value seq head t v
  strength t := Activation.strength (p.betaLogit seq head t)

def Problem.state (p : Problem) (seq head : Nat) (v : Fin 128) (t : Nat) : Row 128 :=
  tokenState (p.tokens seq head v) (p.initial seq head v) t

def Problem.outputLoc (p : Problem) (seq head t : Nat) (v : Fin 128) : Loc :=
  ⟨.global, 0, p.outputBase + 2 * (((firstToken p.length seq + t) * p.heads + head) * 128 + v)⟩

def Problem.stateLoc (p : Problem) (seq head : Nat) (v k : Fin 128) : Loc :=
  ⟨.global, 0, p.stateBase + 65536*(seq*p.heads+head) + 512*v.val + 4*k.val⟩

def Post (p : Problem) (initial : Mem0) (m : FinalMem) : Prop :=
  (∀ seq < p.sequences, ∀ head < p.heads, ∀ t < p.length seq, ∀ v,
    memFloat .bf16 m (p.outputLoc seq head t v) =
      .ok (p.scale * dot (p.state seq head v (t+1)) (p.query seq head t))) ∧
  (∀ seq < p.sequences, ∀ head < p.heads, ∀ v k,
    memFloat .f32 m (p.stateLoc seq head v k) = .ok (p.state seq head v (p.length seq) k)) ∧
  ∀ l, l.space = .global →
    ¬ (l.cta = 0 ∧ ((p.outputBase ≤ l.addr ∧
        l.addr < p.outputBase + 256 * (firstToken p.length p.sequences) * p.heads) ∨
      (p.stateBase ≤ l.addr ∧ l.addr < p.stateBase + 65536 * p.sequences * p.heads))) →
    m l = initial l

theorem state_destination (p : Problem) {seq head : Nat} (hs : seq < p.sequences)
    (hh : head < p.heads) (v k : Fin 128) (b : Fin 4)
    (allocation : TensorDescriptor.AllocationClass) (smem : Loc) :
    ∃ (i : Fin 16) (col : Fin 8),
      (StateMap.strip p.stateBase (p.sequences*p.heads) (seq*p.heads+head) allocation smem i
      ).globalAddress (StateMap.slot p.stateBase (p.sequences*p.heads) allocation col v b) =
        some ((p.stateLoc seq head v k).addr + b.val) := by
  have h : (seq+1)*p.heads ≤ p.sequences*p.heads := Nat.mul_le_mul_right _ hs
  rw [Nat.add_mul, Nat.one_mul] at h
  exact StateMap.covers _ _ _ _ _ (by omega) k v b

end
end FlashKda.Packed
