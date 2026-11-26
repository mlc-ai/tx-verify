-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Math.Algorithm

@[expose] public section
namespace PTX.Kernels.FlashKdaFwd.Math.Sequence
noncomputable section
open Chunk Block Algorithm Recurrence

def activate {d : ℕ} (q k gate : ℕ → Row d) (v logits : ℕ → ℝ)
    (lower parameter : ℝ) (bias : Row d) : Tokens d where
  key t := normalize (k t)
  query t := normalize (q t)
  value := v
  strength t := sigmoid (logits t)
  logDecay t := logGate lower parameter bias (gate t)

variable {d : ℕ}

theorem state_shift (x : Tokens d) (s : Row d) (offset t : ℕ) :
    tokenState (suffix x offset) (tokenState x s offset) t = tokenState x s (offset+t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step (tokenState (suffix x offset) (tokenState x s offset) t) _ _ _ _ =
      step (tokenState x s (offset+t)) _ _ _ _
    rw [ih]
    rfl

def runBlock (x : Tokens d) (s : Row d) (len : ℕ) (scale : ℝ) : (ℕ → ℝ) × Row d :=
  let k := fun t => if t < len then x.key t else fun _ => 0
  let p := cum (fun t => if t < len then x.logDecay t else fun _ => 0)
  let u := corrections s p k x.value x.strength
  (blockOutput s p k x.query u scale, exitState s p k u)

theorem runBlock_eq (x : Tokens d) (s : Row d) {len : ℕ} (h : len ≤ 16) (scale : ℝ) :
    (∀ t < len, (runBlock x s len scale).1 t = scale * dot (tokenState x s (t+1)) (x.query t)) ∧
      (runBlock x s len scale).2 = tokenState x s len :=
  forward_chunk h s x.logDecay x.key x.query x.value x.strength scale

theorem live_le (total b : ℕ) : liveRows total b ≤ 16 := min_le_left _ _

theorem next_cursor (total b : ℕ) :
    cursor total b + liveRows total b = cursor total (b+1) := by
  simp only [cursor, liveRows, Nat.mul_succ]
  omega

def carry (x : Tokens d) (initial : Row d) (total : ℕ) (scale : ℝ) : ℕ → Row d
  | 0 => initial
  | b+1 => (runBlock (suffix x (cursor total b)) (carry x initial total scale b)
      (liveRows total b) scale).2

theorem carry_eq (x : Tokens d) (initial : Row d) (total b : ℕ) (scale : ℝ) :
    carry x initial total scale b = tokenState x initial (cursor total b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [carry, ih, (runBlock_eq _ _ (live_le total b) scale).2, state_shift, next_cursor]

def output (x : Tokens d) (initial : Row d) (total : ℕ) (scale : ℝ) (t : ℕ) : ℝ :=
  let b := t / 16
  (runBlock (suffix x (cursor total b)) (carry x initial total scale b)
    (liveRows total b) scale).1 (t % 16)

theorem forward (x : Tokens d) (initial : Row d) (total : ℕ) (scale : ℝ) :
    (∀ t < total, output x initial total scale t =
      scale * dot (tokenState x initial (t+1)) (x.query t)) ∧
    carry x initial total scale ((total+15)/16) = tokenState x initial total := by
  constructor
  · intro t ht
    have base : cursor total (t/16) = 16*(t/16) := by unfold cursor; omega
    have live : t % 16 < liveRows total (t/16) := by unfold liveRows; rw [base]; omega
    dsimp only [output]
    rw [(runBlock_eq _ _ (live_le total (t/16)) scale).1 _ live, carry_eq, state_shift]
    change _ * dot (tokenState x initial (cursor total (t/16) + (t%16+1)))
      (x.query (cursor total (t/16) + t%16)) = _
    rw [base, show 16*(t/16) + (t%16+1) = t+1 by omega,
      show 16*(t/16) + t%16 = t by omega]
  · rw [carry_eq]
    congr 1
    unfold cursor
    omega

end
end PTX.Kernels.FlashKdaFwd.Math.Sequence
