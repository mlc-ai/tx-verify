-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmAll
public import Kernels.InklingRelDecode.Proof.Interface.SvAlg

@[expose] public section

/-!
# The softmax region's iteration invariant: the specification's numbers of a row

`Sv` ties the softmax region's running state (`Sm.D`) to `Softmax.run` over the row's blocks. This
file fixes the specification's numbers a softmax thread works with and what the entry numbers of
its table mean:

* a thread of half `h` (`Sm.half`) of a tile row sees the 64 keys `64 h + k` of the block of
  iteration `b` (key `128 (s + b · num_splits) + 64 h + k`); `halfScores` is the list of the
  logits (`score + bias / scale`) of the visible ones in column order;
* `EntFull`: the entry numbers (`Sm.Ent`) are the launch's numbers of request `r`, split `s` and
  KV head `kvh` (`Sm.EntMeans` and the fields it leaves out: the scale and `q_len + past`).

No program counter and no register id occurs; the layers above use only the abstract state.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Softmax (St)

noncomputable section
open Classical

/-- The key at column `k` of half `h` of the block of iteration `b` of split `s`. -/
def keyB (Q : Params) (s b h k : Nat) : Nat := 128 * (s + b * Q.splits) + 64 * h + k

/-- The key is visible to the query token (`key ≤ past + token`). -/
def visB (Q : Params) (r s tok b h k : Nat) : Prop := keyB Q s b h k ≤ Q.past r + tok

/-- The logit the kernel forms for a key: `S + bias · (1 / scale)` (`Spec.score`, `Spec.bias`). -/
def logitB (Q : Params) (r s tok head b h k : Nat) : ℝ :=
  score Q r tok head (keyB Q s b h k) + bias Q r tok head (keyB Q s b h k) / Q.scale

/-- The bias of the key at column `k` of half `h` of block `b`. -/
def biasB (Q : Params) (r s tok head b h k : Nat) : ℝ := bias Q r tok head (keyB Q s b h k)

/-- **The visible logits of one half of a row's block**, in column order. -/
def halfScores (Q : Params) (r s tok head b h : Nat) : List ℝ :=
  ((List.range 64).filter fun k => decide (visB Q r s tok b h k)).map
    (logitB Q r s tok head b h)

/-- `scale_log2` of the launch. -/
def slQ (Q : Params) : ℝ := Q.scale * log2eF32

/-- **What the region's entry numbers are**: those of request `r`, split `s` and KV head `kvh`. -/
structure EntFull (Q : Params) (r s kvh : Nat) (e : Ent) : Prop where
  split : e.split = s
  kvh : e.kvh = kvh * 6
  qlen : e.qlen = Q.qLen r
  past : e.past = Q.past r
  nbias : e.nbias = Q.nBias r
  r25 : e.r25 = Q.numIters r s
  splits : e.splits = Q.splits
  sc : e.sc = Q.scale

theorem EntFull.sl {Q : Params} {r s kvh : Nat} {e : Ent} (h : EntFull Q r s kvh e) :
    slOf e = slQ Q := by
  unfold slOf slQ
  rw [h.sc]

theorem EntFull.blk {Q : Params} {r s kvh : Nat} {e : Ent} (h : EntFull Q r s kvh e) (i : Nat) :
    blkOf e i = s + i * Q.splits := by
  unfold blkOf
  rw [h.split, h.splits]

/-- The key of the thread's column `k` in iteration `i`, in the machine's terms. -/
theorem keyB_eq {Q : Params} {r s kvh : Nat} {e : Ent} (h : EntFull Q r s kvh e) (T i k : Nat) :
    keyB Q s i (half T) k = blkOf e i * 128 + half T * 64 + k := by
  unfold keyB
  rw [h.blk]
  omega

/-! ### Lists -/

theorem filterMap_range_eq {α : Type} (p : Nat → Bool) (f : Nat → α) :
    ∀ n, (List.range n).filterMap (fun k => if p k then some (f k) else none) =
      ((List.range n).filter p).map f
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filterMap_append, List.filter_append, List.map_append,
      filterMap_range_eq p f n]
    by_cases hp : p n <;> simp [hp]

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
