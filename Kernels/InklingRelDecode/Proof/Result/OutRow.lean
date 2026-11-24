-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.MmaRun
public import Kernels.InklingRelDecode.Proof.Geometry

@[expose] public section

/-!
# The online softmax of a row is `Spec`'s row sum and numerator (result layer, part 2a)

`Softmax.run` is the kernel's online softmax over a list of blocks (`Softmax.lean`). This file
says which blocks the kernel's CTA `(split, kv_head, request)` feeds it for one output row, in
`Spec`'s terms, and proves that the state after the last block is `Spec`'s row:

* `blocks`: block `b < num_iters` is the key block `split + b · num_splits`; its visible keys
  (`Vis`: `k ≤ past + tok`, `attention.py:780-786`) are the pairs `(logit, value)` with
  `logit = S + bias · (1 / softmax_scale)` (`attention.py:757-778`, PTX
  `fma(bias, inv_scale, s)`) and the value of the key at the output column;
* `flatten_sum`: the keys of all blocks are the keys of `Spec.keys`, once each, so the sums of
  `W` and `W · v` over them are `Spec.rowSum` and `Spec.numerator` (`rowSum_eq`,
  `numerator_eq`), where `W sl s = 2 ^ (sl · s)` with `sl = scale_log2 = softmax_scale ·
  0f3FB8AA3B` is `Spec.weight` (`weight_eq`);
* `row_run`: the running maximum, sum and numerator after the last block are either the initial
  state, for a row with no visible key (`rowSum = 0`, `oPart = 0`), or `o / l = Spec.oPart`,
  `m · sl + log2 l = Spec.lsePart` with `l > 0` and `m` finite (`Softmax.fold_normalized`,
  `fold_lse`);
* `run_ml_congr`: the running maximum and sum do not depend on the values `v`, so the state
  of a row is the one of `blocks0` (all values `0`), which is what the softmax threads' registers
  hold (`l`, `m`) whatever the output column.

Everything is about `Params`; no launch, no thread, no program counter.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Softmax (blockMax step St W)
open Classical

noncomputable section

/-! ### The row's blocks -/

/-- `scale_log2 = softmax_scale · 0f3FB8AA3B` (`attention.py:749-750`, PTX `mul.f32`). -/
def sl (P : Params) : ℝ := P.scale * log2eF32

/-- The key at offset `k` of the `b`-th block of split `s`: `128 (s + b · num_splits) + k`. -/
def key (P : Params) (s b k : Nat) : Nat := 128 * (s + b * P.splits) + k

/-- Key `k` of block `b` is visible to token `tok` of request `r`: `key ≤ past + tok`. -/
def Vis (P : Params) (r s tok b k : Nat) : Prop := key P s b k ≤ P.past r + tok

/-- The logit of a key as the kernel forms it: `S + bias · (1 / softmax_scale)`. -/
def logit (P : Params) (r s tok head b k : Nat) : ℝ :=
  score P r tok head (key P s b k) + bias P r tok head (key P s b k) / P.scale

/-- The value of a key at output column `d`. -/
def val (P : Params) (r s head d b k : Nat) : ℝ := P.vVal r (head / group) (key P s b k) d

/-- The visible keys of block `b`, as `(logit, value)` pairs in key order. -/
def blk (P : Params) (r s tok head : Nat) (vv : Nat → Nat → ℝ) (b : Nat) :
    List (ℝ × ℝ) :=
  blockOf (Vis P r s tok) (logit P r s tok head) vv b

/-- The blocks of one row of split `s`: one per iteration. -/
def blocks (P : Params) (r s tok head : Nat) (vv : Nat → Nat → ℝ) :
    List (List (ℝ × ℝ)) :=
  (List.range (P.numIters r s)).map (blk P r s tok head vv)

/-- The blocks of output column `d`. -/
def blocksD (P : Params) (r s tok head d : Nat) : List (List (ℝ × ℝ)) :=
  blocks P r s tok head (val P r s head d)

/-- The blocks with every value `0`: the scores alone, which decide `m` and `l`. -/
def blocks0 (P : Params) (r s tok head : Nat) : List (List (ℝ × ℝ)) :=
  blocks P r s tok head (fun _ _ => 0)

/-! ### The running maximum and sum do not depend on the values -/

/-- The maximum of a list of scores in the extended reals. -/
def bm (l : List ℝ) : EReal := l.foldr (fun (x : ℝ) (acc : EReal) => max (x : EReal) acc) ⊥

theorem blockMax_eq_bm (blk : List (ℝ × ℝ)) : blockMax blk = bm (blk.map Prod.fst) := by
  unfold blockMax bm
  induction blk with
  | nil => rfl
  | cons a t ih => simp only [List.foldr, List.map_cons, ih]

theorem blockMax_congr {blk blk' : List (ℝ × ℝ)} (h : blk.map Prod.fst = blk'.map Prod.fst) :
    blockMax blk = blockMax blk' := by
  rw [blockMax_eq_bm, blockMax_eq_bm, h]

/-- One step's maximum and sum depend only on the old maximum and sum and on the scores. -/
theorem step_ml_congr (sl : ℝ) {blk blk' : List (ℝ × ℝ)}
    (h : blk.map Prod.fst = blk'.map Prod.fst)
    {st st' : St} (hm : st.m = st'.m) (hl : st.l = st'.l) :
    (step sl blk st).m = (step sl blk' st').m ∧ (step sl blk st).l = (step sl blk' st').l := by
  have hb := blockMax_congr h
  have hp : (blk.map fun q => (2 : ℝ) ^ (sl * q.1 - 0 * sl)) =
      (blk'.map fun q => (2 : ℝ) ^ (sl * q.1 - 0 * sl)) := by
    have := congrArg (List.map fun x : ℝ => (2 : ℝ) ^ (sl * x - 0 * sl)) h
    simpa [List.map_map, Function.comp_def] using this
  have hmu : ∀ mu : ℝ, (blk.map fun q => (2 : ℝ) ^ (sl * q.1 - mu * sl)) =
      (blk'.map fun q => (2 : ℝ) ^ (sl * q.1 - mu * sl)) := by
    intro mu
    have := congrArg (List.map fun x : ℝ => (2 : ℝ) ^ (sl * x - mu * sl)) h
    simpa [List.map_map, Function.comp_def] using this
  constructor
  · unfold step
    simp only [hb, hm]
  · unfold step
    simp only [hb, hm, hl, hmu]

/-- **The running maximum and sum after a list of blocks depend only on the scores.** -/
theorem run_ml_congr (sl : ℝ) {bs bs' : List (List (ℝ × ℝ))}
    (h : bs.map (List.map Prod.fst) = bs'.map (List.map Prod.fst)) :
    (Softmax.run sl bs).m = (Softmax.run sl bs').m ∧
      (Softmax.run sl bs).l = (Softmax.run sl bs').l := by
  unfold Softmax.run
  have key : ∀ (bs bs' : List (List (ℝ × ℝ))) (st st' : St),
      bs.map (List.map Prod.fst) = bs'.map (List.map Prod.fst) → st.m = st'.m → st.l = st'.l →
      (bs.foldl (fun st blk => step sl blk st) st).m =
          (bs'.foldl (fun st blk => step sl blk st) st').m ∧
        (bs.foldl (fun st blk => step sl blk st) st).l =
          (bs'.foldl (fun st blk => step sl blk st) st').l := by
    intro bs
    induction bs with
    | nil =>
      intro bs' st st' h hm hl
      cases bs' with
      | nil => exact ⟨hm, hl⟩
      | cons _ _ => simp at h
    | cons b t ih =>
      intro bs' st st' h hm hl
      cases bs' with
      | nil => simp at h
      | cons b' t' =>
        simp only [List.map_cons, List.cons.injEq] at h
        obtain ⟨hb, ht⟩ := h
        obtain ⟨h1, h2⟩ := step_ml_congr sl hb hm hl
        exact ih t' _ _ ht h1 h2
  exact key bs bs' _ _ h rfl rfl

theorem blk_fst (P : Params) (r s tok head : Nat) (vv vv' : Nat → Nat → ℝ) (b : Nat) :
    (blk P r s tok head vv b).map Prod.fst = (blk P r s tok head vv' b).map Prod.fst := by
  simp [blk, blockOf, List.map_map, Function.comp_def]

theorem blocks_fst (P : Params) (r s tok head : Nat) (vv vv' : Nat → Nat → ℝ) :
    (blocks P r s tok head vv).map (List.map Prod.fst) =
      (blocks P r s tok head vv').map (List.map Prod.fst) := by
  simp only [blocks, List.map_map]
  refine List.map_congr_left fun b _ => ?_
  exact blk_fst P r s tok head vv vv' b

/-- The softmax state of a row after the last block, from the scores alone: the running maximum
and sum the softmax threads hold. -/
def rowState (P : Params) (r s tok head : Nat) : St :=
  Softmax.run (sl P) (blocks0 P r s tok head)

/-- The softmax state of output column `d` of a row after the last block. -/
def colState (P : Params) (r s tok head d : Nat) : St :=
  Softmax.run (sl P) (blocksD P r s tok head d)

/-- **The row's maximum and sum are those of the value-free blocks**, for every column. -/
theorem colState_ml (P : Params) (r s tok head d : Nat) :
    (colState P r s tok head d).m = (rowState P r s tok head).m ∧
      (colState P r s tok head d).l = (rowState P r s tok head).l :=
  run_ml_congr (sl P) (blocks_fst P r s tok head _ _)

/-! ### The keys of the blocks are `Spec.keys` -/

theorem key_div (P : Params) (s b : Nat) {k : Nat} (hk : k < 128) :
    key P s b k / 128 = s + b * P.splits := by
  unfold key
  omega

theorem key_mod (P : Params) (s b : Nat) {k : Nat} (hk : k < 128) : key P s b k % 128 = k := by
  unfold key
  omega

/-- **A key of `Spec.keys` is a visible key of a block of the split, and back.** -/
theorem mem_keys {P : Params} (hsp : 0 < P.splits) {r s tok kk : Nat} :
    kk ∈ keys P r s tok ↔
      ∃ b < P.numIters r s, ∃ k < 128, Vis P r s tok b k ∧ kk = key P s b k := by
  unfold keys
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, hin, hv⟩
    obtain ⟨h1, i, hi, he⟩ := (numIters_spec (P := P) (r := r) (s := s) (k := kk) hsp).1 hin
    refine ⟨i, hi, kk % 128, Nat.mod_lt _ (by norm_num), ?_, ?_⟩
    · unfold Vis key
      omega
    · unfold key
      omega
  · rintro ⟨b, hb, k, hk, hv, rfl⟩
    have hd := key_div P s b hk
    have hin' : P.inSplit r s (key P s b k) :=
      (numIters_spec (P := P) (r := r) (s := s) (k := key P s b k) hsp).2
        ⟨by omega, b, hb, hd⟩
    have h3 := hin'.2.2
    exact ⟨by omega, hin', hv⟩

theorem sum_filter_range (p : Nat → Prop) [DecidablePred p] (f : Nat → ℝ) (n : Nat) :
    (((List.range n).filter fun k => decide (p k)).map f).sum =
      ∑ k ∈ Finset.range n, if p k then f k else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    by_cases hp : p n <;> simp [hp]

theorem sum_range_map (F : Nat → ℝ) (n : Nat) :
    ((List.range n).map F).sum = ∑ b ∈ Finset.range n, F b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- **The sum of a function of the key over the keys of the blocks** (block by block, in order)
is its sum over `Spec.keys`. -/
theorem sum_keys {P : Params} (hsp : 0 < P.splits) (r s tok : Nat) (h : Nat → ℝ) :
    ((List.range (P.numIters r s)).flatMap fun b =>
        ((List.range 128).filter fun k => decide (Vis P r s tok b k)).map
          fun k => h (key P s b k)).sum = ∑ kk ∈ keys P r s tok, h kk := by
  have hflat : ((List.range (P.numIters r s)).flatMap fun b =>
        ((List.range 128).filter fun k => decide (Vis P r s tok b k)).map
          fun k => h (key P s b k)) =
      ((List.range (P.numIters r s)).map fun b =>
        (((List.range 128).filter fun k => decide (Vis P r s tok b k)).map
          fun k => h (key P s b k))).flatten := by
    rw [List.flatMap_def]
  rw [hflat, List.sum_flatten, List.map_map]
  have e1 : ((List.range (P.numIters r s)).map ((fun l => l.sum) ∘ fun b =>
      ((List.range 128).filter fun k => decide (Vis P r s tok b k)).map
        fun k => h (key P s b k))).sum =
      ∑ b ∈ Finset.range (P.numIters r s), ∑ k ∈ Finset.range 128,
        if Vis P r s tok b k then h (key P s b k) else 0 := by
    rw [sum_range_map]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact sum_filter_range (Vis P r s tok b) (fun k => h (key P s b k)) 128
  rw [e1, ← Finset.sum_product'
    (f := fun b k => if Vis P r s tok b k then h (key P s b k) else 0), ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun p => key P s p.1 p.2)
    (fun kk => ((kk / 128 - s) / P.splits, kk % 128)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    exact (mem_keys hsp).2 ⟨p.1, hp.1.1, p.2, hp.1.2, hp.2, rfl⟩
  · intro kk hk
    obtain ⟨b, hb, k, hk', hv, rfl⟩ := (mem_keys hsp).1 hk
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, key_div P s b hk',
      key_mod P s b hk']
    rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hsp]
    exact ⟨⟨hb, hk'⟩, hv⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp only [key_div P s p.1 hp.1.2, key_mod P s p.1 hp.1.2, Nat.add_sub_cancel_left,
      Nat.mul_div_cancel _ hsp]
  · intro kk hk
    obtain ⟨b, hb, k, hk', hv, rfl⟩ := (mem_keys hsp).1 hk
    simp only [key_div P s b hk', key_mod P s b hk', Nat.add_sub_cancel_left,
      Nat.mul_div_cancel _ hsp]
  · intro p hp
    simp only [Finset.mem_filter] at hp
    simp

/-! ### The sums of the blocks are the row sum and the numerator -/

/-- `Spec.weight` is `W` of the logit: `2 ^ (c (scale S + bias)) = 2 ^ (sl (S + bias / scale))`. -/
theorem weight_eq (P : Params) (hs : 0 < P.scale) (r tok head kk : Nat) :
    weight P r tok head kk =
      W (sl P) (score P r tok head kk + bias P r tok head kk / P.scale) := by
  unfold weight W sl
  congr 1
  field_simp

/-- A function of the pairs of the blocks, summed over the flattened blocks, is the sum over the
keys of the blocks. -/
theorem flatten_map_eq (P : Params) (r s tok head : Nat) (vv : Nat → Nat → ℝ)
    (F : ℝ × ℝ → ℝ) :
    ((blocks P r s tok head vv).flatten.map F) =
      (List.range (P.numIters r s)).flatMap fun b =>
        ((List.range 128).filter fun k => decide (Vis P r s tok b k)).map
          fun k => F (logit P r s tok head b k, vv b k) := by
  simp only [blocks, blk, blockOf, List.map_flatten, List.map_map, List.flatMap_def,
    Function.comp_def]

/-- **The sum of `W` over the visible logits of the blocks is `Spec.rowSum`.** -/
theorem rowSum_eq (P : Params) (hs : 0 < P.scale) (hsp : 0 < P.splits) (r s tok head : Nat)
    (vv : Nat → Nat → ℝ) :
    rowSum P r s tok head =
      ((blocks P r s tok head vv).flatten.map fun q => W (sl P) q.1).sum := by
  rw [flatten_map_eq]
  simp only [logit]
  rw [sum_keys hsp r s tok (fun kk => W (sl P) (score P r tok head kk +
    bias P r tok head kk / P.scale))]
  unfold rowSum
  refine Finset.sum_congr rfl fun kk _ => ?_
  exact weight_eq P hs r tok head kk

/-- **The sum of `W · v` over the visible keys of the blocks of column `d` is `Spec.numerator`.**
-/
theorem numerator_eq (P : Params) (hs : 0 < P.scale) (hsp : 0 < P.splits)
    (r s tok head d : Nat) :
    numerator P r s tok head d =
      ((blocksD P r s tok head d).flatten.map fun q => W (sl P) q.1 * q.2).sum := by
  unfold blocksD
  rw [flatten_map_eq]
  simp only [logit, val]
  rw [sum_keys hsp r s tok (fun kk => W (sl P) (score P r tok head kk +
    bias P r tok head kk / P.scale) * P.vVal r (head / group) kk d)]
  unfold numerator
  refine Finset.sum_congr rfl fun kk _ => ?_
  rw [weight_eq P hs r tok head kk]

/-! ### The state after the last block -/

theorem sl_pos {P : Params} (hs : 0 < P.scale) : 0 < sl P := by
  unfold sl
  have : 0 < log2eF32 := by unfold log2eF32; norm_num
  positivity

/-- The blocks have a visible key exactly when the row sum is not zero. -/
theorem flatten_eq_nil_iff {P : Params} (hs : 0 < P.scale) (hsp : 0 < P.splits)
    (r s tok head : Nat) (vv : Nat → Nat → ℝ) :
    (blocks P r s tok head vv).flatten = [] ↔ rowSum P r s tok head = 0 := by
  rw [rowSum_eq P hs hsp r s tok head vv]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    by_contra hne
    exact (Softmax.sumW_pos (sl P) hne).ne' h

/-- **A row with no visible key**: the state is the initial one (`l = 0`, `m = -inf`, `o = 0`),
and `Spec.oPart` is `0`. -/
theorem row_empty {P : Params} (hs : 0 < P.scale) (hsp : 0 < P.splits) (r s tok head d : Nat)
    (h : rowSum P r s tok head = 0) :
    (rowState P r s tok head).l = 0 ∧ (rowState P r s tok head).m = ⊥ ∧
      (colState P r s tok head d).o = 0 ∧ oPart P r s tok head d = 0 := by
  have h0 := Softmax.fold_empty (sl P) (sl_pos hs) (blocks0 P r s tok head)
    ((flatten_eq_nil_iff hs hsp r s tok head (fun _ _ => 0)).2 h)
  have hd := Softmax.fold_empty (sl P) (sl_pos hs) (blocksD P r s tok head d)
    ((flatten_eq_nil_iff hs hsp r s tok head (val P r s head d)).2 h)
  exact ⟨h0.1, h0.2.2, hd.2.1, by simp [oPart, h]⟩

/-- **A row with a visible key**: the row sum is positive and the maximum finite; the normalized
output is `Spec.oPart` and the log-sum-exp is `Spec.lsePart`. -/
theorem row_nonempty {P : Params} (hs : 0 < P.scale) (hsp : 0 < P.splits)
    (r s tok head d : Nat) (h : rowSum P r s tok head ≠ 0) :
    0 < (rowState P r s tok head).l ∧ (∃ M : ℝ, (rowState P r s tok head).m = (M : EReal)) ∧
      (colState P r s tok head d).o / (rowState P r s tok head).l = oPart P r s tok head d ∧
      (rowState P r s tok head).m.toReal * sl P + Real.logb 2 (rowState P r s tok head).l =
        lsePart P r s tok head := by
  have hne : ∀ vv, (blocks P r s tok head vv).flatten ≠ [] := fun vv hnil =>
    h ((flatten_eq_nil_iff hs hsp r s tok head vv).1 hnil)
  obtain ⟨M, hM, -, -, -⟩ := Softmax.fold_invariant (sl P) (sl_pos hs) (blocks0 P r s tok head)
    (hne fun _ _ => 0)
  obtain ⟨hn, -⟩ := Softmax.fold_normalized (sl P) (sl_pos hs) (blocksD P r s tok head d)
    (hne (val P r s head d))
  obtain ⟨-, hl0⟩ := Softmax.fold_normalized (sl P) (sl_pos hs) (blocks0 P r s tok head)
    (hne fun _ _ => 0)
  have hlse := Softmax.fold_lse (sl P) (sl_pos hs) (blocks0 P r s tok head) (hne fun _ _ => 0)
  have hml := (colState_ml P r s tok head d).2
  refine ⟨hl0, ⟨M, hM⟩, ?_, ?_⟩
  · have hn' : (colState P r s tok head d).o / (colState P r s tok head d).l =
        numerator P r s tok head d / rowSum P r s tok head := by
      rw [numerator_eq P hs hsp r s tok head d, rowSum_eq P hs hsp r s tok head (val P r s head d)]
      exact hn
    rw [← hml, hn']
    simp [oPart, h]
  · have hl' : rowSum P r s tok head = ((blocks0 P r s tok head).flatten.map
        fun q => W (sl P) q.1).sum := rowSum_eq P hs hsp r s tok head (fun _ _ => 0)
    unfold lsePart
    rw [hl']
    exact hlse

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Out
