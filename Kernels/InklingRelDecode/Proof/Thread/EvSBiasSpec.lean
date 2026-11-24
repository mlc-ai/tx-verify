-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvSBias
public import Kernels.InklingRelDecode.Proof.Thread.SmMask
public import Kernels.InklingRelDecode.Proof.Geometry

@[expose] public section

/-!
# The bias loads in the specification's terms

`EvSBias` says a bias load reads two bytes at `biasAddr e T n j`, the register arithmetic of the
code. This file says which element of `Rel` that is.

**What the entry numbers mean.** `EntMeans P r s kvh e` collects the documented fields of
`SmEntry.entOf` (the prologue's tie, `ProBSpec.exit_spec`, `entOf_params`): for the request `r`,
the split `s` (`ctaid.x`) and the KV head `kvh` (`ctaid.y`),

* `split = s`, `kvh = 6 · kvh`, `qs = cu_seqlens_q[r]`, `qlen = q_len`, `nbias = n_bias`;
* `r24 = ⌈seqlen_k / 128⌉ · 128` and `r25 = num_iters` of the split, `splits = num_splits`;
* `strRel` and `rel` are the words of the `stride_rel_t` and `Rel` parameters (`entOf_params`).

**The address.** For a thread `T` of the default partition with a valid row, the load of word `j`
of block `n` reads the `Rel` element

`relAddr P r tok head c = relBase + 2 (token · stride_rel + head · 1280 + c)`,

with `tok = tokOf T` (the thread's query token of the request), `head = 6 kvh + remOf T`, and
`c = relCol P r k` for the key `k = 128 n + 64 · half T + j` (`biasAddr_spec`). This is the second
clause of `Params.reads`, and `Params.bias` of that key is `P.rel` at the same element
(`bias_eq_rel`). `shape_pre_spec` and `shape_nxt_spec` state it for the events: a preload reads
the keys of the split's first block `s`, a loop load those of the block `s + (i + 1) · splits`.

**What the machine's state does not pin.** The column `c` is `relCol` of the key only because the
block is below `blocks` and at or after `n_bias`; the machine knows these through `act0`/`actB`
(`Inv.cwPre`/`cwNxt`) and `EntMeans.r25`, which gives `block < blocks`. The event's value (which
`bf16` number is in the memory at the address) is the memory model's, not the shape's
(`Pre.relInput`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

/-- The byte address of element `c` of the relative-logit row of token `tok` and head `head` of
request `r` (the second clause of `Params.reads`, byte 0). -/
def relAddr (P : Params) (r tok head c : Nat) : Nat :=
  P.relBase + 2 * ((P.qStart r + tok) * P.strideRel + head * relPad + c)

/-- The documented fields of `SmEntry.entOf` for request `r`, split `s` and KV head `kvh`. -/
structure EntMeans (P : Params) (r s kvh : Nat) (e : Ent) : Prop where
  split : e.split = s
  kvh : e.kvh = kvh * 6
  qs : e.qs = P.qStart r
  qlen : e.qlen = P.qLen r
  nbias : e.nbias = P.nBias r
  r24 : e.r24 = P.blocks r * 128
  r25 : e.r25 = P.numIters r s
  splits : e.splits = P.splits
  strRel : e.strRel = P.strideRel % 2 ^ 32
  rel : e.rel = P.relBase % 2 ^ 64

/-! ### Arithmetic of the pointer -/

theorem biasAddr_eq (e : Ent) (T n j : Nat) (hq : e.qs + tokOf T < 2 ^ 31)
    (hs : e.strRel < 2 ^ 31) (hh : e.kvh + remOf T < 2 ^ 20) (h24 : e.r24 < 2 ^ 31)
    (hn : n * 128 < 2 ^ 31) (hc : e.r24 ≤ n * 128 + half T * 64 + j + 1280) :
    biasAddr e T n j = (e.rel + 2 * ((e.qs + tokOf T) * e.strRel + (e.kvh + remOf T) * 1280 +
      (n * 128 + half T * 64 + j + 1280 - e.r24))) % 2 ^ 64 := by
  have hq' : (e.qs + tokOf T) % 2 ^ 32 = e.qs + tokOf T := Nat.mod_eq_of_lt (by omega)
  have hp : (e.qs + tokOf T) * e.strRel < 2 ^ 62 := by
    calc (e.qs + tokOf T) * e.strRel < 2 ^ 31 * 2 ^ 31 := Nat.mul_lt_mul'' hq hs
      _ = 2 ^ 62 := by norm_num
  have e258 : p258 e T = (e.qs + tokOf T) * e.strRel := by
    unfold p258
    rw [hq', sxw_small hq, sxw_small hs]
    exact Nat.mod_eq_of_lt (by omega)
  have ek : sxw (key n) = n * 128 := by
    unfold key
    rw [Nat.mod_eq_of_lt (by omega)]
    exact sxw_small hn
  have e345 : r345 e T = (e.kvh + remOf T) * 1280 := by
    unfold r345
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have e24 : e.r24 % 2 ^ 32 = e.r24 := Nat.mod_eq_of_lt (by omega)
  unfold biasAddr ptrAt p9 p262 p261 p260 p259
  rw [e258, ek, e345]
  unfold r346
  rw [e24]
  by_cases h1 : e.r24 ≤ 1280
  · have : (1280 + 2 ^ 32 - e.r24) % 2 ^ 32 = 1280 - e.r24 := by omega
    rw [this, sxw_small (by omega)]
    simp only [Nat.add_mod_mod, Nat.mod_add_mod]
    congr 1
    omega
  · obtain ⟨X, hX⟩ : ∃ X, X + e.r24 = 2 ^ 32 + 1280 := ⟨2 ^ 32 + 1280 - e.r24, by omega⟩
    have : (1280 + 2 ^ 32 - e.r24) % 2 ^ 32 = X := by omega
    rw [this]
    simp only [Nat.add_mod_mod, Nat.mod_add_mod]
    have hXs : sxw X = X + (2 ^ 64 - 2 ^ 32) := by
      unfold sxw
      omega
    rw [hXs]
    omega

/-- Block `s + i · splits` of the split is a block of the request for `i < num_iters`. -/
theorem lt_blocks_of_iters {P : Params} {r s i : Nat} (hsp : 0 < P.splits)
    (hi : i < P.numIters r s) : s + i * P.splits < P.blocks r := by
  unfold Params.numIters at hi
  have h := (Nat.le_div_iff_mul_le hsp).1 (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at h
  omega

variable {P : Params} {L : Launch} {mem0 : Mem0} {en : Ent} {r s kvh : Nat}

/-- **The address of a bias load in the specification's terms.** Premises: the launch's `Pre`, the
request and KV head of the thread's CTA, the entry numbers' meaning, a thread index below 128 with
a valid row, and a block `n` of the request at or after `n_bias`. The load of word `j` of the
thread's half row reads the `Rel` element `relAddr` of the thread's token and head at the column
`relCol` of the key `128 n + 64 · half + j`, all inside the row; the address does not wrap. -/
theorem biasAddr_spec (hpre : Pre P L mem0) (hm : EntMeans P r s kvh en) (hr : r < P.b)
    (hkvh : kvh < kvHeads) {T : Nat} (_hT : T < 128) (hrv : rowValid en T = true) {n j : Nat}
    (hj : j < 64) (hn : n < P.blocks r) (hnb : P.nBias r ≤ n) :
    tokOf T < P.qLen r ∧ kvh * 6 + remOf T < heads ∧
      (relCol P r (n * 128 + half T * 64 + j)).toNat < relPad ∧
      biasAddr en T n j = relAddr P r (tokOf T) (kvh * 6 + remOf T)
        (relCol P r (n * 128 + half T * 64 + j)).toNat := by
  have hrv' : row T < 60 ∧ tokOf T < en.qlen := by simpa [rowValid] using hrv
  have htok : tokOf T < P.qLen r := by rw [← hm.qlen]; exact hrv'.2
  have hrem := remOf_lt T
  have hkv2 : kvh < 2 := hkvh
  have hhalf : half T < 2 := by unfold half; omega
  have hLe := blocks_le_nBias (hpre.qLenLe r hr) (hpre.qLenSeq r hr)
  have hseq := hpre.seqRange r hr
  have hbl : P.blocks r * 128 < 2 ^ 31 := by unfold Params.blocks; omega
  have htokn := token_lt hpre hr htok
  have hnT := hpre.nTokRange
  have hstr := hpre.scalarsRange.2.1
  have hk : n * 128 + half T * 64 + j < P.blocks r * 128 := by omega
  have hk2 : P.nBias r * 128 ≤ n * 128 + half T * 64 + j := by omega
  obtain ⟨h0, h1⟩ := relCol_range hpre hr hk hk2
  have hcn : (relCol P r (n * 128 + half T * 64 + j)).toNat =
      n * 128 + half T * 64 + j + 1280 - P.blocks r * 128 := by
    unfold relCol relPad at h0 h1 ⊢
    omega
  have hheads : kvh * 6 + remOf T < heads := by unfold heads; omega
  have hcr : (relCol P r (n * 128 + half T * 64 + j)).toNat < relPad := by
    unfold relPad at *
    omega
  refine ⟨htok, hheads, hcr, ?_⟩
  have h := biasAddr_eq en T n j (by rw [hm.qs]; omega) (by rw [hm.strRel]; omega)
    (by rw [hm.kvh]; omega) (by rw [hm.r24]; exact hbl) (by omega)
    (by rw [hm.r24]; omega)
  rw [h, hm.qs, hm.strRel, hm.rel, hm.kvh, hm.r24, hcn]
  have hread : P.reads (relAddr P r (tokOf T) (kvh * 6 + remOf T)
      (relCol P r (n * 128 + half T * 64 + j)).toNat) :=
    Or.inr (Or.inl ⟨r, hr, tokOf T, htok, kvh * 6 + remOf T, hheads, _, hcr, 0, by omega,
      by unfold relAddr; omega⟩)
  have hlt := hpre.readsRange _ hread
  unfold relAddr at hlt ⊢
  rw [hcn] at hlt
  have hs32 : P.strideRel % 2 ^ 32 = P.strideRel := Nat.mod_eq_of_lt (by omega)
  rw [hs32]
  simp only [relPad] at hlt ⊢
  omega

/-- The bias of the key is the `Rel` element at that address: `n ≥ n_bias`. -/
theorem bias_eq_rel {k tok head : Nat} (h : P.nBias r * 128 ≤ k) :
    bias P r tok head k = P.rel (P.qStart r + tok) head (relCol P r k).toNat := by
  unfold bias
  simp [h]

variable {g : Nat} {d : D} {e : Event} {u : TState}

/-- The entry numbers' meaning, for the state `d` of thread `g`, determines the request, split and
KV head the thread's table is for. -/
theorem pre_block (hm : EntMeans P r s kvh d.e) (hi : Inv L g d) {j : Fin 64}
    (hs : d.site = .pre j) :
    d.n = s ∧ rowValid d.e (g % L.block) = true ∧ 0 < P.numIters r s ∧
      P.nBias r ≤ s := by
  obtain ⟨-, hact⟩ := hi.cwPre j hs
  obtain ⟨hi0, -⟩ := hi.loop.1 j hs
  simp only [act0, Bool.and_eq_true, decide_eq_true_eq] at hact
  obtain ⟨⟨⟨h1, -⟩, hrv⟩, h3⟩ := hact
  refine ⟨?_, hrv, by rw [← hm.r25]; exact h1, by rw [← hm.nbias, ← hm.split]; exact h3⟩
  simp only [D.n, blkOf, hi0, hm.split, Nat.zero_mul, Nat.add_zero]

theorem nxt_block (hm : EntMeans P r s kvh d.e) (hi : Inv L g d) {j : Fin 64}
    (hs : d.site = .nxt j) :
    d.n + d.e.splits = s + (d.i + 1) * P.splits ∧ rowValid d.e (g % L.block) = true ∧
      d.i + 1 < P.numIters r s ∧ P.nBias r ≤ s + (d.i + 1) * P.splits := by
  obtain ⟨-, -, hact, -⟩ := hi.cwNxt j hs
  simp only [actB, Bool.and_eq_true, decide_eq_true_eq] at hact
  obtain ⟨⟨hrv, h2, -⟩, h3⟩ := hact
  have hn : d.n + d.e.splits = s + (d.i + 1) * P.splits := by
    simp only [D.n, blkOf, hm.split, hm.splits]
    ring
  refine ⟨hn, hrv, by rw [← hm.r25]; exact h2, ?_⟩
  rw [← hn, ← hm.nbias]
  simp only [D.n, blkOf] at h3 ⊢
  omega

/-- **A preload, in the specification's terms** (`hm`: the numbers of the thread's table are the
launch's; `hr`, `hkvh`: its request and KV head are in range). The load reads two bytes at the
`Rel` element of the thread's token and head at the column of the key `128 s + 64 · half + j`,
where `s` is the split: the first block of the split. -/
theorem shape_pre_spec (hpre : Pre P L mem0) (hm : EntMeans P r s kvh d.e) (hr : r < P.b)
    (hkvh : kvh < kvHeads) {j : Fin 64} (hF : Fired L g d e (some u)) (hs : d.site = .pre j) :
    ∃ bs : List (Option Byte), bs.length = 2 ∧
      e = ⟨evPc d.site, .rd (globalAcc (relAddr P r (tokOf (g % L.block))
        (kvh * 6 + remOf (g % L.block))
        (relCol P r (s * 128 + half (g % L.block) * 64 + j.val)).toNat) 2) bs⟩ := by
  obtain ⟨bs, hl, he⟩ := shape_pre hF hs
  obtain ⟨t, -, hi, -⟩ := hF
  obtain ⟨hn, hrv, hit, hnb⟩ := pre_block hm hi hs
  have hbl : s < P.blocks r := by
    have := lt_blocks_of_iters (r := r) (s := s) (i := 0) hpre.splitsPos hit
    simpa using this
  obtain ⟨-, -, -, hadr⟩ := biasAddr_spec hpre hm hr hkvh hi.tid hrv j.isLt hbl hnb
  exact ⟨bs, hl, by rw [he, hn, hadr]⟩

/-- **A loop load, in the specification's terms**: the same for the key
`128 (s + (i + 1) · num_splits) + 64 · half + j`, the next block of the split. -/
theorem shape_nxt_spec (hpre : Pre P L mem0) (hm : EntMeans P r s kvh d.e) (hr : r < P.b)
    (hkvh : kvh < kvHeads) {j : Fin 64} (hF : Fired L g d e (some u)) (hs : d.site = .nxt j) :
    ∃ bs : List (Option Byte), bs.length = 2 ∧
      e = ⟨evPc d.site, .rd (globalAcc (relAddr P r (tokOf (g % L.block))
        (kvh * 6 + remOf (g % L.block))
        (relCol P r ((s + (d.i + 1) * P.splits) * 128 + half (g % L.block) * 64 + j.val)).toNat)
        2) bs⟩ := by
  obtain ⟨bs, hl, he⟩ := shape_nxt hF hs
  obtain ⟨t, -, hi, -⟩ := hF
  obtain ⟨hn, hrv, hit, hnb⟩ := nxt_block hm hi hs
  have hbl := lt_blocks_of_iters hpre.splitsPos hit
  obtain ⟨-, -, -, hadr⟩ := biasAddr_spec hpre hm hr hkvh hi.tid hrv j.isLt hbl hnb
  exact ⟨bs, hl, by rw [he, hn, hadr]⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
