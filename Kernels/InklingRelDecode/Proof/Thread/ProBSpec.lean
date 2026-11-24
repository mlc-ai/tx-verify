-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProBClosed
public import Kernels.InklingRelDecode.Proof.Geometry
public import Lemmas.Cluster.Unit

@[expose] public section

/-! # The prologue's exit registers are the specification's quantities

`ProBClosed` gives each exit register as a closed `Nat` expression of the loaded words
`cu_seqlens_q[req]`, `cu_seqlens_q[req + 1]`, `seq_lens[req]`, `num_splits` and `ctaid.x`. This
file ties those to `Spec`.

* The CTA of a thread: in the kernel's launch (`Pre.gridShape`, `clusterPlaces`: one CTA per
  cluster, the grid's clusters numbered with the last coordinate fastest, `ClusterPlace.uniform`)
  the CTA `c = g / block` has `ctaid = (c / (2 b), c / b % 2, c % b)`: `ctaid.x` is the split,
  `ctaid.y` the KV head and `ctaid.z` the request. All three are below the grid extents.
* `WordsMatch`: the three loaded words are `P.qStart r`, `P.qStart (r + 1)` and `P.seqK r` of the
  request `r = ctaid.z`; the protocol layer supplies it from `Pre.cuInput` and `Pre.seqInput`.
* `wordsOk_of_pre`: the numeric facts the machine needs of the words (`WordsOk`) follow from `Pre`:
  `cu0 ≤ cu1 < 2 ^ 31` (`cuMono`, `cuEnd`, `nTokRange`), `cu1 - cu0 ≤ seq_lens` (`qLenSeq`),
  `seq_lens + 255 < 2 ^ 31` (`seqRange`), and the numerators of the two signed divisions are below
  `2 ^ 31`: both are `num_splits - 1 - split` plus a block count below `2 ^ 24`, and
  `splitsRange : splits + 2 ^ 24 < 2 ^ 31`.
* `argsOk_of_pre`: the thread's inherited registers satisfy `ArgsOk` when they hold the launch's
  parameters.
* The exit registers: `r22 = nBias`, `r23 = past / 128` (`fa_mask_right`), `r21 = past`
  (`pos0`), `r20 = qLen`, `r24 = blocks * 128` (`rel_base` is this minus `REL_PAD`: `relCol`),
  `r25 = r26 = numIters r split`, `r32 = num_pre = min (min num_old num_iters) 3`. `num_old` is
  `max (cdiv (past // 128 - split) num_splits) 0` (`attention.py:967`), defined here as `numOld`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The `%ctaid` of CTA `c` of the kernel's launch: the grid `(num_splits, 2, b)` of one-CTA
clusters, numbered with the last coordinate fastest (`ClusterPlace.uniform`). -/
theorem ctaid_eq (hpre : Pre P L mem0) {c : Nat} (hc : c < L.grid) :
    L.ctaidOf c = ⟨c / (kvHeads * P.b), c / P.b % kvHeads, c % P.b⟩ := by
  have hs : ∀ k, (L.clusterPlaces k).shape = ⟨1, 1, 1⟩ := by
    intro k
    rw [hpre.clusterPlaces, hpre.clusterNctaid]
    rfl
  have hcn : c < L.nclusters := by rw [hpre.nclusters]; exact hc
  have h1 := Launch.clusterOfCta_unit hs hcn
  have h2 := Launch.rankOfCta_unit hs hcn
  simp only [Launch.ctaidOf, Launch.placeOf, Launch.clusterCtaidOf, h1, h2, hpre.clusterPlaces,
    hpre.clusterNctaid, hpre.gridShape, ClusterPlace.uniform, Dim3.coord]
  simp

/-- The CTA of a thread of the launch is in the grid. -/
theorem grid_lt {g : Nat} (hg : g < L.threads) : g / L.block < L.grid := by
  rw [Launch.threads] at hg
  exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)

/-- The CTA coordinates of a thread: `ctaid.x` is its split, `ctaid.y` its KV head and `ctaid.z`
its request. -/
theorem cta_coords (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) :
    cta L g .x = g / L.block / (kvHeads * P.b) ∧ cta L g .y = g / L.block / P.b % kvHeads ∧
      cta L g .z = g / L.block % P.b := by
  have := ctaid_eq hpre (grid_lt hg)
  simp only [cta, this, Dim3.get, and_self]

/-- The coordinates are below the grid's extents. -/
theorem cta_lt (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) :
    cta L g .x < P.splits ∧ cta L g .y < kvHeads ∧ cta L g .z < P.b := by
  obtain ⟨hx, hy, hz⟩ := cta_coords hpre hg
  have hgr := grid_lt hg
  rw [hpre.grid] at hgr
  have hb := hpre.bPos
  refine ⟨?_, ?_, ?_⟩
  · rw [hx]
    refine Nat.div_lt_of_lt_mul ?_
    rw [Nat.mul_comm (kvHeads * P.b)]
    have : P.splits * kvHeads * P.b = P.splits * (kvHeads * P.b) := Nat.mul_assoc _ _ _
    omega
  · rw [hy]; exact Nat.mod_lt _ (by decide)
  · rw [hz]; exact Nat.mod_lt _ hb

/-! ### The loaded words are the request's -/

/-- The three loaded words are the request's `cu_seqlens_q[r]`, `cu_seqlens_q[r + 1]` and
`seq_lens[r]` (the protocol layer supplies it from `Pre.cuInput` and `Pre.seqInput`). -/
structure WordsMatch (P : Params) (r : Nat) (dt : Dat) : Prop where
  cu0 : dt.cu0 = P.qStart r
  cu1 : dt.cu1 = P.qStart (r + 1)
  sk : dt.sk = P.seqK r

theorem bnd_of_pre (hpre : Pre P L mem0) {r : Nat} (hr : r < P.b) {dt : Dat}
    (hm : WordsMatch P r dt) : Bnd dt := by
  have h1 := hpre.cuMono r hr
  have h2 := hpre.qLenSeq r hr
  have h3 := hpre.seqRange r hr
  have h4 := qStart_mono hpre (r := r + 1) (r' := P.b) (by omega) (Nat.le_refl _)
  have h5 := hpre.cuEnd
  have h6 := hpre.nTokRange
  unfold Params.qLen at h2
  obtain ⟨c0, c1, c2⟩ := hm
  unfold Bnd
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **The numerators of the two signed divisions are non-negative 32-bit words.** The loaded words
of a request of the launch satisfy `WordsOk`. -/
theorem wordsOk_of_pre (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) {dt : Dat}
    (ha : ArgsOk L g dt.pro) (hs : dt.pro.w71 = P.splits)
    (hm : WordsMatch P (cta L g .z) dt) : WordsOk L g dt := by
  have hr := (cta_lt hpre hg).2.2
  have hb := bnd_of_pre hpre hr hm
  have hsr := hpre.splitsRange
  have h2 := ha.splitIdx
  have hp : pastN dt < 2 ^ 31 := by unfold pastN; omega
  refine ⟨hb, ?_, ?_⟩
  · rw [r176_eq L g dt ha hb]
    refine (nonneg_s32 _ (by omega)).2 (by omega)
  · rw [r217_eq L g dt ha hb]
    refine (nonneg_s32 _ (by omega)).2 (by omega)

/-- The inherited registers of a thread of the default partition hold the launch's parameters:
`ArgsOk`. The words `x0 … x25` are the parameter words (`Pre.paramQ` …), `w71` is
`num_splits`. -/
theorem argsOk_of_pre (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) {inh : Inh}
    (htid : tidOf L g < 128) (hs : inh.w71 = P.splits)
    (h0 : inh.x0 = BitVec.ofNat 64 P.qBase) (h6 : inh.x6 = BitVec.ofNat 64 P.relBase)
    (h8 : inh.x8 = BitVec.ofNat 64 P.seqBase) (h9 : inh.x9 = BitVec.ofNat 64 P.cuBase)
    (h10 : inh.x10 = BitVec.ofNat 64 P.oBase) (h11 : inh.x11 = BitVec.ofNat 64 P.lseBase)
    (h15 : ∀ w, L.params (param "15") = some w → inh.x15 = w)
    (h16 : inh.x16 = BitVec.ofNat 64 P.strideQ) (h17 : inh.x17 = BitVec.ofNat 64 P.strideRel)
    (h25 : inh.x25 = BitVec.ofNat 64 P.nTok) : ArgsOk L g inh where
  tid := htid
  splitsPos := by rw [hs]; exact hpre.splitsPos
  splitsRange := by have := hpre.splitsRange; omega
  splitIdx := by rw [hs]; exact (cta_lt hpre hg).1
  p0 := by rw [h0]; exact hpre.paramQ
  p6 := by rw [h6]; exact hpre.paramRel
  p8 := by rw [h8]; exact hpre.paramSeq
  p9 := by rw [h9]; exact hpre.paramCu
  p10 := by rw [h10]; exact hpre.paramO
  p11 := by rw [h11]; exact hpre.paramLse
  p15 := by
    obtain ⟨bits, -, hp, -⟩ := hpre.paramScale
    rw [hp, h15 _ hp]
  p16 := by rw [h16]; exact hpre.paramStrideQ
  p17 := by rw [h17]; exact hpre.paramStrideRel
  p25 := by rw [h25]; exact hpre.paramNTok

/-! ### The registers are `Spec`'s quantities -/

/-- `num_old = max (cdiv (past // 128 - n_first) num_splits) 0` with `n_first = split`
(`attention.py:967`), as a natural number. -/
def numOld (P : Params) (r s : Nat) : Nat := (P.past r / 128 - s + (P.splits - 1)) / P.splits

/-- `num_pre = min (min num_old num_iters) STAGES` with `STAGES = 3` (`attention.py:968`). -/
def numPre (P : Params) (r s : Nat) : Nat := min (min (numOld P r s) (P.numIters r s)) 3

/-- The ceiling quotient written with the kernel's numerator `num_splits - 1 - split + b` equals
the one written with the truncated difference `b - split + (num_splits - 1)`, for a split below
`num_splits`. -/
theorem cdiv_numer (n s b : Nat) (hs : s < n) :
    (n - 1 - s + b) / n = (b - s + (n - 1)) / n := by
  by_cases h : s ≤ b
  · exact congrArg (· / n) (by omega)
  · rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]

theorem pastN_eq {r : Nat} {dt : Dat} (hm : WordsMatch P r dt) : pastN dt = P.past r := by
  simp [pastN, Params.past, Params.qLen, hm.cu0, hm.cu1, hm.sk]

theorem blocksN_eq {r : Nat} {dt : Dat} (hm : WordsMatch P r dt) :
    (dt.sk + 127) / 128 = P.blocks r := by
  simp [Params.blocks, hm.sk]

theorem itersN_eq {g : Nat} {dt : Dat} (hs : dt.pro.w71 = P.splits) (hx : cta L g .x < P.splits)
    (hm : WordsMatch P (cta L g .z) dt) :
    itersN L g dt = P.numIters (cta L g .z) (cta L g .x) := by
  unfold itersN Params.numIters
  rw [blocksN_eq hm, hs]
  exact cdiv_numer _ _ _ hx

theorem oldN_eq {g : Nat} {dt : Dat} (hs : dt.pro.w71 = P.splits) (hx : cta L g .x < P.splits)
    (hm : WordsMatch P (cta L g .z) dt) :
    oldN L g dt = numOld P (cta L g .z) (cta L g .x) := by
  unfold oldN numOld
  rw [pastN_eq hm, hs]
  exact cdiv_numer _ _ _ hx

/-- The prologue's exit registers, as `Spec`'s quantities of the request `r = ctaid.z` and the
split `s = ctaid.x` of the thread. -/
theorem exit_spec (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) {dt : Dat}
    (ha : ArgsOk L g dt.pro) (hs : dt.pro.w71 = P.splits)
    (hm : WordsMatch P (cta L g .z) dt) :
    v_r20 L g dt = BitVec.ofNat 64 (P.qLen (cta L g .z)) ∧
    v_r21 L g dt = BitVec.ofNat 64 (P.past (cta L g .z)) ∧
    v_r22 L g dt = BitVec.ofNat 64 (P.nBias (cta L g .z)) ∧
    v_r23 L g dt = BitVec.ofNat 64 (P.past (cta L g .z) / 128) ∧
    v_r24 L g dt = BitVec.ofNat 64 (P.blocks (cta L g .z) * 128) ∧
    v_r25 L g dt = BitVec.ofNat 64 (P.numIters (cta L g .z) (cta L g .x)) ∧
    v_r26 L g dt = BitVec.ofNat 64 (P.numIters (cta L g .z) (cta L g .x)) ∧
    v_r32 L g dt = BitVec.ofNat 64 (numPre P (cta L g .z) (cta L g .x)) := by
  have hr := (cta_lt hpre hg).2.2
  have hx := (cta_lt hpre hg).1
  have hb := bnd_of_pre hpre hr hm
  have hw := wordsOk_of_pre hpre hg ha hs hm
  have hq : dt.cu1 - dt.cu0 = P.qLen (cta L g .z) := by
    simp [Params.qLen, hm.cu0, hm.cu1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r20_val L g dt hb, hq]
  · rw [r21_val L g dt hb, pastN_eq hm]
  · rw [r22_eq L g dt hb, pastN_eq hm]
    rfl
  · rw [r23_eq L g dt hb, pastN_eq hm]
  · rw [r24_eq L g dt hb, blocksN_eq hm]
  · rw [r25_eq L g dt ha hw, itersN_eq hs hx hm]
  · rw [r26_eq L g dt ha hw, itersN_eq hs hx hm]
  · rw [r32_eq L g dt ha hw, itersN_eq hs hx hm, oldN_eq hs hx hm]
    rfl

/-! ### The values the hand-off carries

`valueOf L g dt id` is the value the table gives register `id`. The registers of the exit
(`exitRegs`) that the softmax region reads are, by their ids in the table: `481 = q_len`,
`482 = pos0 = past`, `483 = n_bias`, `484 = fa_mask_right`, `485 = rel_base + REL_PAD`,
`486`, `487 = num_iters`, `493 = num_pre`, `623`, `624` the two barrier addresses. -/

theorem exit_values (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) {dt : Dat}
    (ha : ArgsOk L g dt.pro) (hs : dt.pro.w71 = P.splits)
    (hm : WordsMatch P (cta L g .z) dt) :
    valueOf L g dt 481 = b32 (P.qLen (cta L g .z)) ∧
    valueOf L g dt 482 = b32 (P.past (cta L g .z)) ∧
    valueOf L g dt 483 = b32 (P.nBias (cta L g .z)) ∧
    valueOf L g dt 484 = b32 (P.past (cta L g .z) / 128) ∧
    valueOf L g dt 485 = b32 (P.blocks (cta L g .z) * 128) ∧
    valueOf L g dt 486 = b32 (P.numIters (cta L g .z) (cta L g .x)) ∧
    valueOf L g dt 487 = b32 (P.numIters (cta L g .z) (cta L g .x)) ∧
    valueOf L g dt 493 = b32 (numPre P (cta L g .z) (cta L g .x)) ∧
    valueOf L g dt 623 = b32 ((L.sharedBase + 213312) % 2 ^ 32) ∧
    valueOf L g dt 624 = b32 ((L.sharedBase + 213328) % 2 ^ 32) := by
  obtain ⟨h20, h21, h22, h23, h24, h25, h26, h32⟩ := exit_spec hpre hg ha hs hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Value.bits 32 (v_r20 L g dt) = _
    rw [h20]; rfl
  · show Value.bits 32 (v_r21 L g dt) = _
    rw [h21]; rfl
  · show Value.bits 32 (v_r22 L g dt) = _
    rw [h22]; rfl
  · show Value.bits 32 (v_r23 L g dt) = _
    rw [h23]; rfl
  · show Value.bits 32 (v_r24 L g dt) = _
    rw [h24]; rfl
  · show Value.bits 32 (v_r25 L g dt) = _
    rw [h25]; rfl
  · show Value.bits 32 (v_r26 L g dt) = _
    rw [h26]; rfl
  · show Value.bits 32 (v_r32 L g dt) = _
    rw [h32]; rfl
  · show Value.bits 32 (v_r162 L g dt) = _
    rw [r162_eq]; rfl
  · show Value.bits 32 (v_r163 L g dt) = _
    rw [r163_eq]; rfl

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
