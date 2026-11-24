-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvDEpiStore
public import Kernels.InklingRelDecode.Proof.Thread.ProBSpec

@[expose] public section

/-!
# What the epilogue's registers mean: the output row of a thread

The epilogue carries the registers the softmax region leaves (`Epi.Prm`). `Means P L g pr` says
what each is for thread `g` of the default partition, in terms of the launch and `Spec`:

* `tid`, `w` (warp index), `p3` (the guard of the Tensor Memory release): the thread's own;
* `b` is `%ctaid.x` (the split), `a` is `num_tokens`, `dd` is `cu_seqlens_q[request]` with the
  request `%ctaid.z`; `ob`, `lb` are the bases of `OPart` and `LsePart` (parameters 10 and 11);
  `mb` is the address of `o_final`; `c0` is the Tensor Memory base plus 256 (the `O` tile);
* the tile row `m = ((tid & 96) >> 1) | (tid & 15)` (PTX `kernel_module.py:279`) is token
  `c = m / 6` of the request and head `e = 6 · ctaid.y + m % 6` (lines 280, 286); the row is valid,
  `rv`, when `m < 60` and `c < q_len` (line 281); `d0 = 64 · (tid / 16 % 2)` is the first column
  of the thread's half row (lines 283, 285).

`Means` is a statement about registers of the softmax region: its fields `a`, `b`, `dd`, `mb`,
`ob`, `lb`, `tid`, `tm`, `w`, `p3`, `c0` are registers the prologue's exit leaves live
(`exit_carried`: the prologue machine's table gives them these values), the others (`c`, `e`,
`d0`, `rv`) are computed from `tid` by the softmax region's first instructions (PTX lines
1195-1226, read here, not yet a machine fact: the development notes, "thread-layer gaps").

From `Means` and `Pre`: the store of word `k` writes `oLoc P split token head (d0 + k)` and the
store of `LsePart` writes `lseLoc P split token head` (`stO_loc`, `stLse_loc`), the footprints the
output `Post` speaks about.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

/-- The tile row of thread index `tid` of the default partition: `((tid & 96) >> 1) | (tid & 15)`
for `tid < 128`. -/
def rowM (tid : Nat) : Nat := 16 * (tid / 32 % 4) + tid % 16

/-- Its token (`m · 43 >> 8`, which is `m / 6` for `m < 64`), query head and half. -/
def tokM (tid : Nat) : Nat := rowM tid / 6
def headM (kvh tid : Nat) : Nat := 6 * kvh + rowM tid % 6
def halfM (tid : Nat) : Nat := tid / 16 % 2

/-- What the epilogue's registers are for thread `g`. -/
structure Means (P : Params) (L : Launch) (g : Nat) (pr : Prm) : Prop where
  tid : pr.tid = g % L.block
  w : pr.w = g % L.block / 32
  p3 : pr.p3 = decide (g % L.block < 32)
  a : pr.a = P.nTok
  b : pr.b = ProA.cta L g .x
  dd : pr.dd = P.qStart (ProA.cta L g .z)
  c : pr.c = tokM (g % L.block)
  e : pr.e = headM (ProA.cta L g .y) (g % L.block)
  d0 : pr.d0 = 64 * halfM (g % L.block)
  rv : pr.rv = decide (rowM (g % L.block) < 60 ∧
    tokM (g % L.block) < P.qLen (ProA.cta L g .z))
  mb : pr.mb = (L.sharedBase + Bar.off .oFinal) % 2 ^ 32
  ob : pr.ob = P.oBase
  lb : pr.lb = P.lseBase
  c0 : pr.c0 = (pr.tm + 256) % 2 ^ 32

/-- The recorded lane bits do not enter `Means`. -/
theorem Means.bw {P : Params} {L : Launch} {g : Nat} {pr : Prm} (h : Means P L g pr) (b : Nat) :
    Means P L g { pr with bw := b } := by
  cases h
  constructor <;> assumption

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {pr : Prm}

/-- The coordinates of a valid row are in range. -/
theorem row_coords (hpre : Pre P L mem0) (hg : g < L.threads) (hm : Means P L g pr)
    (hrv : pr.rv = true) :
    ProA.cta L g .x < P.splits ∧ ProA.cta L g .z < P.b ∧
      P.qStart (ProA.cta L g .z) + tokM (g % L.block) < P.nTok ∧
      headM (ProA.cta L g .y) (g % L.block) < heads := by
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  rw [hm.rv] at hrv
  simp only [decide_eq_true_eq] at hrv
  refine ⟨hx, hz, token_lt hpre hz hrv.2, ?_⟩
  have h1 : ProA.cta L g .y ≤ 1 := by unfold kvHeads at hy; omega
  have h2 : rowM (g % L.block) % 6 < 6 := Nat.mod_lt _ (by omega)
  unfold headM heads
  omega

/-- The 32-bit arithmetic of the output row index does not wrap. -/
theorem row_arith (a b c dd e X : Nat) (hN : b * a + (dd + c) < X) (hX : X * 12 * 128 < 2 ^ 31)
    (he : e < 12) :
    ((((a * b + c) % M32 + dd) % M32) * 12 + e) % M32 = (b * a + (dd + c)) * 12 + e := by
  rw [Nat.mul_comm a b]
  generalize b * a = A at *
  unfold M32
  omega

/-- The output row index the code computes, `((split · num_tokens + token) · 12 + head)`, with no
wrap-around in its 32-bit arithmetic, and the last element of its `OPart` row is inside the
array. -/
theorem row_eq (hpre : Pre P L mem0) (hg : g < L.threads) (hm : Means P L g pr)
    (hrv : pr.rv = true) :
    pr.row = (ProA.cta L g .x * P.nTok +
      (P.qStart (ProA.cta L g .z) + tokM (g % L.block))) * 12 +
        headM (ProA.cta L g .y) (g % L.block) ∧
    ((ProA.cta L g .x * P.nTok + (P.qStart (ProA.cta L g .z) + tokM (g % L.block))) * 12 +
      headM (ProA.cta L g .y) (g % L.block)) * 128 + 128 ≤ P.splits * P.nTok * heads * headDim := by
  obtain ⟨hx, hz, ht, hh⟩ := row_coords hpre hg hm hrv
  have hout := hpre.outRange
  have hs1 : (ProA.cta L g .x + 1) * P.nTok ≤ P.splits * P.nTok :=
    Nat.mul_le_mul_right _ hx
  have hN : ProA.cta L g .x * P.nTok + (P.qStart (ProA.cta L g .z) + tokM (g % L.block)) <
      P.splits * P.nTok := by
    rw [Nat.add_mul, Nat.one_mul] at hs1
    omega
  have hh' : headM (ProA.cta L g .y) (g % L.block) < 12 := hh
  unfold heads headDim at *
  constructor
  · have := row_arith pr.a pr.b pr.c pr.dd pr.e (P.splits * P.nTok)
      (by rw [hm.a, hm.b, hm.c, hm.dd]; exact hN)
      (by omega) (by rw [hm.e]; exact hh')
    simp only [Prm.row, Prm.r1898, Prm.r1897]
    rw [this, hm.a, hm.b, hm.c, hm.dd, hm.e]
  · omega

/-- **The address of word `k` of the thread's `OPart` row**: `Prm.oAddr + 4 k` is the byte
address of `OPart[split, token, head, 64 · half + k]`. -/
theorem oAddr_eq (hpre : Pre P L mem0) (hg : g < L.threads) (hm : Means P L g pr)
    (hrv : pr.rv = true) {k : Nat} (hk : k < 64) :
    (pr.oAddr + 4 * k) % M64 =
      (oLoc P (ProA.cta L g .x) (P.qStart (ProA.cta L g .z) + tokM (g % L.block))
        (headM (ProA.cta L g .y) (g % L.block)) (64 * halfM (g % L.block) + k)).addr := by
  obtain ⟨hrow, hbnd⟩ := row_eq hpre hg hm hrv
  have hhalf : halfM (g % L.block) ≤ 1 := by unfold halfM; omega
  have hr := hpre.oRange
  have h4 : 4 * P.splits * P.nTok = 4 * (P.splits * P.nTok) := by ring
  unfold oBytes at hr
  rw [h4] at hr
  simp only [oLoc, Prm.oAddr, hrow, hm.ob, hm.d0]
  unfold heads headDim at *
  unfold M64
  generalize P.splits * P.nTok = Y at *
  generalize (ProA.cta L g .x * P.nTok + (P.qStart (ProA.cta L g .z) + tokM (g % L.block))) * 12 +
    headM (ProA.cta L g .y) (g % L.block) = R at *
  generalize halfM (g % L.block) = H at *
  omega

/-- **The address of the thread's `LsePart` word**: `Prm.lAddr` is the byte address of
`LsePart[split, token, head]`. -/
theorem lAddr_eq (hpre : Pre P L mem0) (hg : g < L.threads) (hm : Means P L g pr)
    (hrv : pr.rv = true) :
    pr.lAddr =
      (lseLoc P (ProA.cta L g .x) (P.qStart (ProA.cta L g .z) + tokM (g % L.block))
        (headM (ProA.cta L g .y) (g % L.block))).addr := by
  obtain ⟨hrow, hbnd⟩ := row_eq hpre hg hm hrv
  have hr := hpre.lseRange
  have h4 : 4 * P.splits * P.nTok = 4 * (P.splits * P.nTok) := by ring
  unfold lseBytes at hr
  rw [h4] at hr
  simp only [lseLoc, Prm.lAddr, hrow, hm.lb]
  unfold heads headDim at *
  unfold M64
  generalize P.splits * P.nTok = Y at *
  omega

/-! ### The registers the prologue's exit leaves for the epilogue -/

/-! ### The events of the stores, in the specification's coordinates -/

/-- The split, the token (counted over the whole tensor), the head and the first column of the
half row of thread `g`'s output row. -/
abbrev outSplit (L : Launch) (g : Nat) : Nat := ProA.cta L g .x
abbrev outToken (P : Params) (L : Launch) (g : Nat) : Nat :=
  P.qStart (ProA.cta L g .z) + tokM (g % L.block)
abbrev outHead (L : Launch) (g : Nat) : Nat := headM (ProA.cta L g .y) (g % L.block)
abbrev outCol0 (L : Launch) (g : Nat) : Nat := 64 * halfM (g % L.block)

variable {d : D} {e : Event} {u : TState}

/-- **The poll of `o_final`, by function**: a poll of the barrier `EvD.Bar.oFinal` of the thread's
own CTA, parity 0, acquire at CTA scope (the address register is `sharedBase + off` of
`o_final`, and the launch's shared window does not wrap). -/
theorem shape_wait_oFinal (hsb : L.sharedBase + 213340 ≤ 2 ^ 18) (hm : Means P L g d.pr)
    (hF : Fired L g d e (some u)) (hs : d.site = .wait) :
    ∃ ok, e = ⟨evPc d.site, .wait (Bar.loc L (g / L.block) .oFinal) 0 ok true .cta⟩ := by
  obtain ⟨ok, he⟩ := shape_wait hF hs
  refine ⟨ok, ?_⟩
  rw [he, hm.mb]
  have : (L.sharedBase + Bar.off .oFinal) % 2 ^ 32 = L.sharedBase + Bar.off .oFinal := by
    apply Nat.mod_eq_of_lt
    simp only [Bar.off]
    omega
  rw [this]
  rfl

/-- **A store of `OPart`, in the specification's terms**: word `k` of the thread's half row is
written, four bytes `storeValue 32 (D.word k)`, to `oLoc P split token head (col0 + k)`. -/
theorem shape_stO_loc (hpre : Pre P L mem0) (hg : g < L.threads) (hm : Means P L g d.pr)
    {k : Fin 64} (hF : Fired L g d e (some u)) (hs : d.site = .stO k) :
    ∃ v', storeValue 32 (d.word k.val) = .ok v' ∧
      e = ⟨evPc d.site, .wr (wordAcc (oLoc P (outSplit L g) (outToken P L g) (outHead L g)
        (outCol0 L g + k.val))) v'.toBytes⟩ := by
  obtain ⟨v', hv, he⟩ := shape_stO hF hs
  obtain ⟨t, -, hi, -⟩ := hF
  have hrv : d.pr.rv = true := hi.rv (by rw [hs]; trivial)
  have hloc := oAddr_eq hpre hg hm hrv k.isLt
  refine ⟨v', hv, ?_⟩
  rw [he]
  have : (⟨.global, 0, (d.pr.oAddr + 4 * k.val) % M64⟩ : Loc) =
      oLoc P (outSplit L g) (outToken P L g) (outHead L g) (outCol0 L g + k.val) := by
    unfold oLoc
    exact congrArg (Loc.mk .global 0) hloc
  rw [this]

/-- **The store of `LsePart`, in the specification's terms**: four bytes `storeValue 32
(Prm.lseWord)` to `lseLoc P split token head`. -/
theorem shape_stLse_loc (hpre : Pre P L mem0) (hg : g < L.threads) (hm : Means P L g d.pr)
    (hF : Fired L g d e (some u)) (hs : d.site = .stLse) :
    ∃ v', storeValue 32 d.pr.lseWord = .ok v' ∧
      e = ⟨evPc d.site, .wr (wordAcc (lseLoc P (outSplit L g) (outToken P L g) (outHead L g)))
        v'.toBytes⟩ := by
  obtain ⟨v', hv, he⟩ := shape_stLse hF hs
  obtain ⟨t, -, hi, -⟩ := hF
  have hrv : d.pr.rv = true := hi.rv (by rw [hs]; trivial)
  have hloc := lAddr_eq hpre hg hm hrv
  refine ⟨v', hv, ?_⟩
  rw [he]
  have : (⟨.global, 0, d.pr.lAddr⟩ : Loc) =
      lseLoc P (outSplit L g) (outToken P L g) (outHead L g) := by
    unfold lseLoc
    exact congrArg (Loc.mk .global 0) hloc
  rw [this]

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
