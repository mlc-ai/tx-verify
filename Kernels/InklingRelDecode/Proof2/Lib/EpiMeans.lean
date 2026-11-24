-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DCompTail
public import Kernels.InklingRelDecode.Proof.Thread.EvDEpiMeans
public import Kernels.InklingRelDecode.Proof.Thread.EvSBiasSpec

@[expose] public section

/-!
# The bridge's numbers

Moved from the first tree's `Proof/Interface/Reach.lean` (names and namespace unchanged):
`SmMeans` (what the softmax region's entry numbers mean, with the launch's `num_tokens` and
output bases) and `exitIn_means` (the numbers the loop hands the bridge mean what `Epi.Means`
says), with their arithmetic helpers; `oLoc_range`, `lseLoc_range` from
`Proof/Interface/OutputFrame.lean` (the output elements are inside their arrays).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- What the softmax region's entry numbers `e` mean for thread `g`: the documented fields of
`SmEntry.entOf`, and the launch's `num_tokens` and output bases. -/
structure SmMeans (Q : Params) (L : Launch) (g : Nat) (e : Sm.Ent) : Prop where
  ent : Sm.EntMeans Q (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) e
  ntok : e.ntok = Q.nTok % 2 ^ 32
  rd75 : e.rd75 = Q.oBase % 2 ^ 64
  rd76 : e.rd76 = Q.lseBase % 2 ^ 64

theorem rowM_eq (T : Nat) : Sm.row T = Epi.rowM T := by
  unfold Sm.row Epi.rowM
  omega

theorem rowM_lt (T : Nat) : Epi.rowM T < 64 := by
  unfold Epi.rowM
  omega

theorem tokOf_eq (T : Nat) : Sm.tokOf T = Epi.tokM T := by
  have key : ∀ x : Nat, x < 64 → x * 43 / 256 = x / 6 := by decide
  unfold Sm.tokOf Epi.tokM
  rw [rowM_eq]
  exact key _ (rowM_lt T)

theorem remOf_eq (T : Nat) : Sm.remOf T = Epi.rowM T % 6 := by
  unfold Sm.remOf
  rw [tokOf_eq, rowM_eq]
  unfold Epi.tokM
  omega

/-- **The numbers the loop hands the bridge mean what `Epi.Means` says**, given the entry numbers'
meaning. -/
theorem exitIn_means (hpre : Pre Q L mem0) (hg : g < L.threads) {d : Sm.D}
    (hm : SmMeans Q L g d.e) : Epi.Means Q L g (Br.prm (DComp.exitIn L g d)) := by
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  have hnt := hpre.nTokRange
  have hob : Q.oBase < 2 ^ 64 := by
    have h1 := hpre.oRange
    have h2 : 0 < oBytes Q := by
      unfold oBytes
      have := hpre.splitsPos
      have := hpre.nTokPos
      unfold heads headDim
      positivity
    omega
  have hlb : Q.lseBase < 2 ^ 64 := by
    have h1 := hpre.lseRange
    have h2 : 0 < lseBytes Q := by
      unfold lseBytes
      have := hpre.splitsPos
      have := hpre.nTokPos
      unfold heads
      positivity
    omega
  have hy1 : ProA.cta L g .y ≤ 1 := by unfold kvHeads at hy; omega
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show d.e.ntok = _
    rw [hm.ntok]
    exact Nat.mod_eq_of_lt (by omega)
  · exact hm.ent.split
  · exact hm.ent.qs
  · exact tokOf_eq _
  · show (d.e.kvh + Sm.remOf (g % L.block)) % 2 ^ 32 = _
    rw [hm.ent.kvh, remOf_eq]
    unfold Epi.headM
    have : Epi.rowM (g % L.block) % 6 < 6 := Nat.mod_lt _ (by omega)
    omega
  · show Sm.half (g % L.block) * 64 = _
    unfold Epi.halfM Sm.half
    omega
  · show Sm.rowValid d.e (g % L.block) = _
    unfold Sm.rowValid
    rw [hm.ent.qlen, rowM_eq, tokOf_eq]
  · show (L.sharedBase + 213328) % 2 ^ 32 = _
    rfl
  · show d.e.rd75 = _
    rw [hm.rd75]
    exact Nat.mod_eq_of_lt hob
  · show d.e.rd76 = _
    rw [hm.rd76]
    exact Nat.mod_eq_of_lt hlb
  · rfl

/-- The element of an output row is inside the array (`Spec.oBytes`). -/
theorem oLoc_range (s t h d : Nat) (hs : s < Q.splits) (ht : t < Q.nTok) (hh : h < heads)
    (hd : d < headDim) :
    Q.oBase ≤ (oLoc Q s t h d).addr ∧ (oLoc Q s t h d).addr + 4 ≤ Q.oBase + oBytes Q := by
  have h1 : s * Q.nTok + t + 1 ≤ Q.splits * Q.nTok := by
    have := Nat.mul_le_mul_right Q.nTok (show s + 1 ≤ Q.splits by omega)
    rw [Nat.succ_mul] at this
    omega
  have hh' : h < 12 := hh
  have hd' : d < 128 := hd
  have h2 : (s * Q.nTok + t) * 12 + h + 1 ≤ Q.splits * Q.nTok * 12 := by nlinarith
  have h3 : ((s * Q.nTok + t) * 12 + h) * 128 + d + 1 ≤ Q.splits * Q.nTok * 12 * 128 := by
    nlinarith
  simp only [oLoc, oBytes, heads, headDim]
  constructor
  · omega
  · have : 4 * Q.splits * Q.nTok * 12 * 128 = 4 * (Q.splits * Q.nTok * 12 * 128) := by ring
    omega

/-- The `LsePart` element is inside the array. -/
theorem lseLoc_range (s t h : Nat) (hs : s < Q.splits) (ht : t < Q.nTok) (hh : h < heads) :
    Q.lseBase ≤ (lseLoc Q s t h).addr ∧
      (lseLoc Q s t h).addr + 4 ≤ Q.lseBase + lseBytes Q := by
  have h1 : s * Q.nTok + t + 1 ≤ Q.splits * Q.nTok := by
    have := Nat.mul_le_mul_right Q.nTok (show s + 1 ≤ Q.splits by omega)
    rw [Nat.succ_mul] at this
    omega
  have hh' : h < 12 := hh
  have h2 : (s * Q.nTok + t) * 12 + h + 1 ≤ Q.splits * Q.nTok * 12 := by nlinarith
  simp only [lseLoc, lseBytes, heads]
  constructor
  · omega
  · have : 4 * Q.splits * Q.nTok * 12 = 4 * (Q.splits * Q.nTok * 12) := by ring
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
