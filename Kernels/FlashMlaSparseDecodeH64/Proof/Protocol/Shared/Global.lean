-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ordered
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.GlobalCls
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.StoreUnique
import Lemmas.Arith.MixedRadix

@[expose] public section

/-! # The bytes outside shared memory are ordered

Every access of a byte outside shared memory is of one of three kinds (`GlobalAt`): the LSE store
of a lane, a slot of an output tensor store, or a tensor load's read of an input byte. Two
accesses of one byte, one of them a write, are
* two LSE stores: the word names the lane (`64 ctaOf + tid`), so they are one thread's, ordered by
  program order (`same_thread`);
* two slots of output stores: the byte names the CTA tile, the slot and the warp and chunk of its
  columns, which name one store (`store_unique`), so they are one access;
* an LSE store or an output slot against another kind: the LSE output, the output tensor and the
  inputs are apart (`Pre`), so there is none. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The first column of a warp's chunk and the slot's column name the warp, the chunk and the
column. -/
private theorem col_inj {w w' c c' x x' : Nat} (hw : w < 2) (hw' : w' < 2) (hc : c < 4)
    (hc' : c' < 4) (hx : x < 64) (hx' : x' < 64)
    (h : 128 * w + [0, 64, 256, 320].getD c 0 + x = 128 * w' + [0, 64, 256, 320].getD c' 0 + x') :
    w = w' ∧ c = c' ∧ x = x' := by
  interval_cases c <;> interval_cases c' <;>
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h <;> omega

/-- The LSE words name their lane: two lanes whose words (of the lanes' CTA and thread) overlap
are one lane. -/
private theorem lse_lane (hp : Pre P L m) {g g' : Nat} (h1 : tidOf L g < 64) (h2 : tidOf L g' < 64)
    {l : Loc} (a1 : P.lseBase + 4 * (ctaOf L g * 64 + tidOf L g) ≤ l.addr)
    (a2 : l.addr < P.lseBase + 4 * (ctaOf L g * 64 + tidOf L g) + 4)
    (b1 : P.lseBase + 4 * (ctaOf L g' * 64 + tidOf L g') ≤ l.addr)
    (b2 : l.addr < P.lseBase + 4 * (ctaOf L g' * 64 + tidOf L g') + 4) : g = g' := by
  simp only [ctaOf, tidOf_eq hp, hp.block] at *
  omega

/-- A slot's kind, with its parts named. -/
private theorem store_inv {l : Loc} {i : EvId} {x y z : Nat}
    (h : GlobalAt P L X l (.async i (.write (.store x y z))) true) :
    ∃ addr c s, X.TensorStoreIssue i addr s ∧ MbarRow.warp L i.1 < 2 ∧ c < 4 ∧
      s.origin 0 = ((128 * MbarRow.warp L i.1 + [0, 64, 256, 320].getD c 0 : Nat) : Int) ∧
      x < 64 ∧ y < 64 ∧ z < 2 ∧
      l = ⟨.global, 0, P.outBase + 2 * ((ctaOf L i.1 * 64 + y) * 512 +
        (128 * MbarRow.warp L i.1 + [0, 64, 256, 320].getD c 0 + x)) + z⟩ := by
  cases h with
  | store hi hw hc ho hx hy hz hl hO => exact ⟨_, _, _, hi, hw, hc, ho, hx, hy, hz, hl⟩

/-- **Two output slots covering one byte are one slot of one store.** -/
private theorem store_pair (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {l : Loc} {i i' : EvId} {x y z x' y' z' : Nat}
    (h : GlobalAt P L X l (.async i (.write (.store x y z))) true)
    (h' : GlobalAt P L X l (.async i' (.write (.store x' y' z'))) true) :
    i = i' ∧ x = x' ∧ y = y' ∧ z = z' := by
  obtain ⟨a₁, c₁, s₁, hi, hw, hc, ho, hx, hy, hz, hl⟩ := store_inv h
  obtain ⟨a₂, c₂, s₂, hi', hw', hc', ho', hx', hy', hz', hl'⟩ := store_inv h'
  have hl2 := hl.symm.trans hl'
  simp only [Loc.mk.injEq, true_and] at hl2
  have hT : ∀ {w c x : Nat}, w < 2 → c < 4 → x < 64 →
      128 * w + [0, 64, 256, 320].getD c 0 + x < 512 := by
    intro w c x hw hc hx
    interval_cases c <;> simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega
  have hz2 : z = z' ∧ ((ctaOf L i.1 * 64 + y) * 512 +
      (128 * MbarRow.warp L i.1 + [0, 64, 256, 320].getD c₁ 0 + x)) =
      ((ctaOf L i'.1 * 64 + y') * 512 +
      (128 * MbarRow.warp L i'.1 + [0, 64, 256, 320].getD c₂ 0 + x')) := by omega
  obtain ⟨rfl, hz3⟩ := hz2
  obtain ⟨hr1, hr2⟩ := Nat.digits_of_eq (hT hw hc hx) (hT hw' hc' hx') hz3
  obtain ⟨hr3, hy2⟩ := Nat.digits_of_eq hy hy' hr1
  obtain ⟨hw2, hc2, hx2⟩ := col_inj hw hw' hc hc' hx hx' hr2
  subst hy2 hc2 hx2
  have hcta : i.1 / L.block = i'.1 / L.block := by simpa only [ctaOf] using hr3
  have hss : s₁.origin 0 = s₂.origin 0 := by rw [ho, ho', hw2]
  obtain ⟨hg, hk⟩ := store_unique hp hX hFw hnu hi hi' hcta hw2 hss
  exact ⟨Prod.ext hg hk, rfl, rfl, rfl⟩

/-- The LSE output and the output tensor are apart. -/
private theorem out_lse {l : Loc} (hp : Pre P L m) (h1 : OutByte P l) (h2 : LseByte P l) :
    False := by
  obtain ⟨-, -, a1, a2⟩ := h1
  obtain ⟨-, -, b1, b2⟩ := h2
  rcases hp.outApartLse with h | h <;> omega

/-- **The bytes outside shared memory are ordered**: there is no conflict between two accesses of
them, but two LSE stores of one lane, which program order orders. -/
theorem global_ordered (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    ByteOrdered L X fun l => l.space ≠ .shared := by
  intro e f a b l hcon ha hb hl _
  obtain ⟨hne, we, wf, he, hf, hw, hov⟩ := hcon
  have ce := global_at hp hX hFw hnu he ha hl
  have cf := global_at hp hX hFw hnu hf hb hl
  cases ce with
  | @lse g k _ _ _ hg1 ht1 LB a1 a2 =>
    cases cf with
    | @lse g' k' _ _ _ hg2 ht2 LB' b1 b2 =>
      obtain rfl := lse_lane hp ht1 ht2 a1 a2 b1 b2
      have hk : k ≠ k' := fun h => hne (by rw [h])
      exact same_thread he hf hk hov l
    | store _ _ _ _ _ _ _ _ OB => exact (out_lse hp OB LB).elim
    | load _ nL => exact (nL LB).elim
  | store hi1 hw1 hc1 ho1 hx1 hy1 hz1 hl1 OB =>
    cases cf with
    | lse _ _ LB _ _ => exact (out_lse hp OB LB).elim
    | store hi2 hw2 hc2 ho2 hx2 hy2 hz2 hl2 OB' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := store_pair hp hX hFw hnu
        (.store hi1 hw1 hc1 ho1 hx1 hy1 hz1 hl1 OB) (.store hi2 hw2 hc2 ho2 hx2 hy2 hz2 hl2 OB')
      exact (hne rfl).elim
    | load nO _ => exact (nO OB).elim
  | load nO nL =>
    cases cf with
    | lse _ _ LB _ _ => exact (nL LB).elim
    | store _ _ _ _ _ _ _ _ OB => exact (nO OB).elim
    | load _ _ => simp at hw

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
