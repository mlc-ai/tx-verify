-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Lib.LaneFold
import Kernels.InklingRelDecode.Proof.Lib.Rows

@[expose] public section

/-! # The fold's probability words against the lane's

The fold's words of a row (`FoldWords`) as one function of the CTA, the round, the row and the key,
independent of the dimension, and the lane's words (`lanePw`) are its values. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX Finset SoftRow SoftFold Classical

theorem blockMax_fst : ∀ (a b : List (ℝ × ℝ)), a.map Prod.fst = b.map Prod.fst →
    blockMax a = blockMax b
  | [], [], _ => rfl
  | p :: a, q :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [blockMax, List.foldr_cons] at *
    rw [h.1]
    congr 1
    exact blockMax_fst a b h.2
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem kBlk_fst (P : Params) (r s tok h d d' i : Nat) :
    (kBlk P r s tok h d i).map Prod.fst = (kBlk P r s tok h d' i).map Prod.fst := by
  simp [kBlk, blockList, pair, List.map_map, Function.comp_def]

theorem run_m_fst (sl : ℝ) : ∀ (as bs : List (List (ℝ × ℝ))) (st st' : St),
    List.Forall₂ (fun a b => a.map Prod.fst = b.map Prod.fst) as bs → st.m = st'.m →
    ((as.foldl (fun st blk => step sl blk st) st).m) =
      ((bs.foldl (fun st blk => step sl blk st) st').m)
  | [], [], _, _, _, h => h
  | a :: as, b :: bs, st, st', hf, h => by
    obtain ⟨h1, h2⟩ := List.forall₂_cons.mp hf
    simp only [List.foldl_cons]
    refine run_m_fst sl as bs _ _ h2 ?_
    simp only [step, h, blockMax_fst a b h1]
  | [], _ :: _, _, _, hf, _ => by cases hf
  | _ :: _, [], _, _, hf, _ => by cases hf

theorem kSt_m (P : Params) (r s tok h d d' n : Nat) :
    (kSt P r s tok h d n).m = (kSt P r s tok h d' n).m := by
  unfold kSt SoftFold.run
  refine run_m_fst _ _ _ _ _ ?_ rfl
  simp only [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun x _ => kBlk_fst P r s tok h d d' x

theorem mUse_d (P : Params) (r s tok h d d' i : Nat) :
    mUseOf (P.scale * log2eF32) (kBlk P r s tok h d i) (kSt P r s tok h d i) =
      mUseOf (P.scale * log2eF32) (kBlk P r s tok h d' i) (kSt P r s tok h d' i) := by
  unfold mUseOf
  rw [blockMax_fst _ _ (kBlk_fst P r s tok h d d' i), kSt_m P r s tok h d d' i]

theorem alpha_d (P : Params) (r s tok h d d' i : Nat) :
    stepAlpha (P.scale * log2eF32) (kBlk P r s tok h d i) (kSt P r s tok h d i) =
      stepAlpha (P.scale * log2eF32) (kBlk P r s tok h d' i) (kSt P r s tok h d' i) := by
  unfold stepAlpha
  rw [blockMax_fst _ _ (kBlk_fst P r s tok h d d' i), kSt_m P r s tok h d d' i]

theorem mem_blockKeys {P : Params} {r s tok i κ : Nat} (hs : 0 < P.splits)
    (hi : i < P.numIters r s) (hk : κ < 128) :
    128 * (P.splits * i + s) + κ ∈ blockKeys P r s tok i ↔
      128 * (P.splits * i + s) + κ ≤ P.past r + tok := by
  have hb := blk_lt hs hi
  have hm : P.splits * i = i * P.splits := Nat.mul_comm _ _
  unfold blockKeys keys
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
  simp only [Params.inSplit]
  have hq : (128 * (P.splits * i + s) + κ) / 128 = P.splits * i + s := by omega
  rw [hq]
  constructor
  · rintro ⟨⟨-, -, h⟩, -⟩
    exact h
  · intro h
    refine ⟨⟨by omega, ⟨by omega, ?_, by omega⟩, h⟩, by omega⟩
    rw [Nat.add_sub_cancel]
    exact Nat.mul_mod_right _ _

/-- **The fold's probability word** of the CTA `c`, the round `b`, the tile row and the key `κ`
of the block. -/
noncomputable def foldPw (Q : Params) (L : Launch) (c b row κ : Nat) : ℝ :=
  if 128 * (Q.splits * b + (L.ctaidOf c).get .x) + κ ∈
      blockKeys Q ((L.ctaidOf c).get .z) ((L.ctaidOf c).get .x) (row / 6) b then
    pExp (Q.scale * log2eF32) (mUseOf (Q.scale * log2eF32)
      (kBlk Q ((L.ctaidOf c).get .z) ((L.ctaidOf c).get .x) (row / 6)
        ((L.ctaidOf c).get .y * 6 + row % 6) 0 b)
      (kSt Q ((L.ctaidOf c).get .z) ((L.ctaidOf c).get .x) (row / 6)
        ((L.ctaidOf c).get .y * 6 + row % 6) 0 b))
      (keyPair Q ((L.ctaidOf c).get .z) (row / 6) ((L.ctaidOf c).get .y * 6 + row % 6) 0
        (128 * (Q.splits * b + (L.ctaidOf c).get .x) + κ))
  else 0

/-- **The fold's rescale factor** of the CTA `c`, the round `b` and the tile row. -/
noncomputable def foldAl (Q : Params) (L : Launch) (c b row : Nat) : ℝ :=
  stepAlpha (Q.scale * log2eF32)
    (kBlk Q ((L.ctaidOf c).get .z) ((L.ctaidOf c).get .x) (row / 6)
      ((L.ctaidOf c).get .y * 6 + row % 6) 0 b)
    (kSt Q ((L.ctaidOf c).get .z) ((L.ctaidOf c).get .x) (row / 6)
      ((L.ctaidOf c).get .y * 6 + row % 6) 0 b)

/-- **The lane's probability word is the fold's** for a block of the row. -/
theorem lanePw_eq (Q : Params) (L : Launch) (g i c : Nat) (hs : 0 < Q.splits)
    (hsc : 0 < Q.scale)
    (hi : i < Q.numIters ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x))
    (hc : c < 64) :
    lanePw Q L g i c = foldPw Q L (g / L.block) i (softRow (g % L.block))
      (64 * (g % L.block / 16 % 2) + c) := by
  have key : laneKey Q L g i c = 128 * (Q.splits * i + (L.ctaidOf (g / L.block)).get .x) +
      (64 * (g % L.block / 16 % 2) + c) := by
    unfold laneKey; omega
  have hmem := mem_blockKeys (tok := softRow (g % L.block) / 6) hs hi
    (show 64 * (g % L.block / 16 % 2) + c < 128 by omega)
  unfold lanePw foldPw
  rw [key]
  by_cases hv : 128 * (Q.splits * i + (L.ctaidOf (g / L.block)).get .x) +
      (64 * (g % L.block / 16 % 2) + c) ≤ Q.past ((L.ctaidOf (g / L.block)).get .z) +
        softRow (g % L.block) / 6
  · simp only [hv, hmem.mpr hv, ite_true]
    have hne := hsc.ne'
    unfold pExp keyPair pair
    simp only [laneHead, laneBlk, laneSt]
    congr 3
    unfold laneBias laneScore laneHead laneKey
    simp only [add_assoc]
    field_simp
    ring
  · have hn : ¬ (128 * (Q.splits * i + (L.ctaidOf (g / L.block)).get .x) +
        (64 * (g % L.block / 16 % 2) + c) ∈ blockKeys Q ((L.ctaidOf (g / L.block)).get .z)
        ((L.ctaidOf (g / L.block)).get .x) (softRow (g % L.block) / 6) i) := fun h => hv (hmem.mp h)
    simp only [hv, hn, ite_false]

end PTX.Kernels.InklingRelDecode.Proof.Lib
