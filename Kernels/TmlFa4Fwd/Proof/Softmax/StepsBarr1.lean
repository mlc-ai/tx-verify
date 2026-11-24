-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsProd1
public import Lemmas.Flow.RegionSlice
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Proof.Softmax.MaskFold
import Kernels.TmlFa4Fwd.Proof.Softmax.MaskW0
import Kernels.TmlFa4Fwd.Proof.Softmax.MaskW1
import Kernels.TmlFa4Fwd.Proof.Softmax.MaskW2
import Kernels.TmlFa4Fwd.Proof.Softmax.MaskW3
import Kernels.TmlFa4Fwd.Proof.Softmax.RunLand
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # The first round from its bias products to its named-barrier arrival

From pc 3591 (after the bias slot's arrival, or the named barrier's branch for the lanes that do
not arrive) to the arrival at the correction warps' named barrier (`narr .first`, pc 4397): the
scale-word reads, the bias products (`Gen.prod1_run`), the mask count, the four mask words'
selects and the fold (`mask_word0` … `mask_fold`), and the maximum the exponents subtract. Each
piece is stated on the facts it reads; the others are carried by `SegD.frameR` (the code up to the
arrival writes none of them). The end facts are the arrival state's (`valuesNarr1`).
The chain and the steps are in `StepsBarr1b.lean`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (andi scmpi)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- No software `exp2` site in `[lo, hi]`. -/
theorem segFree_in {lo hi : Nat}
    (hS : (List.range (hi + 1 - lo)).all
      (fun i => !Assumptions.swExp2Sites.contains (lo + i)) = true) :
    ∀ pc, lo ≤ pc → pc ≤ hi → Assumption.SegFreePc Assumptions.all pc := by
  intro pc h1 h2
  have := Gen.segFree_range hS (pc - lo) (by omega)
  rwa [show lo + (pc - lo) = pc by omega] at this

/-- A piece with facts `H` carried: the code from `lo` to the event at `hi` writes none of them. -/
theorem seg_frame {lo hi s b : Nat} {F G H : List (Nat × Value)}
    (h : ∃ n, Seg kernel Assumptions.all L g n s F b G)
    (hB : regionS lo hi (H.map Prod.fst) lo ((kernel.code.drop lo).take (hi + 1 - lo)) = true)
    (hS : (List.range (hi + 1 - lo)).all
      (fun i => !Assumptions.swExp2Sites.contains (lo + i)) = true)
    (hlo : lo ≤ s) (hhi : s ≤ hi) :
    ∃ n, Seg kernel Assumptions.all L g n s (F ++ H) b (G ++ H) := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, (SegD.frameR Gen.rulesFrame (SegD.of_seg h) (regionB_of_S hB) (segFree_in hS) hlo
    hhi).seg trivial⟩

/-- Facts of an updated value function from facts of it and of the function before the update. -/
theorem holds_upd {R : Nat → Option Value} {A B C : List Nat} {W : Nat → Value} {k : Nat}
    {x : Value} (hA : Holds R (factsFrom A (Function.update W k x)))
    (hB : Holds R (factsFrom B W))
    (hC : C.all (fun r => A.contains r || (B.contains r && r != k)) = true) :
    Holds R (factsFrom C (Function.update W k x)) := by
  refine holds_of_pointwise fun r hr => ?_
  have h := List.all_eq_true.mp hC r hr
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq] at h
  rcases h with h | ⟨h, hk⟩
  · exact holds_mem hA (mem_factsFrom h)
  · rw [Function.update_of_ne hk]; exact holds_mem hB (mem_factsFrom h)

/-! ### The pieces -/

/-- The scale-word reads (pcs 3591, 3592). -/
theorem ldp1 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 3591
    (factsFrom (ctlLive 3591) (valueOfD p L g ⟨.barr false, v, 0, []⟩)) 3593
    (factsFrom (ctlLive 3593) (vProd1 p L g v)) := by
  have hparams := params hp
  seg_sym using (soft_seg)

/-- The control values from the mask count on: the arrival state's, with the mask count. -/
def vMc (p : Params) (L : Launch) (g : Nat) (v : V) : Nat → Value :=
  Function.update (valueOfD p L g ⟨.narr .first, v, 0, []⟩) 3235 (.bits 32 (mcnt p L g v))

/-- The mask count (pcs 3850 to 3871). -/
theorem mcnt1 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 3850
    (factsFrom (ctlLive 3850) (valueOfD p L g ⟨.narr .first, v, 0, []⟩)) 3872
    (factsFrom (ctlLive 3872) (vMc p L g v)) := by
  have hparams := params hp
  seg_sym using (soft_seg)

/-- The 64 product pairs in the form the mask selects read. -/
def maskPairs (bf : Nat → Bool) (sc : Nat → ℝ) : List (Nat × Value) :=
  (List.range 64).map fun j =>
    (7897 + 2 * j, .pair (bvl (bf (2 * j)) (sc (2 * j))) (bvl (bf (2 * j + 1)) (sc (2 * j + 1))))

/-- The 128 masked elements. -/
def elemsF (m : BitVec 64) (bf : Nat → Bool) (sc : Nat → ℝ) : List (Nat × Value) :=
  (List.range 128).map fun n => (elemRegs.getD n 0, elemVal m bf sc n)

/-- **The selects of the four mask words** (pcs 3872 to 4328). -/
theorem mask_sel (L : Launch) (g : Nat) (m : BitVec 64) (sc : Nat → ℝ) (bf : Nat → Bool) :
    ∃ n, Seg kernel Assumptions.all L g n 3872 ((3235, .bits 32 m) :: maskPairs bf sc) 4329
      (elemsF m bf sc) := by
  obtain ⟨_, h0⟩ := mask_word0 L g m sc bf
  obtain ⟨_, h1⟩ := mask_word1 L g m sc bf
  obtain ⟨_, h2⟩ := mask_word2 L g m sc bf
  obtain ⟨_, h3⟩ := mask_word3 L g m sc bf
  exact ⟨_, ((h0.comp (h1.comp (h2.comp h3))).weaken_start fun R hR =>
    cast (congrArg (Holds R) (by kernel_rfl)) hR).weaken_end fun R hR =>
    cast (congrArg (Holds R) (by kernel_rfl)) hR⟩

/-- **The fold** (pcs 4329 to 4394). -/
theorem mask_fold' (L : Launch) (g : Nat) (m : BitVec 64) (sc : Nat → ℝ) (bf : Nat → Bool) :
    ∃ n, Seg kernel Assumptions.all L g n 4329 (elemsF m bf sc) 4395
      [(7256, Assumption.erealValue .f32 (foldM m (bpe bf sc)))] := by
  obtain ⟨_, h⟩ := mask_fold L g m sc bf
  exact ⟨_, h.weaken_start fun R hR => cast (congrArg (Holds R) (by kernel_rfl)) hR⟩

/-- **The maximum the exponents subtract** (pcs 4395, 4396): the row maximum, or `0` when it is
`-∞`. -/
theorem sel_max (L : Launch) (g : Nat) {x : EReal} (hx : x < ⊤) :
    ∃ n, Seg kernel Assumptions.all L g n 4395 [(7256, Assumption.erealValue .f32 x)] 4397
      [(3685, selMax x), (7256, Assumption.erealValue .f32 x)] := by
  by_cases hb : x = ⊥
  · subst hb
    rw [show selMax ⊥ = .bits 32 (BitVec.ofNat 64 0) by simp [selMax], erealValue_bot]
    seg_sym using (soft_seg)
  · obtain ⟨r, rfl⟩ : ∃ r : ℝ, x = r := ⟨x.toReal, (EReal.coe_toReal hx.ne hb).symm⟩
    rw [show selMax (r : EReal) = .float .f32 r by
      simp [selMax, EReal.coe_ne_bot, erealValue_coe], erealValue_coe]
    seg_sym using (soft_seg)

/-! ### The chain -/

/-- The data registers at pc 3591: the bias halves and the score pairs. -/
def dataK1 : List Nat := List.range' 786 128 ++ List.range' 7303 64


theorem valueOf_narr_barr (v : V) {r : Nat} (hc : ctl r = true)
    (hr : ((valuesP1 p L g).map Prod.fst).contains r = false) :
    valueOfD p L g ⟨.narr .first, v, 0, []⟩ r = valueOfD p L g ⟨.barr false, v, 0, []⟩ r := by
  rw [valueOfD_ctl _ hc, valueOfD_ctl _ hc]
  have hn : (valuesP1 p L g).lookup r = none := by
    cases h : (valuesP1 p L g).lookup r with
    | none => rfl
    | some x =>
      have := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := Prod.fst) (mem_of_lookup h))
      rw [hr] at this; cases this
  simp only [valueOf, values, List.lookup_append, hn, Option.none_or]

theorem seg_start_ex {s b : Nat} {F F' G : List (Nat × Value)}
    (h : ∃ n, Seg kernel Assumptions.all L g n s F b G) (hF : ∀ R, Holds R F' → Holds R F) :
    ∃ n, Seg kernel Assumptions.all L g n s F' b G := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, h.weaken_start hF⟩

/-- The maximum, masked elements and carried control values determine the arrival facts. -/
theorem narr1_land (v : V) (R : Nat → Option Value)
    (hR : Holds R
      ([(3685, selMax (foldF p L g v)), (7256, Assumption.erealValue .f32 (foldF p L g v))] ++
        (elemsF (mcnt p L g v) (bpf v) (bps p v) ++
          factsFrom (ctlLive 3872) (vMc p L g v)))) :
    Holds R (factsD p L g ⟨.narr .first, v, 0, []⟩) := by
  obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
  obtain ⟨h2, h3⟩ := (holds_append _ _ _).mp h2
  have h3' : Holds R (factsFrom (ctlLive 4397) (valueOfD p L g ⟨.narr .first, v, 0, []⟩)) := by
    have hk : (ctlLive 4397).all (fun r => (ctlLive 3872).contains r && r != 3235) = true := by
      kernel_rfl
    refine holds_of_pointwise fun r hr => ?_
    have h := List.all_eq_true.mp hk r hr
    simp only [Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq] at h
    have := holds_mem h3 (mem_factsFrom h.1)
    rwa [vMc, Function.update_of_ne h.2] at this
  refine land_run (G := valuesNarr1 p L g v) (ctlK := ctlLive 4397)
    (valueOfD_prefix (d := ⟨.narr .first, v, 0, []⟩) (X := []) (by simp; rfl)
      (nodup_of_nodupB (by kernel_rfl)))
    (fun _ _ => rfl) (by kernel_rfl) ?_ h3'
  exact (show valuesNarr1 p L g v = [(3685, selMax (foldF p L g v)),
    (7256, Assumption.erealValue .f32 (foldF p L g v))] ++ elemsF (mcnt p L g v) (bpf v) (bps p v)
    from rfl) ▸ (holds_append _ _ _).mpr ⟨h1, h2⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
