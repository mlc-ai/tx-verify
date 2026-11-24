-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsMaxB
public import Kernels.TmlFa4Fwd.Proof2.Softmax.Scales
public import Kernels.TmlFa4Fwd.Proof2.Lib.MulEReal

@[expose] public section

/-! # The bias round's keep test

From the maximum `%r3500` (pc 5666) to the statistics store (pc 5682): the test whether the
maximum is `-∞`, the scaled difference to the maximum before the round, its `ex2`, the keep test,
the row maximum, the maximum the exponents subtract and the rescaling factor. The walk runs once
per kind of the maximum before the round and of the fold (finite, or `-∞` when the maximum
before the round is `-∞` and every bias half is masked), so that every value it reads has one
form. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option seg_sym.decideHeartbeats 40000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-! ### The fold's kind -/

theorem le_foldB (x0 : EReal) (e : Nat → EReal) : x0 ≤ foldB x0 e := by
  simp only [foldB, le_max_iff, le_refl, true_or]

theorem foldB_lt_top {x0 : EReal} {e : Nat → EReal} (h0 : x0 < ⊤) (he : ∀ n, e n < ⊤) :
    foldB x0 e < ⊤ := by
  simp only [foldB, max_lt_iff, h0, he, and_self]

theorem bpeB_lt_top (p : Params) (v : V) (n : Nat) : bpeB p v n < ⊤ := by
  simp only [bpeB, bpe]
  split
  · exact EReal.coe_lt_top _
  · exact bot_lt_top

theorem foldBE_lt_top (p : Params) (v : V) : foldBE p v < ⊤ := by
  refine foldB_lt_top ?_ (bpeB_lt_top p v)
  simp only [mxE]
  split
  · exact EReal.coe_lt_top _
  · exact bot_lt_top

/-- With a finite maximum before the round, the fold is the number `foldBR`. -/
theorem foldBE_real {v : V} (hm : v.mf = true) : foldBE p v = ((foldBR p v : ℝ) : EReal) := by
  have h1 : (v.mr : EReal) ≤ foldBE p v := by
    have := le_foldB (mxE v) (bpeB p v)
    simpa [foldBE, mxE, hm] using this
  exact (EReal.coe_toReal (foldBE_lt_top p v).ne
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1)).symm

/-! ### The walks -/

/-- The registers live at the statistics store other than the three the keep test writes. -/
def keepKeys : List Nat :=
  [441, 634, 637, 1062, 1069, 1215, 1229, 1230, 1359, 1361, 2390, 2535, 4571, 5127, 6495, 6497,
   7132, 7248, 7249, 7250, 7253, 7257, 7258, 7500, 7501, 7502, 7503, 7506, 7896, 8317, 8319, 8321,
   8323, 8325, 8327, 8329, 8331, 8333, 8335, 8337, 8339, 8341, 8343, 8345, 8347, 8349, 8351, 8353,
   8355, 8357, 8359, 8361, 8363, 8365, 8367, 8369, 8371, 8373, 8375, 8377, 8379, 8381, 8383, 8385,
   8387, 8389, 8391, 8393, 8395, 8397, 8399, 8401, 8403, 8405, 8407, 8409, 8411, 8413, 8415, 8417,
   8419, 8421, 8423, 8425, 8427, 8429, 8431, 8433, 8435, 8437, 8439, 8441, 8443]

theorem keepKeys_eq :
    keepKeys = (liveD 5682).filter fun r => r != 7256 && r != 4565 && r != 1362 := by
  kernel_rfl

/-- The registers live at pc 5666 other than the maximum. -/
def startKeys : List Nat :=
  [441, 634, 1062, 1069, 1215, 1229, 1230, 1359, 1361, 2390, 2535, 5127, 6495, 6497, 7132, 7248,
   7249, 7250, 7251, 7253, 7257, 7258, 7500, 7501, 7502, 7503, 7506, 7896, 8317, 8319, 8321, 8323,
   8325, 8327, 8329, 8331, 8333, 8335, 8337, 8339, 8341, 8343, 8345, 8347, 8349, 8351, 8353, 8355,
   8357, 8359, 8361, 8363, 8365, 8367, 8369, 8371, 8373, 8375, 8377, 8379, 8381, 8383, 8385, 8387,
   8389, 8391, 8393, 8395, 8397, 8399, 8401, 8403, 8405, 8407, 8409, 8411, 8413, 8415, 8417, 8419,
   8421, 8423, 8425, 8427, 8429, 8431, 8433, 8435, 8437, 8439, 8441, 8443]

theorem startKeys_eq : startKeys = (PTX.Kernels.TmlFa4Fwd.Flow.live 5666).filter (· != 4560) := by
  kernel_rfl

/-- The facts at pc 5666 other than the maximum's. -/
abbrev keepStart (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  factsFrom startKeys (valueOfD p L g (statB v))

/-- **A finite maximum before the round.** -/
theorem keep_t (hp : Pre p L m) (sc ukw nb bt bpar spar ppar pl sv bk br mr rs) :
    ∃ n, Seg kernel Assumptions.all L g n 5666
      ((4560, .float .f32
          (foldBR p ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, true, mr, rs⟩)) ::
        keepStart p L g ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, true, mr, rs⟩)
      5682
      (factsD p L g (statB ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, true, mr, rs⟩)) := by
  have hparams := params hp
  obtain ⟨hw, hs⟩ := scl_word hp
  have hm := mulEReal_coe_bot_pos hs
  seg_sym using (soft_seg)

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
