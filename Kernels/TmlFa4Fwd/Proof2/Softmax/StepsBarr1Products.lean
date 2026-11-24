-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsBarr1

@[expose] public section

/-! # The first round's bias and score products

The opening pieces reach pc 3850 with the computed bias and score products. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue (andi scmpi)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The unpack and product run from pc 3591 to pc 3850. -/
theorem chain1_products (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 3591
    (factsFrom (liveD 3591) (valueOfD p L g ⟨.barr false, v, 0, []⟩)) 3850
    (Gen.prod1_facts9 (vProd1 p L g v) ++ factsFrom (ctlLive 3593) (vProd1 p L g v)) := by
  have p01 := seg_frame (lo := 3591) (hi := 4397)
    (H := factsFrom dataK1 (valueOfD p L g ⟨.barr false, v, 0, []⟩)) (ldp1 (g := g) hp v)
    (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  have hrun := Gen.prod1_run L g (vProd1 p L g v)
  have hframe := SegD.frame (H := factsFrom (ctlLive 3593) (vProd1 p L g v))
    Gen.rulesFrame hrun rfl (by kernel_rfl) (by kernel_rfl) (Gen.segFree_range (by kernel_rfl))
  have p12 := seg_of_segD hframe (prod1_ok hp v)
  -- 3591: the state's facts
  refine Seg.comp_ex (seg_start_ex p01 fun R hR => (holds_append _ _ _).mpr
    ⟨holds_sub hR (by kernel_rfl), holds_sub hR (by kernel_rfl)⟩) ?_
  -- 3593: the products' start facts
  exact seg_start_ex p12 fun R hR => by
    obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
    refine (holds_append _ _ _).mpr ⟨?_, h1⟩
    rw [prod1_facts0_eq]
    exact holds_upd (A := ctlLive 3593) (B := dataK1) h1 h2 (by kernel_rfl)

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
