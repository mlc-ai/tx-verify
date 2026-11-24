-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorRld0
import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorRld1
import Lemmas.Flow.LoadFrameU

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {g : Nat}

/-- Every rescale load issues its implicit wait with the shape and control registers intact. -/
theorem stepAt_rldU (st : Fin 2) (c : Fin 8) (v : V) :
    (code p L g).StepAtU ⟨.rld st c, v, 0⟩ := by
  have h : loadOk (.rld st c) (.rldw st c) true = true := by
    fin_cases st
    · exact rld_table0 c
    · exact rld_table1 c
  obtain ⟨ds, ta, hc, hw, hframe⟩ := load_of_ok h
  refine ⟨fun _ => ⟨_, hc, rfl, trivial⟩, ?_⟩
  intro t e u ins hat _ hins hf
  obtain ⟨hpcAt, hsubAt, haccAt, hfaultAt, hregsAt⟩ := hat
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain ⟨a, vals, rfl, rfl⟩ := fires_tcLd_loadU (fun s he => by cases he)
    (hpcAt ▸ hw) hsubAt hf
  obtain ⟨hpcSet, hsubSet, haccSet, hfaultSet⟩ := setRegs_skel (PTX.next t) ds vals
  refine .inl (.inr ⟨⟨.rldw st c, v, 1⟩, _, rfl, .refl, .inl ⟨?_, .inr rfl⟩⟩)
  exact ⟨hpcAt, rfl, haccSet.trans haccAt, hfaultSet.trans hfaultAt,
    holds_after_tcLd (t := t) (vs := vals) hregsAt hframe⟩

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
