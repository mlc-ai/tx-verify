-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.QueryAll
public import Kernels.InklingRelDecode.Proof.Prologue.Checked

@[expose] public section

/-! # The value machine's step obligations -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow

/-- **Every state of the prologue's value machine** takes its step: the control machine's, and the
data step. -/
theorem step_at {Q L m g w} (hp : Pre Q L m) (d : D) : (code Q L g w).StepAtU d :=
  (over Q L g w).stepAtU (fun c => Control.checked_stepAt hp c) (data_step_all hp d)

/-- **The scale fact** is held at every site, the exit among them, for the Softmax entry. -/
theorem scale_mem {Q L g} (d : D) : scaleFact L ∈ dF Q L g d :=
  List.mem_map.mpr ⟨.scale, List.mem_cons_self .., rfl⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
