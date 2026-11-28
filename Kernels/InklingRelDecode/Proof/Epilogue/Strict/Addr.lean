-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Skip
public import Kernels.InklingRelDecode.Proof.Epilogue.Steps.Address

@[expose] public section

/-! # The strict address chain of the word stores

The exact stretch `addr_exact` (pcs 2683 to 2750, the values of the control facts) with one typed
check of the whole stretch from the tags at its start to the tags at its end. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption Control
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

variable {e : Entry} {L : Launch} {g : Nat} {v : Value}

theorem tail_ok : epiOk 2683 2750 = true ∧
    checkF absF5 lateQt 2683 2750 [] [] ((kernel.code.drop 2683).take (2750 - 2683)) = true := by
  decide +kernel

/-- The address words, strictly, up to the last unpack. -/
theorem tail_exact : SegQ kernel Assumptions.all L g (QTF lateQt) 2683 (facts e L g v 2683) 2750
    (facts e L g v 2750) :=
  segQF_of_seg_typed lateQt (Ft := []) (n := 67) addr_exact rfl (by decide +kernel)
    (by have := kernel_code_length; omega) (absF5_sound (fp3_epi tail_ok.1))
    (factTags_of_B (by rfl)) tail_ok.2

theorem last_ok : epiOk 2750 2751 = true ∧ (∀ r ∈ ctlLive 2751, r ∈ ctlLive 2750) ∧
    checkW absF5 lateQt 2750 2751 ((kernel.code.drop 2750).take 1)
      (wrF absF5 (lateQt 2750) ((kernel.code.drop 2750).take 1)) = true ∧
    ∀ r ∈ ctlLive 2751, r ∉ wrF absF5 (lateQt 2750) ((kernel.code.drop 2750).take 1) := by
  decide +kernel

/-- **The address chain**: the control facts after it are those of the exact stretch. -/
theorem tail_seg : SegQ kernel Assumptions.all L g (QTF lateQt) 2683 (facts e L g v 2683) 2751
    (facts e L g v 2751) := by
  obtain ⟨hp, hs, hc, hw⟩ := last_ok
  refine tail_exact.comp (segQF5_runW lateQt (by omega) ?_ (fp3_epi hp) hc ?_ ?_)
  · have := kernel_code_length
    omega
  · intro p hp'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp'
    exact hw r hr
  · intro p hp'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp'
    exact mem_factsFrom (hs r hr)

variable {R : TState → Prop} {Wf : Event → Prop}

/-- **The guarded LSE store** goes on, through the address chain, to the first word store. -/
theorem sstep_lse (ev : Event) : (code e L g).StepForQP (QTF lateQt)
    (TauAll kernel Assumptions.all L g R) Wf ⟨.lse, v⟩ ev := by
  obtain ⟨a, hc, kind, len, -⟩ := store_fetch (by decide +kernel : storeCheck 2682 174 = true)
  refine Code.StepForQP.ofInv fun hinv => ?_
  exact Code.scalarStoreFP (C := code e L g) (d := ⟨.lse, v⟩) (dn := ⟨.store 0, v⟩) hc kind len
    (fun _ => rfl) rfl rfl rfl rfl hinv.1
    (by change afterF lateQt 2682 [] = true; decide +kernel)
    (SegQ.tauAll R (SegQ.fromFacts (F' := facts e L g v 2683)
      (fsub (v := v) (p := 2682) (q := 2683) (by decide +kernel)) tail_seg)) ev

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
