-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Unpack
public import Kernels.InklingRelDecode.Proof.Epilogue.Steps.Store
public import Lemmas.Flow.StepsQFG

@[expose] public section

/-! # The strict step of the guarded word stores -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption Control
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

variable {e : Entry} {L : Launch} {g : Nat} {v : Value} {R : TState → Prop} {Wf : Event → Prop}

/-- Each store goes on at the next store (at the join after the last), through the unpack when it
is the odd one of a pair. -/
theorem store_pcs : ∀ j : Fin 64, (j.val % 2 = 1 ∧ j.val < 63) ∨
    (storeAt (j.val + 1)).pc = storePc j + 1 ∧
    (∀ r ∈ ctlLive (storePc j + 1), r ∈ ctlLive (storePc j)) := by decide +kernel

theorem store_afterF : ∀ j : Fin 64, afterF lateQt (storePc j) [] = true := by decide +kernel

theorem store_span (j : Fin 64) (R : TState → Prop) :
    SegQ kernel Assumptions.all L g (fun t => QTF lateQt t ∧ TauAll kernel Assumptions.all L g R t)
      (storePc j + 1) (facts e L g v (storePc j)) (storeAt (j.val + 1)).pc
      (facts e L g v (storeAt (j.val + 1)).pc) := by
  rcases store_pcs j with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨m, hm⟩ : ∃ m : Fin 31, j.val = 2 * m.val + 1 :=
      ⟨⟨j.val / 2, by omega⟩, by simp only []; omega⟩
    have e1 : storePc j = uPc m - 1 := by simp only [storePc, uPc, hm]; omega
    have e2 : (storeAt (j.val + 1)).pc = uPc m + 1 := by
      have hlt : j.val + 1 < 64 := by omega
      unfold storeAt
      simp only [hlt, ↓reduceDIte]
      simp only [Site.pc, storePc, uPc, hm]
      omega
    rw [e1, e2, show uPc m - 1 + 1 = uPc m by unfold uPc; omega]
    exact unpack_span m R
  · exact seg_step (p := storePc j) h1 h2

theorem sstep_store (j : Fin 64) (ev : Event) : (code e L g).StepForQP (QTF lateQt)
    (TauAll kernel Assumptions.all L g R) Wf ⟨.store j, v⟩ ev := by
  obtain ⟨fetch, -, -⟩ := store_checks j
  obtain ⟨a, hc, kind, len, -⟩ := store_fetch fetch
  refine Code.StepForQP.ofInv fun hinv => ?_
  exact Code.scalarStoreFP (C := code e L g) (d := ⟨.store j, v⟩) (dn := ⟨storeAt (j.val + 1), v⟩)
    hc kind len (fun _ => rfl) rfl rfl rfl rfl (store_inv v hinv _) (store_afterF j)
    (store_span j R) ev

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
