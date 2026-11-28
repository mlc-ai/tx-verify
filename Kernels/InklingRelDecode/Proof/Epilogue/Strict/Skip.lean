-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Store

@[expose] public section

/-! # A masked output row skips every store, strictly -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption Control
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

variable {e : Entry} {L : Launch} {g : Nat} {v : Value}

theorem skip_tags : ∀ j : Fin 64,
    tagsInF (lateQt (storePc j + 1)) (lateQt (storePc j)) = true := by decide +kernel

/-- **The stores of a masked row** are skipped one by one, to the join. -/
theorem skip_stores (R : TState → Prop) (off : e.valid = false) {n : Nat} (bound : n ≤ 64) :
    SegQ kernel Assumptions.all L g (fun t => QTF lateQt t ∧ TauAll kernel Assumptions.all L g R t)
      (storeAt n).pc (facts e L g v (storeAt n).pc) (storeAt 64).pc
      (facts e L g v (storeAt 64).pc) := by
  induction bound using Nat.decreasingInduction with
  | self => exact SegQ.weaken fun _ h => h
  | of_succ k hk ih =>
    let j : Fin 64 := ⟨k, hk⟩
    obtain ⟨fetch, key, -⟩ := store_checks j
    obtain ⟨a, ins, -, -, -⟩ := store_fetch fetch
    have val : valueOf e L g v 175 = .pred false := congrArg Value.pred off
    have skip := SegQF.skipG (A := Assumptions.all) (L := L) (g := g) (qt := lateQt)
      (G := facts e L g v (storePc j)) ins
      (fun _ hR => holds_mem hR (mem_factsFrom_eq key val)) rfl (fun _ h => h) (skip_tags j)
    have e1 : (storeAt k).pc = storePc j := by simp [storeAt, hk, j, Site.pc]
    rw [e1]
    exact ((SegQ.tauAll R skip).comp (store_span (v := v) j R)).comp ih

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
