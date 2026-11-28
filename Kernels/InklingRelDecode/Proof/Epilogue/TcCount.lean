-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine
public import Kernels.InklingRelDecode.Proof.Lib.TcDataEvent

@[expose] public section

/-! # The `tcgen05` data events of the epilogue

The epilogue loads the O tile (`tcgen05.ld` at pc 2607 and its wait at pc 2608) unless the launch
has no block (`Entry.skip`). `epiCount skip s P` is the number of events at the data position `P`
before the thread at site `s`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue
open _root_.PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control

/-- The sites after the O load. -/
def afterLoad : Site → Bool
  | .wait | .shfl | .load => false
  | _ => true

/-- The sites after the wait for the O load. -/
def afterWaitLd : Site → Bool
  | .wait | .shfl | .load | .waitLd => false
  | _ => true

/-- The number of events at the data position `P` before site `s`. -/
def epiCount (skip : Bool) (s : Site) (P : Nat) : Nat :=
  if skip then 0
  else if P = 2607 then (afterLoad s).toNat
  else if P = 2608 then (afterWaitLd s).toNat
  else 0

/-- The load's sites are reached only when the load is not skipped. -/
def Live (e : Entry) (s : Site) : Prop := (s = .shfl ∨ s = .load ∨ s = .waitLd) → e.skip = false

theorem count_next {e L g d ev dn} (P : Nat) (hP : P = 2607 ∨ P = 2608) (live : Live e d.site)
    (step : Control.next e L g d ev = some (some dn)) :
    epiCount e.skip dn.site P = epiCount e.skip d.site P + (d.site.pc == P).toNat ∧
      Live e dn.site := by
  obtain ⟨s,v⟩ := d
  unfold Live at live ⊢
  cases s <;> simp only [Control.next,firstStore,storeAt] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals simp only [epiCount,afterLoad,afterWaitLd,Site.pc] at live ⊢
  all_goals rcases hP with rfl|rfl
  all_goals simp (config := {decide := true}) at live ⊢
  all_goals first | omega | (simp only [storePc]; omega) | simp_all

end PTX.Kernels.InklingRelDecode.Proof.Epilogue
