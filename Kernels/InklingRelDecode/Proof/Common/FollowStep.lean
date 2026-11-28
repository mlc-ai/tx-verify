-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Roles
import Kernels.InklingRelDecode.Proof.Dispatch.Nc
import Kernels.InklingRelDecode.Proof.Loader.Nc
import Kernels.InklingRelDecode.Proof.Mma.Nc
import Kernels.InklingRelDecode.Proof.Prologue.Nc
import Kernels.InklingRelDecode.Proof.Softmax.Nc
import Kernels.InklingRelDecode.Proof.Epilogue.Nc

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- A transition ends the lane or continues at an active site of the glue. -/
def AdvancesIn {α : Type} (P : α → Prop) : Option (Option α) → Prop
  | none => True
  | some none => False
  | some (some d) => P d

theorem advances_map {α β : Type} {P : β → Prop} {f : α → β} {o : Option (Option α)}
    (h : o ≠ some none) (hf : ∀ d, P (f d)) : AdvancesIn P (o.map (Option.map f)) := by
  rcases o with _ | _ | d
  · trivial
  · exact (h rfl).elim
  · exact hf d

theorem advances_lift {α β : Type} {P : α → Prop} {R : β → Prop} {f : α → β}
    {o : Option (Option α)} (h : AdvancesIn P o) (hf : ∀ d, P d → R (f d)) :
    AdvancesIn R (o.map (Option.map f)) := by
  rcases o with _ | _ | d
  · trivial
  · exact h.elim
  · exact hf d h

def WorkerActive {Q L g w x} : (workerCode Q L g w x).D → Prop
  | .inl d => d.site ≠ .loaderEntry ∧ d.site ≠ .mmaEntry
  | .inr ⟨.loader _,d⟩ => d.site ≠ .dispatch
  | .inr ⟨.mma _,d⟩ => d.site ≠ .dispatch

private theorem dispatch_enter {Q L g w x} (d : Dispatch.D) : WorkerActive
    (Code.enter (Dispatch.code L g (startRegs Q L g w x) x 0) (workerFrag Q L g w x)
      workerEntry d) := by
  obtain ⟨s,n⟩ := d
  cases s <;> first | exact ⟨nofun,nofun⟩ | exact nofun

private theorem worker_back {Q L g w x} (i : Worker) (d : (workerFrag Q L g w x i).D) :
    WorkerActive (Code.backEnter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry (workerBack Q L g w x) i d) := by
  unfold Code.backEnter
  split
  · apply dispatch_enter
  · rename_i h
    cases i <;> simp only [workerBack,ite_eq_right_iff,reduceCtorEq,imp_false] at h <;> exact h

theorem worker_advances {Q L g w x} (d : (workerCode Q L g w x).D) (e : Event)
    (h : WorkerActive d) : AdvancesIn WorkerActive ((workerCode Q L g w x).next d e) := by
  rcases d with d | ⟨i,d⟩
  · exact advances_map (Dispatch.no_stop h) dispatch_enter
  · apply advances_map _ (worker_back i)
    cases i with
    | loader => exact Loader.no_stop h
    | mma => exact Mma.no_stop h

def DataActive {Q L g w} : (dataCode Q L g w).D → Prop
  | .inl d => d.site ≠ .exit
  | .inr ⟨_,.inl d⟩ => d.site ≠ .epilogue
  | .inr ⟨_,.inr _⟩ => True

private theorem data_enter {Q L g w} (d : Prologue.Control.D) :
    DataActive (Code.enter (Prologue.Control.checkedCode Q L g w) (fun e => softCode e L g)
      (dataExit Q L g w) d) := by
  by_cases h : d.site = .exit
  · rw [Code.enter_some (i := dataEntry Q L g w d) (by simp [dataExit,h])]
    exact nofun
  · rw [Code.enter_none (by simp [dataExit,h])]
    exact h

private def SoftActive {ent L g} : (softCode ent L g).D → Prop
  | .inl d => d.site ≠ .epilogue
  | .inr _ => True

private theorem soft_advances {ent L g} (d : (softCode ent L g).D) (e : Event)
    (h : SoftActive d) : AdvancesIn SoftActive ((softCode ent L g).next d e) := by
  rcases d with d | ⟨⟨⟩,d⟩
  · apply advances_map (Softmax.Control.no_stop h)
    intro d'
    by_cases hx : d'.site = .epilogue
    · rw [Code.enter_some (i := ()) (by simp [epiExit,hx])]
      trivial
    · rw [Code.enter_none (by simp [epiExit,hx])]
      exact hx
  · exact advances_map Epilogue.Control.no_stop (fun _ => trivial)

theorem data_advances {Q L g w} (d : (dataCode Q L g w).D) (e : Event)
    (h : DataActive d) : AdvancesIn DataActive ((dataCode Q L g w).next d e) := by
  rcases d with d | ⟨ent,d⟩
  · exact advances_map (Prologue.Control.no_stop h) data_enter
  · have hx : SoftActive d := by cases d <;> exact h
    apply advances_lift (β := (dataCode Q L g w).D) (soft_advances d e hx)
      (f := fun d' => .inr ⟨ent,d'⟩)
    intro t ht
    cases t <;> exact ht

end
end PTX.Kernels.InklingRelDecode.Proof
