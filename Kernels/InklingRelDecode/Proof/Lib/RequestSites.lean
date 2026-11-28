-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.NotRegister
import Kernels.InklingRelDecode.Flow.Code.Part044

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

/-- The positions of the `setmaxnreg` instructions. -/
def requestPcs : List Nat := [27,574,2333,2336,2337,2344,2420,2422,2555,2847]

/-- The direction and count of the `setmaxnreg` at a position. -/
def requestAt (pc : Nat) : Option (Bool × Nat) :=
  match kernel.code[pc]? with
  | some ins => match ins.op with
    | .setMaxReg inc n => some (inc,n)
    | _ => none
  | none => none

def reqCheckSite (x : Instr × Nat) : Bool :=
  match x.1.op with
  | .setMaxReg _ n => decide (x.2 ∈ requestPcs) && SetMaxNReg.validCount n
  | _ => !decide (x.2 ∈ requestPcs)

theorem reqChecked : kernel.code.zipIdx.all reqCheckSite = true := by decide +kernel

/-- A step fired at a position produces a request exactly at the listed positions, with the
direction and count of the instruction. -/
theorem request_fires {A L g t pc e o ins} (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl A L g t ins.op) e o) :
    SetMaxNReg.isRequest e = decide (pc ∈ requestPcs) ∧
      ∀ inc n inst, e.kind = .setMaxReg inc n inst → requestAt pc = some (inc,n) := by
  have h := List.all_eq_true.mp reqChecked (ins,pc) (List.mem_zipIdx_iff_getElem?.mpr hc)
  have key : requestAt pc = match ins.op with | .setMaxReg inc n => some (inc,n) | _ => none := by
    simp only [requestAt,hc]
    rfl
  simp only [reqCheckSite] at h
  cases hop : ins.op with
  | setMaxReg inc n =>
    rw [hop] at h hf
    simp only [Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨inst,rfl⟩ := fires_of_setMaxReg_op h.2 hf
    refine ⟨by simp [SetMaxNReg.isRequest,h.1],fun i m _ hk => ?_⟩
    simp only [Kind.setMaxReg.injEq] at hk
    obtain ⟨rfl,rfl,-⟩ := hk
    simp [key,hop]
  | _ =>
    have none_ : ∀ inc n inst, e.kind ≠ .setMaxReg inc n inst := fun inc n inst hk => by
      have := fires_setMaxReg_op hf hk
      rw [hop] at this
      cases this
    have not_ : pc ∉ requestPcs := by
      rw [hop] at h
      simpa using h
    refine ⟨?_,fun inc n inst hk => (none_ inc n inst hk).elim⟩
    obtain ⟨p,k⟩ := e
    cases k <;> simp [SetMaxNReg.isRequest,not_]
    rename_i inc n inst
    exact none_ inc n inst rfl

end PTX.Kernels.InklingRelDecode.Proof.Lib
