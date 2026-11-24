-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.MmaSources

namespace PTX.Tests.MmaCompletionClosure
open PTX TcMma
noncomputable section
private def desc : Descriptor :=
  ⟨.two,.f16 .f16 .f32,256,256,false,false,false,false,false⟩
private def spec : OperandSpec :=
  ⟨desc,⟨0,0,1024,0,false,false,.b128⟩,⟨0,0,1024,0,false,false,.b128⟩,0,1,none,{}⟩
private def mask : List Nat := List.replicate 8 0
private def L : Launch := { grid := 1, block := 32, params := fun _ => none }
private def exampleTrace (secondMask : List Nat) : Nat →List Event := fun g =>
  if g=0 then [⟨0,.tc (.mma 0 spec false mask)⟩,⟨1,.tc (.mma 0 spec true secondMask)⟩] else []
private def pending : Execution := {tr := exampleTrace mask,rf := fun _ _ => none}
private def laterOnly : Execution :=
  {pending with async := {mmaDone := fun i => decide (i=(0,1))}}

private theorem sameWarp00 : SameWarp L 0 0 := by
  simp [SameWarp, SameCta, L, Launch.threads]

/-- Real identical nonempty write footprints instantiate the sufficient domain. -/
theorem precedes (X : Execution) (h : X.tr = exampleTrace mask) :
    CompletionPrecedes L X (0,0) (0,1) := by
  refine completionPrecedes_iff.mpr ⟨rfl,by decide,sameWarp00,
    ⟨0,spec,false,mask,0,spec,true,mask,⟨0,by simp [Execution.get,h,exampleTrace]⟩,
      ⟨1,by simp [Execution.get,h,exampleTrace]⟩,rfl,rfl,rfl,rfl,rfl⟩,
    0,spec,false,mask,0,spec,true,mask,⟨0,by simp [Execution.get,h,exampleTrace]⟩,
      ⟨1,by simp [Execution.get,h,exampleTrace]⟩,fun _ _ => rfl,0,0,⟨0,0,0⟩,?_⟩
  decide

example : CompletionPrecedes L pending (0,0) (0,1) := precedes pending rfl

/-- A missing earlier completion is rejected despite identical source issues. -/
example : ¬CompletionClosed L laterOnly := by
  intro hc
  have hh := hc (0,0) (0,1) (precedes laterOnly rfl) rfl
  cases hh

/-- Operand starts are not prerequisites of a start-only snapshot satisfying
this pure law; no arithmetic completion has occurred. -/
example : CompletionClosed L pending := by
  intro i j _ hj
  cases hj

/-- Different issuer threads are outside this intentionally narrow domain. -/
example : ¬CompletionPrecedes L pending (0,0) (1,1) := by
  intro h
  cases h.1

/-- Reversed source order does not create completion dependencies. -/
example : ¬CompletionPrecedes L pending (0,1) (0,0) := by
  intro h
  exact Nat.not_lt_zero _ h.2.1

/-- Changed masks cannot instantiate a whole-identical-footprint predecessor. -/
example : ¬CompletionPrecedes L ({tr := exampleTrace (List.replicate 8 1),rf := fun _ _ =>
                                   none} : Execution)
    (0,0) (0,1) := by
  intro h
  obtain ⟨-,-,-,-,d,s,a,m,d',s',a',m',⟨pc,hi⟩,⟨pc',hj⟩,heq,-⟩ := completionPrecedes_iff.mp h
  simp only [Execution.get,exampleTrace,↓reduceIte] at hi hj
  simp only [List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq,Event.mk.injEq,
    Kind.tc.injEq,TcKind.mma.injEq] at hi hj
  obtain ⟨-,rfl,rfl,rfl,rfl⟩ := hi
  obtain ⟨-,rfl,rfl,rfl,rfl⟩ := hj
  have h00 := heq 0 0
  revert h00
  decide

/-- Starting only the later operand reads does not force an earlier start. -/
example :
    let X : Execution := {pending with async :=
      {mmaOperands := fun i => if i=(0,1) then some ⟨[],[]⟩ else none}}
    CompletionClosed L X ∧ X.async.mmaStarted (0,1)=true ∧
      X.async.mmaOperands (0,0)=none := by
  refine ⟨?_,rfl,rfl⟩
  intro i j _ hj
  cases hj

/-- Different accumulator addresses do not instantiate this predecessor. -/
example : ¬CompletionPrecedes L
    ({tr := fun g => if g=0 then
      [⟨0,.tc (.mma 0 spec false mask)⟩,⟨1,.tc (.mma 256 spec true mask)⟩] else [],
      rf := fun _ _ => none} : Execution) (0,0) (0,1) := by
  intro h
  obtain ⟨-,-,-,⟨d,s,a,m,d',s',a',m',⟨pc,hi⟩,⟨pc',hj⟩,hsa⟩,-⟩ := completionPrecedes_iff.mp h
  have hleft := congrArg Event.kind (Option.some.inj hi)
  have hright := congrArg Event.kind (Option.some.inj hj)
  simp only [Kind.tc.injEq,TcKind.mma.injEq] at hleft hright
  have := hsa.1
  omega

end
end PTX.Tests.MmaCompletionClosure
