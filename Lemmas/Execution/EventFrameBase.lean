-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.TensorMulticast
public import Core.Thread.Run
public import Aesop

@[expose] public section

namespace PTX.EventFrame
open PTX
noncomputable section

/-- A property of all returning event callbacks. Exit and UB have no callback. An atomic
read-modify-write whose write fails still returns its thread, with the fault recorded, so the frame
covers that state as well. -/
def CallbackFrame (P : TState → Prop) : Tmpl → Prop
  | .setMaxReg _ _ t | .warpBar _ t | .write _ _ t | .bar _ t _ _ | .cluster _ t
  | .clcQuery _ _ t | .clcIssue _ _ t | .tensorIssue _ _ t | .tensorStore _ _ t
  | .bulkCommit t | .bulkWait _ _ t | .fence _ _ t | .fenceProxy _ _ t | .fenceMbarInit t
  | .mbInit _ _ t | .mbInval _ t | .arrive _ _ t _ _ _ | .copy _ t | .bulkPrefetch _ t
  | .asyncCommit t | .asyncWait _ t | .asyncArrive _ _ t | .tc _ t | .tcAllocStore _ t
  | .tensorPrefetch _ _ t => P t
  | .elect _ k => ∀ v, P (k v)
  | .read _ k | .readNC _ k => ∀ v, P (k v)
  | .shfl _ _ _ _ k => ∀ v b, P (k v b)
  | .vote _ _ k => ∀ v, P (k v)
  | .voteMode _ _ _ k => ∀ v, P (k v)
  | .redux _ _ _ _ k => ∀ v, P (k v)
  | .match_ _ _ _ _ k => ∀ v b, P (k v b)
  | .activemask k => ∀ v, P (k v)
  | .matrix _ _ k => ∀ v, P (k v)
  | .wait _ _ k _ _ => ∀ b, P (k b)
  | .tcLd _ _ _ k => ∀ vs, P (k vs)
  | .sreg _ k => ∀ v, P (k v)
  | .rmw _ _ k => ∀ v, P (k v) ∧ ∀ f, P { k v with fault := some f }
  | .exit | .ub _ => True

abbrev ReturnedFrame (pc : Nat) : Tmpl → Prop :=
  CallbackFrame (fun u => u.pc=pc ∨ u.pc=pc+1)

def AllOk {α : Type} (P : α → Prop) : Exec α → Prop
  | .error _ => True
  | .ok v => P v

theorem allOk_bind {α β : Type} {P : β → Prop} {r : Exec α} {f : α → Exec β}
    (h : ∀ a, AllOk P (f a)) : AllOk P (r >>= f) := by
  cases r with
  | error => trivial
  | ok a => exact h a

theorem allOk_ite {α : Type} {P : α → Prop} {c : Prop} [Decidable c] {r₁ r₂ : Exec α}
    (h₁ : AllOk P r₁) (h₂ : AllOk P r₂) : AllOk P (if c then r₁ else r₂) := by
  by_cases hc : c
  · rwa [ite_eq_left hc]
  · rwa [ite_eq_right hc]

theorem ofExec_frame {P : TState → Prop} {r : Exec Tmpl}
    (h : AllOk (CallbackFrame P) r) : CallbackFrame P (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

theorem setRegs_pc (t : TState) (ds : List Nat) (vs : List Value) :
    (setRegs t ds vs).pc = t.pc := by
  induction ds generalizing t vs with
  | nil => rfl
  | cons d ds ih =>
    cases vs with
    | nil => rfl
    | cons v vs => exact ih (setReg t d v) vs

theorem afterLoad_pc (t : TState) (ds : List Nat) (bs : List (Option Byte)) :
    (afterLoad t ds bs).pc=t.pc ∨ (afterLoad t ds bs).pc=t.pc+1 := by
  unfold afterLoad
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem afterStore_pc (t : TState) (srcs : List Opnd) :
    (afterStore t srcs).pc=t.pc ∨ (afterStore t srcs).pc=t.pc+1 := by
  unfold afterStore
  split
  · exact Or.inl rfl
  · exact Or.inr rfl


end
end PTX.EventFrame
