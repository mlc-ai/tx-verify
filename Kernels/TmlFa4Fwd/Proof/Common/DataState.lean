-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Projects
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Projects
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Numerics
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX.Flow
noncomputable section

variable {p : Params} {L : Launch} {g : Nat}

def eraseRole : (i : Role) → (fragD p L g i).D → (frag p L g i).D
  | .correction, d => Correction.Control.erase d
  | .softmax, d => Softmax.Control.erase d
  | .mma, d | .epilogue, d | .loader _, d | .stub _, d => d

def eraseDispatch : (gluedD p L g).D → (glued p L g).D
  | .inl s => .inl s
  | .inr ⟨i,d⟩ => .inr ⟨i,eraseRole i d⟩

def eraseThread (s : (threadD p L g).D) : (thread p L g).D := (eraseDispatch s.1,s.2)

private theorem erase_step {m} (hp : Pre p L m) {s s' : (threadD p L g).D} {e : Event}
    (h : (threadD p L g).next s e = some (some s')) :
    (thread p L g).next (eraseThread s) e = some (some (eraseThread s')) := by
  obtain ⟨s,n⟩ := s
  obtain ⟨a,n'⟩ := s'
  obtain ⟨hn,rfl⟩ := Code.counted_next_some (C := gluedD p L g) h
  suffices hn' : (glued p L g).next (eraseDispatch s) e = some (some (eraseDispatch a)) by
    change ((glued p L g).next (eraseDispatch s) e).map _ = _
    rw [hn']
    rfl
  cases s with
  | inl s =>
    obtain ⟨s',hs,rfl⟩ := Code.glue_inl_some hn
    change ((Startup.code p L g).next s e).map _ = _
    rw [hs]
    simp only [Option.map_some, Option.some.injEq]
    unfold Code.enter
    cases exit L g s' with
    | none => rfl
    | some i => cases i <;> rfl
  | inr a =>
    obtain ⟨i,d⟩ := a
    obtain ⟨d',hs,rfl⟩ := Code.glue_inr_some hn
    suffices h : (frag p L g i).next (eraseRole i d) e = some (some (eraseRole i d')) by
      change ((frag p L g i).next (eraseRole i d) e).map _ = _
      rw [h]
      rfl
    cases i with
    | correction => exact Correction.Control.projects d e d' hs
    | softmax =>
      change (SmWarp.codeT p L g).next d e = _ at hs
      rw [SmWarp.next_eq (SmWarp.numSteps hp)] at hs
      exact Softmax.Control.projects d e d' hs
    | _ => exact hs

/-- Up to its first stop, a value state determines the protocol state on the same trace. -/
theorem control_of_data {m X k} (hp : Pre p L m) {s : (threadD p L g).D}
    (hs : Frame.stateAt (threadD p L) X g k = some (some s)) :
    Frame.stateAt (thread p L) X g k = some (some (eraseThread s)) := by
  suffices transfer : ∀ (es : List Event) (a : (threadD p L g).D),
      (threadD p L g).toMachine.after (some a) es = some (some s) →
      (thread p L g).toMachine.after (some (eraseThread a)) es = some (some (eraseThread s)) from
    transfer _ _ hs
  intro es
  induction es with
  | nil =>
    intro a hs
    cases hs
    rfl
  | cons e es ih =>
    intro a hs
    change ((threadD p L g).next a e).bind _ = _ at hs
    change ((thread p L g).next (eraseThread a) e).bind _ = _
    rcases h : (threadD p L g).next a e with _ | _ | b
    · rw [h] at hs; cases hs
    · rw [h] at hs
      have dead : ∀ l, (threadD p L g).toMachine.after none l = some none := by
        intro l
        induction l with
        | nil => rfl
        | cons _ _ ih => exact ih
      change (threadD p L g).toMachine.after none es = _ at hs
      rw [dead] at hs
      cases hs
    · rw [h] at hs
      rw [erase_step hp h]
      exact ih _ hs

end
end PTX.Kernels.TmlFa4Fwd.Proof
