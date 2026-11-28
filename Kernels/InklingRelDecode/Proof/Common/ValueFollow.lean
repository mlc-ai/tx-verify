-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.ValueThread
public import Lemmas.Kernel.StateMap
import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.StartupEvents

@[expose] public section

/-! # A followed control state has a value state

`threadD` is the control thread machine with the value machines in the slots of the data roles;
the value machine follows what the control machine does (`threadD_next`), so the value machine's
states along a trace are the control machine's with the value fields (`value_state`). -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof Control

variable {Q : Params} {L : Launch} {g : Nat}

/-- The thread state of the prologue's value machine. -/
abbrev proDState (w : Value) (d : Prologue.Data.D) (n : Cls → Nat) : (threadD Q L g).D :=
  (.inr ⟨.inl (.prologue w), .inl d⟩, n)

theorem threadD_next (s : (threadD Q L g).D) (e : Event) :
    ((threadD Q L g).next s e).map (Option.map (eraseThread Q L g)) =
      (thread Q L g).next (eraseThread Q L g s) e := by
  symm
  obtain ⟨a, n⟩ := s
  rcases a with b | ⟨j | r, x⟩
  · simp only [thread, threadD, eraseThread, Code.roleThread, Code.counted, Code.glue,
      Code.eraseSum]
    rcases Startup.succ L g b e with _ | _ | c
    · rfl
    · rfl
    · simp only [Option.map_some]
      unfold Code.enter
      cases hx : Code.gatedExit (P := Startup.code Q L g) Startup.enterOf (sel L g) c with
      | none => rfl
      | some j =>
        rcases j with i | r
        · simp only [eraseThread, Code.eraseSum, Code.eraseStubs]
          rw [(frag_erases Q L g i).init]
        · rfl
  · cases j with
    | dispatch w x' =>
      simp only [thread, threadD, eraseThread, Code.roleThread, Code.counted, Code.glue,
        Code.withStubs, frag, fragD, eraseFrag, Code.eraseSum, Code.eraseStubs]
      rcases (workerCode Q L g w x').next x e with _ | _ | c <;> simp <;> rfl
    | prologue w =>
      simp only [thread, threadD, eraseThread, Code.roleThread, Code.counted, Code.glue,
        Code.withStubs, frag, fragD, eraseFrag, Code.eraseSum, Code.eraseStubs]
      simp only [dataErase, Code.eraseSumH, dataCode, dataDCode]
      rcases x with d | ⟨en, y⟩
      · rcases hn : Prologue.Control.next Q L g d.c e with _ | _ | c
        · simp [Prologue.Data.succ, prologueErase, hn]
        · simp [Prologue.Data.succ, prologueErase, hn]; rfl
        · simp only [Prologue.Data.succ, prologueErase, hn, Option.map_some]
          unfold Code.enter
          cases hx : dataExit Q L g w c <;> simp only [hx] <;> rfl
      · rcases y with y | ⟨u, y⟩
        · rcases hn : Softmax.Control.next en L g y.c e with _ | _ | c
          · simp [Softmax.Data.succ, softErase, softmaxErase, Code.eraseSumH, hn]
          · simp [Softmax.Data.succ, softErase, softmaxErase, Code.eraseSumH, hn]
          · simp only [Softmax.Data.succ, softErase, softmaxErase, Code.eraseSumH, hn,
              Option.map_some]
            unfold Code.enter
            cases hx : epiExit c <;> simp only [hx] <;> rfl
        · rcases hn : Epilogue.Control.next (epiEntry en (g % L.block)) L g y e with _ | _ | c <;>
            simp [softErase, epilogueErase, Code.eraseSumH, hn]
          rfl
  · rfl

/-- **A followed control state has a value state**: the value machine follows what the control
machine does. -/
theorem threadD_stepMap :
    Frame.StepMap (threadD Q L) (thread Q L) (fun g => eraseThread Q L g) where
  init g := (thread_erases Q L g).init
  next _ d e := threadD_next d e

theorem value_state {X : Execution} {k : Nat} {c : (thread Q L g).D}
    (h : Frame.stateAt (thread Q L) X g k = some (some c)) :
    ∃ s, Frame.stateAt (threadD Q L) X g k = some (some s) ∧ eraseThread Q L g s = c := by
  have hm := Frame.stateAt_map (threadD_stepMap (Q := Q) (L := L)) X g k
  rw [h] at hm
  rcases hs : Frame.stateAt (threadD Q L) X g k with _ | _ | s <;> rw [hs] at hm <;>
    simp only [Option.map_some, Option.map_none, reduceCtorEq, Option.some.injEq] at hm
  exact ⟨s, rfl, hm⟩


end PTX.Kernels.InklingRelDecode.Proof
