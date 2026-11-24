-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DCompAll
public import Kernels.InklingRelDecode.Proof.Thread.WCompAll
public import Lemmas.Kernel.Frame

@[expose] public section

/-!
# The machine of every thread of the Inkling kernel

A thread of the launch is a default-partition thread (warps 0 to 3, `g % L.block < 128`), followed
by `DComp.code`, or a worker thread (warps 4 to 7), followed by `WComp.code`. The layers above the
thread layer follow every thread by one machine, `threadCode L g Q`: its abstract states are the
sum `TSt` of the two machines' states (`.d` and `.w`), its first state is the first state of the
thread's own machine (the default partition's if `g % L.block < 128`, else the worker's), and
its successor is the component's. So `threadCode` *is* the selected machine: the abstract state of
a default-partition thread before an event is `.d s` with `s` the state of `DComp.code` there
(`stateAt_default`), of a worker thread `.w s` with `s` the state of `WComp.code`
(`stateAt_worker`).

`ThreadSound` is the hypothesis under which every launched thread's machine is sound: `Pre`, and
for the default partition the softmax region's obligations `DComp.SmObligations` (the unfinished
score stage; the development notes, "thread-layer gaps"). Soundness gives the framework's facts
about a
consistent execution (`Frame.trace`, `Frame.fired`, `Frame.fired_site`): each event fires from the
state before it.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The abstract states of a thread: a state of the default partition's machine or of the
worker's. -/
inductive TSt where
  | d (s : DComp.St)
  | w (s : WComp.WSt)

/-- The assumptions every machine of the kernel evaluates under. -/
abbrev asms : List Assumption := Assumptions.all

/-- The thread is a default-partition thread: warps 0 to 3 of its CTA. -/
def IsDefault (L : Launch) (g : Nat) : Prop := g % L.block < 128

instance (L : Launch) (g : Nat) : Decidable (IsDefault L g) := by unfold IsDefault; infer_instance

/-- The program counter of a state: the component's (`Site.pc` of its machine). -/
def TSt.pc : TSt → Nat
  | .d s => DComp.pc s
  | .w s => WComp.pc s

/-- The registers live at a state. -/
def TSt.facts (L : Launch) (g : Nat) (Q : Params) : TSt → List (Nat × Value)
  | .d s => DComp.facts L g Q s
  | .w s => WComp.facts L g s

/-- The invariant of a state: the thread is of the state's kind (a default-partition thread has
default-partition states, a worker thread worker states) and the component's invariant holds. -/
def TSt.inv (L : Launch) (g : Nat) (Q : Params) : TSt → Prop
  | .d s => IsDefault L g ∧ DComp.Inv L g Q s
  | .w s => ¬ IsDefault L g ∧ WComp.Inv L g s

/-- The successor after event `e`: the component's. -/
def TSt.next (L : Launch) (g : Nat) (Q : Params) : TSt → Event → Option (Option TSt)
  | .d s, e => (DComp.next L g Q s e).map (Option.map TSt.d)
  | .w s, e => (WComp.next L g s e).map (Option.map TSt.w)

/-- **The machine of thread `g`**: the default partition's if `g % L.block < 128`, the worker's
otherwise. -/
@[reducible] def threadCode (L : Launch) (g : Nat) (Q : Params) : Flow.Code kernel asms L g where
  D := TSt
  init := if g % L.block < 128 then .d (DComp.code L g Q).init else .w (WComp.code L g Q).init
  pc := TSt.pc
  facts := TSt.facts L g Q
  sub := fun
    | .d s => DComp.sub s
    | .w s => WComp.sub s
  acc := fun
    | .d s => DComp.acc s
    | .w s => WComp.acc s
  inv := TSt.inv L g Q
  next := TSt.next L g Q

/-- The machine family of the launch. -/
abbrev code (L : Launch) (Q : Params) : (g : Nat) → Flow.Code kernel asms L g :=
  fun g => threadCode L g Q

variable {L : Launch} {g : Nat} {Q : Params} {mem0 : Mem0}

/-! ### The components' states are the machine's states -/

theorem atD_d {s : DComp.St} {t : TState} :
    (threadCode L g Q).AtD (.d s) t ↔ (DComp.code L g Q).AtD s t := Iff.rfl

theorem atD_w {s : WComp.WSt} {t : TState} :
    (threadCode L g Q).AtD (.w s) t ↔ (WComp.code L g Q).AtD s t := Iff.rfl

theorem next_d (s : DComp.St) (e : Event) :
    (threadCode L g Q).next (.d s) e = (DComp.next L g Q s e).map (Option.map TSt.d) := rfl

theorem next_w (s : WComp.WSt) (e : Event) :
    (threadCode L g Q).next (.w s) e = (WComp.next L g s e).map (Option.map TSt.w) := rfl

/-- A successor of `none` or `some none` under `Option.map` stays so. -/
theorem map_map_eq_some_some {α β : Type} {x : Option (Option α)} {f : α → β} {y : β}
    (h : x.map (Option.map f) = some (some y)) : ∃ a, x = some (some a) ∧ f a = y := by
  cases x with
  | none => simp at h
  | some o =>
    cases o with
    | none => simp at h
    | some a => exact ⟨a, rfl, by simpa using h⟩

/-! ### The obligations of a lifted machine -/

/-- A component's obligation at `s` is the thread machine's at the state that wraps it. -/
theorem stepAt_d {s : DComp.St} (h : IsDefault L g → (DComp.code L g Q).StepAt s) :
    (threadCode L g Q).StepAt (.d s) where
  site hi := (h hi.1).site hi.2
  step := by
    intro t e u ins ha hi hc hf
    rcases (h hi.1).step ins ha hi.2 hc hf with (hn | ⟨d', t', hn, hr, hg⟩) | ⟨hn, hd⟩
    · have hn' : DComp.next L g Q s e = some none := hn
      exact .inl (.inl (by rw [next_d, hn']; rfl))
    · have hn' : DComp.next L g Q s e = some (some d') := hn
      exact .inl (.inr ⟨.d d', t', by rw [next_d, hn']; rfl, hr, hg.1, hi.1, hg.2⟩)
    · have hn' : DComp.next L g Q s e = none := hn
      exact .inr ⟨by rw [next_d, hn']; rfl, hd⟩

theorem stepAt_w {s : WComp.WSt} (h : ¬ IsDefault L g → (WComp.code L g Q).StepAt s) :
    (threadCode L g Q).StepAt (.w s) where
  site hi := (h hi.1).site hi.2
  step := by
    intro t e u ins ha hi hc hf
    rcases (h hi.1).step ins ha hi.2 hc hf with (hn | ⟨d', t', hn, hr, hg⟩) | ⟨hn, hd⟩
    · have hn' : WComp.next L g s e = some none := hn
      exact .inl (.inl (by rw [next_w, hn']; rfl))
    · have hn' : WComp.next L g s e = some (some d') := hn
      exact .inl (.inr ⟨.w d', t', by rw [next_w, hn']; rfl, hr, hg.1, hi.1, hg.2⟩)
    · have hn' : WComp.next L g s e = none := hn
      exact .inr ⟨by rw [next_w, hn']; rfl, hd⟩

/-- **Every thread's machine is sound**: under `Pre`, for a launched thread, given the softmax
region's obligations when the thread is a default-partition thread. -/
theorem sound (hpre : Pre Q L mem0) (hg : g < L.threads)
    (hso : IsDefault L g → DComp.SmObligations Q L mem0 g) : (threadCode L g Q).Sound where
  start := by
    by_cases hd : g % L.block < 128
    · obtain ⟨t, hr, ha, hi⟩ := (DComp.sound hpre hg hd (hso hd)).start
      refine ⟨t, hr, ?_, ?_⟩
      · show (threadCode L g Q).AtD (if g % L.block < 128 then .d (DComp.code L g Q).init
          else .w (WComp.code L g Q).init) t
        simp only [hd, ↓reduceIte]
        exact ha
      · show (threadCode L g Q).inv (if g % L.block < 128 then .d (DComp.code L g Q).init
          else .w (WComp.code L g Q).init)
        simp only [hd, ↓reduceIte]
        exact ⟨hd, hi⟩
    · have hw : 4 ≤ WComp.warpOf L g := by
        show 4 ≤ Worker.warpOf L g
        unfold Worker.warpOf
        omega
      obtain ⟨t, hr, ha, hi⟩ := (WComp.sound (Q := Q) (mem0 := mem0) hpre hw).start
      refine ⟨t, hr, ?_, ?_⟩
      · show (threadCode L g Q).AtD (if g % L.block < 128 then .d (DComp.code L g Q).init
          else .w (WComp.code L g Q).init) t
        simp only [hd, ↓reduceIte]
        exact ha
      · show (threadCode L g Q).inv (if g % L.block < 128 then .d (DComp.code L g Q).init
          else .w (WComp.code L g Q).init)
        simp only [hd, ↓reduceIte]
        exact ⟨hd, hi⟩
  steps d := by
    cases d with
    | d s => exact stepAt_d fun hd => DComp.stepAt hpre hg (hso hd) s
    | w s => exact stepAt_w fun _ => WComp.stepAt hpre s

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
