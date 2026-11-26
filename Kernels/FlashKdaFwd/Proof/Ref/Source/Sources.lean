-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Source.State
public import Kernels.FlashKdaFwd.Proof.Ref.Source.Tile
public import Lemmas.Step.TensorDrain

@[expose] public section

/-! # The tensor loads of an execution: sources fixed, frame, bounds

The kernel issues two families of tensor loads: the sixteen loads of the initial state
(`stateSpec P L g j`, `State.lean`) and the 70 loads of each tile (`tileLoad P L g tt p`,
`Tile.lean`). This file states for a whole execution what the two files prove per copy.

* `LoadShapes P L X`: **the hypothesis**: every tensor load issue of the execution is, for its
  issuing thread `g`, the copy `stateSpec P L g j` of a `j < 16` or the copy
  `tileLoad P L g tt p` of a tile `tt` of the thread's sequence and a position `p < 70`. It
  follows from the exports of the two phases that issue loads (`Ref/Startup/Exports.lean:
  issue_startup`, `Ref/Producer/Exports.lean: full_issue_producer`) once the assembly knows in
  which phase a thread is at an issue; no other phase has a tensor load.
* `load_input`: every global byte a load of the execution reads is a launch input byte.
* **`tensorSources`**: the progress premise `TensorSources L mem0 X`
  (`Lemmas/Step/TensorDrain.lean`): every load is routed to its block, has a valid descriptor
  and a non-empty box, and every global byte it reads has a launch value that no write of the
  execution covers. The last part uses `WriteFrame P X` (every global write is to an output
  array) and the precondition's separation of the outputs from the inputs.
* `loads_readFrame`: the tensor-load part of `DirectFacts.globalReadFrame` (`Proof/Top/Wire.lean`):
  the byte a load's source read touches is allocated and is no output and no final-state byte.
* `loads_fill`, `loads_bounds`: the fields `loadFill` and `loadBounds` of `DirectFacts`, with
  their statements (a load fills with zero through a map whose elements are no 64-bit floats;
  a load that selects an element outside its tensor is a load of `v` or of `beta`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Source
open PTX TensorDescriptor
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup (stateSpec)
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer (tileLoad tilesOf)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every tensor load of the execution is a load of the initial state or a load of a tile**
of its issuing thread: the copy `stateSpec P L g j` of a `j < 16`, or the copy
`tileLoad P L g tt p` of a tile `tt` of the thread's sequence and a position `p < 70`. -/
def LoadShapes (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ i al sp, X.TensorIssue i al sp →
    (∃ j < 16, sp = stateSpec P L i.1 j) ∨
      ∃ tt < tilesOf P i.1, ∃ p < 70, sp = tileLoad P L i.1 tt p

/-- **Every global byte a load of the execution reads is a launch input byte.** -/
theorem load_input (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hS : LoadShapes P L X) {i : EvId} {al : Nat} {sp : TensorCopy.Spec}
    (hi : X.TensorIssue i al sp) {x y z : Nat} {l : Loc}
    (h : TensorCopy.readLoc sp x y z = some l) : InputByte P mem0 l := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, hget⟩ := hi
  have hg : g < L.threads := Frame.lt_of_get hX hget
  rcases hS (g, k) al sp ⟨pc, hget⟩ with ⟨j, hj, rfl⟩ | ⟨tt, htt, p, hp, rfl⟩
  · exact stateSpec_input hpre hg hj h
  · exact tileLoad_input hpre hg htt hp h

/-- **The progress premise `TensorSources`**: every tensor load of the execution is routed to
its block, has a valid descriptor and a non-empty box, and each global byte it reads has a
launch value that no write of the execution covers. -/
theorem tensorSources (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hW : WriteFrame P X) (hS : LoadShapes P L X) : TensorSources L mem0 X := by
  rintro ⟨g, k⟩ al sp hi
  have hsrc : ∀ slot a, TensorCopy.source sp slot = .global a →
      ∃ v, mem0 ⟨.global, 0, a⟩ = some (some v) ∧
        ∀ w dst bytes, X.MemWrites w dst bytes → ¬ dst.Covers ⟨.global, 0, a⟩ := by
    intro slot a h
    have hin := load_input hpre hX hS hi (readLoc_of_source h)
    obtain ⟨v, hv⟩ := hin.2.1
    exact ⟨v, hv, hin.unwritten hW⟩
  obtain ⟨pc, hget⟩ := hi
  have hg : g < L.threads := Frame.lt_of_get hX hget
  rcases hS (g, k) al sp ⟨pc, hget⟩ with ⟨j, hj, rfl⟩ | ⟨tt, htt, p, hp, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := stateSpec_ok hpre hg j
    exact ⟨h1, h2, h3, hsrc⟩
  · obtain ⟨h1, h2, h3⟩ := Producer.tileLoad_ok hpre hg tt hp
    exact ⟨h1, h2, h3, hsrc⟩

/-- **The tensor-load part of `DirectFacts.globalReadFrame`**: a global byte covered by the
source read of a tensor load is allocated and is no output byte and no final-state byte. -/
theorem loads_readFrame (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hS : LoadShapes P L X) {i : EvId} {x y k : Nat} {a : Acc} {w : Bool} {l : Loc}
    (h : X.Intent (.async i (.read (.load x y k))) a w) (hc : a.Covers l) :
    mem0 l ≠ none ∧ ¬ P.OutputByte l ∧ ¬ P.StateByte l := by
  obtain ⟨-, sp, al, hi, hl, hs⟩ := h
  obtain rfl : a.loc = l := Protocol.covers_one hs hc
  exact (load_input hpre hX hS hi hl).frame

/-- **`DirectFacts.loadFill`**: every tensor load goes through a map that fills out-of-bounds
elements with zero and whose elements are not 64-bit floats. -/
theorem loads_fill (hS : LoadShapes P L X) :
    ∀ i address s, X.TensorIssue i address s →
      s.descriptor.fill = .zero ∧ s.descriptor.format ≠ .f64 := by
  intro i al sp hi
  rcases hS i al sp hi with ⟨j, -, rfl⟩ | ⟨tt, -, p, -, rfl⟩
  · exact loadSpec_fill P _ 8 _ _ _
  · exact loadSpec_fill P _ _ _ _ _

/-- **`DirectFacts.loadBounds`**: a tensor load that selects an out-of-bounds element through a
large-class map is a load of the values `v` or of the gate logits `beta`. -/
theorem loads_bounds (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hS : LoadShapes P L X) :
    ∀ i address s, X.TensorIssue i address s →
      TensorHasOob s.descriptor s.origin s.rows → s.descriptor.allocationClass = .large →
      (s.descriptor.base = P.valuesBase ∧ P.allocation 0 = .large) ∨
        (s.descriptor.base = P.logitsBase ∧ P.allocation 1 = .large) := by
  rintro ⟨g, k⟩ al sp hi hoob hlarge
  obtain ⟨pc, hget⟩ := hi
  have hg : g < L.threads := Frame.lt_of_get hX hget
  rcases hS (g, k) al sp ⟨pc, hget⟩ with ⟨j, hj, rfl⟩ | ⟨tt, htt, p, hp, rfl⟩
  · exact absurd hoob (stateSpec_source hpre g hg j hj).1
  · exact Producer.tileLoad_bounds hpre hg htt hp hoob hlarge

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Source
