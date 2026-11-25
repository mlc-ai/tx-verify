-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Top.Layers
public import Kernels.FlashKdaFwd.Proof.Top.Reads
public import Kernels.FlashKdaFwd.Proof.Protocol.ResultGuard
public import Kernels.FlashKdaFwd.Proof.Schedule.Assembly

@[expose] public section

/-!
# The kernel is correct, from the contracts of the reference and value layers

`Layers.lean` states the theorem against six deliverables. Three of them are themselves proved
from contracts of the layers below: the result facts (`Protocol.resultFacts_of_contracts`),
progress (`Progress.progress_of_ref`) and the bound (`Progress.terminates_of_ref`). This file
composes them, so that what remains is exactly one structure, `Contracts`: the statements that
the reference layer (`Proof/Ref`: what every thread does, read off the thread machines) and the
value layer (`Proof/Values`: what the data registers hold) prove for every consistent execution.

Words used below. A *consistent execution* is a partial run of the launch that the model
allows. The *owner functions* `O` name, for a byte of a staging buffer, the piece or the thread
that writes it. `Nums` are the numbers the progress argument reads off a thread state (tile
index, tile count, events left); `rank` is the resulting bound on the events a thread can
still make.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Top
open PTX PTX.Step
open PTX.Kernels.FlashKdaFwd.Protocol (Facts UnionFacts StoreCover StoresIssued OutContent Owners
  ctaTiles)
open PTX.Kernels.FlashKdaFwd.Proof.Progress (Nums RefProgress rank)

/-- **What the reference layer and the value layer deliver for one launch.** `I` are the
numbers read off a thread state and `n` bounds the events any thread can make. -/
structure Contracts (P : Params) (L : Launch) (mem0 : Mem0) (I : Nums) (n : Nat) : Prop where
  /-- The tile count read off a thread is the tile count of its block in the specification. -/
  tiles : ∀ g, I.tiles g = ctaTiles P (g / L.block)
  /-- The contract of the protocol layer (barriers, mbarriers, loads, stores, the state copy). -/
  facts : ∀ X, Consistent L kernel Assumptions.all mem0 X → Facts P L X
  /-- For some owner functions: the accesses of the buffer region are classified
  (`UnionFacts`), every owned byte is written before it is handed over (`StoreCover`), the
  tensor stores and element stores of the outputs have the specified shapes (`StoresIssued`),
  and the bytes the owners write are the specified values (`OutContent`). -/
  buffers : ∀ X, Consistent L kernel Assumptions.all mem0 X →
    ∃ O : Owners, UnionFacts L X (ctaTiles P) O ∧ StoreCover L X O ∧ StoresIssued P L X ∧
      OutContent P L X O
  /-- Footprints, the matrix schedule, tensor copy operands, no undefined-behaviour event. -/
  direct : ∀ X, Consistent L kernel Assumptions.all mem0 X → DirectFacts P L mem0 X
  /-- The contract of the progress argument: positions, ledgers, the events left. -/
  ref : ∀ X, Consistent L kernel Assumptions.all mem0 X → RefProgress L mem0 X I
  /-- Every tensor load is routed to its block, has a valid descriptor, and reads launch memory
  that nobody writes. -/
  tensor : ∀ X, Maximal L kernel Assumptions.all mem0 X → TensorSources L mem0 X
  /-- At most `n` events are left at the first state of every thread. -/
  init : ∀ g < L.threads, rank I g (Thread.code L g).init ≤ n

variable {P : Params} {L : Launch} {mem0 : Mem0} {I : Nums} {n : Nat}

/-- The six deliverables of `Layers`, from the contracts. -/
theorem Contracts.layers (hp : Pre P L mem0) (C : Contracts P L mem0 I n) :
    Layers P L mem0 where
  facts := C.facts
  union X hX := by
    obtain ⟨O, U, -⟩ := C.buffers X hX
    exact ⟨O, U⟩
  direct := C.direct
  result X hX := by
    obtain ⟨O, U, Cv, S, V⟩ := C.buffers X hX
    exact Protocol.resultFacts_of_contracts hp hX (C.facts X hX) U Cv S V
  progress :=
    Progress.progress_of_ref hp C.tiles C.ref C.facts
      (fun X hX => by
        obtain ⟨O, U, Cv, -⟩ := C.buffers X hX
        exact ⟨O, U, Cv⟩)
      (fun X hX => by
        obtain ⟨O, U, -⟩ := C.buffers X hX
        exact readsOrdered (safetyFacts hp hX (C.facts X hX) U (C.direct X hX)))
      C.tensor
  bound := Progress.terminates_of_ref hp C.ref C.init

/-- **The kernel is correct on every launch that satisfies `Pre`, given the contracts.** -/
theorem correct_of_contracts (hp : Pre P L mem0) (C : Contracts P L mem0 I n) :
    Correct kernel Assumptions.all L mem0 (Post P mem0) :=
  correct_of_layers hp (C.layers hp)

end PTX.Kernels.FlashKdaFwd.Proof.Top
