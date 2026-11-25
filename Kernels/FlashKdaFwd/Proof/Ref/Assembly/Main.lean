-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Top.Final
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.FactsB
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Buffers
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Values
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Direct
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Progress

@[expose] public section

/-!
# Everything the reference layer and the value layer deliver

`Proof/Top/Final.lean` reduces the kernel's theorem to one structure, `Top.Contracts`: the
statements about every consistent execution (a partial run of the launch that the model
allows) that the layers below the protocols have to prove. This file fills it, one field from
each file of this directory:

* `facts` (`FactsA.lean`, `FactsB.lean`): the protocol layer's contract — barriers, the
  initialization of the eleven mbarriers, the two pipelines, the state mbarrier, the bfloat16
  state copy, the lifetimes of the asynchronous operations;
* `buffers` (`Buffers.lean`, `Values.lean`): for the owner functions `owners P L` (which piece
  of a load, or which thread, writes a byte of a staging buffer), the classification of every
  access of the buffer region, the coverage of the buffers before they are handed over, the
  shapes of the stores of the results, and the content of the bytes that are stored;
* `direct` (`Direct.lean`, with the value side of `Values.lean`): footprints, the schedule of
  the matrix instructions, and no undefined-behaviour event;
* `ref` (`Progress.lean`): the contract of the progress argument, for the numbers `nums P L`
  that are read off a thread state;
* `tensor` (`Direct.lean`): every tensor load reads launch memory that nobody writes;
* `init` (`Progress.lean`): the bound `bound P` on the events of a thread.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **The contracts of the reference and value layers hold on every launch that satisfies the
precondition.** -/
theorem contracts (hpre : Pre P L mem0) : Top.Contracts P L mem0 (nums P L) (bound P) where
  tiles := Progress.nums_tiles P L
  facts _ hX := facts hpre hX
  buffers _ hX :=
    ⟨owners P L, unionFacts hpre hX, storeCover hpre hX, storesIssued hpre hX,
      outContent hpre hX (owners P L)⟩
  direct _ hX := direct hpre hX (dataHalf hpre hX)
  ref _ hX := refProgress hpre hX (Direct.noUb hpre hX (dataHalf hpre hX))
  tensor _ hmax := tensorSources hpre hmax
  init := init hpre

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
