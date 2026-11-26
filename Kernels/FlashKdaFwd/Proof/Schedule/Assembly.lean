-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Schedule.Free
public import Kernels.FlashKdaFwd.Proof.Schedule.Poll
public import Kernels.FlashKdaFwd.Proof.Progress.Guard
public import Kernels.FlashKdaFwd.Proof.Protocol.StoreCover

@[expose] public section

/-!
# Progress of the FlashKDA kernel from the layers' contracts

`progress_of_ref` assembles the premises of the dispatcher (`Premises2`, `Dispatch.lean`) for
the thread machine, the time table `timed L I`, the classes `cls`, the warp key `wkey L`, the
event shape `pollEv L` and the barrier groups `barG`, and concludes `ProgressGoal`: given
safety, every maximal execution is complete. Every premise is derived; the hypotheses of the
theorem are what the other layers deliver:

* `hpre`: the precondition of the specification. It makes the thread machines sound
  (`Thread.sound`) and fixes the block size.
* `hT`: the tile count the reference layer chose for a thread is the tile count of the thread's
  block in the specification (`Protocol.ctaTiles`). It is a statement about the numbers `I`
  only, true by definition if `I.tiles g` is defined as `ctaTiles P (g / L.block)`.
* `hR`: the reference layer's contract for progress (`RefProgress`, `Contract.lean`), for
  every consistent execution.
* `hF`, `hU`: the protocol layer's contracts (`Protocol.Facts`; the classification of the
  buffer region `UnionFacts` with the coverage `StoreCover`), which the reference layer proves.
* `hreads`: the conflicts at read bytes are ordered (from the safety facts, `Proof/Top`).
* `htensor`: every tensor load is routed to its block, has a valid descriptor and reads launch
  bytes that nothing writes (reference layer).
* `hs`: the safety goal.

Where each premise comes from: `sound` — `Thread.sound`; `tracked`, `barAfter` — the contract
(`Instance.lean`); `started`, `pollOp`, `pollShape`, `pollTime`, `block32`, `keyWarp` — static
(`Instance.lean`); `freeTmpl` — `Free.lean`; `barLag`, `coll`, `matrix` — `Lag.lean`;
`pollState`, `pollBlk` — `Poll.lean`; `barGroup`, `storeSources` — the protocol layer
(`Proof/Protocol/Export.lean`); `readWf`, `guard`, `noRelease`, `noReleaseRmw`, `noFence` —
`Proof/Progress/Kda.lean` and `Guard.lean`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Sched PTX.Step PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Protocol

noncomputable section

variable {L : Launch} {P : Params} {mem0 : Mem0} {I : Nums}

set_option maxRecDepth 100000 in
/-- **Progress of the FlashKDA kernel**: given safety, every maximal execution is complete. -/
theorem progress_of_ref (hpre : Pre P L mem0)
    (hT : ∀ g, I.tiles g = ctaTiles P (g / L.block))
    (hR : ∀ X, Consistent L kernel Assumptions.all mem0 X → RefProgress L mem0 X I)
    (hF : ∀ X, Consistent L kernel Assumptions.all mem0 X → Facts P L X)
    (hU : ∀ X, Consistent L kernel Assumptions.all mem0 X →
      ∃ O, UnionFacts L X (ctaTiles P) O ∧ StoreCover L X O)
    (hreads : ∀ X, Consistent L kernel Assumptions.all mem0 X → ReadsOrdered L X)
    (htensor : ∀ X, Maximal L kernel Assumptions.all mem0 X → TensorSources L mem0 X)
    (hs : SafeGoal kernel Assumptions.all L mem0) :
    ProgressGoal kernel Assumptions.all L mem0 :=
  have hsound : ∀ g < L.threads, (Thread.code L g).Sound := fun _ hg => Thread.sound hpre hg
  progress_of2 (M := timed L I) (cls := cls) (key := wkey L) (pollEv := pollEv L) (G := barG)
    asmOk codeOk
    { sound := hsound
      tracked := fun X hX => (hR X hX).tracked
      block32 := prem_block32 hpre.block
      keyWarp := wkey_eq
      started := fun _ _ _ _ _ hσ hc => prem_started hσ hc
      freeTmpl := fun _ _ _ _ _ _ hg _ hc hat hinv hout =>
        prem_freeTmpl (hsound _ hg) hc hat hinv hout
      readWf := fun _ hmax => readWf_of_safe hs hmax.1
      reads := hreads
      guard := fun X hX => syncGuarded hX (hs.2 X hX)
      noRelease := fun _ hX _ _ _ _ he => noReleasingStore hX he
      noReleaseRmw := fun _ hX _ _ _ _ _ he => (noAtomicEvent hX he).elim
      noFence := fun _ hX _ _ _ => noThreadFence hX
      pollOp := fun hc ins hi => prem_pollOp hc ins hi
      pollShape := fun _ _ hat _ hi hf => prem_pollShape hat hi hf
      pollState := fun X hmax _ _ hp hrel hσ hc l q ok sc hev =>
        prem_pollState hpre (hR X hmax.1) (hF X hmax.1) hmax.1 hp.1 hrel hσ hc l q ok sc hev
      pollBlk := fun X hmax _ _ hp _ hσ hc l q sc before hev hst _ hpar =>
        prem_pollBlk hpre hsound hs hT (hR X hmax.1) (hF X hmax.1) hmax hp.1 hσ hc l q sc
          before hev hst hpar
      pollTime := fun hc => prem_pollTime hc
      coll := fun X hmax => prem_coll hpre hsound hs (hR X hmax.1) (hF X hmax.1) hmax.1
      matrix := fun X hmax => prem_matrix hpre hsound hs hT (hR X hmax.1) hmax
      barGroup := fun X hmax _ _ _ _ _ _ hg he =>
        prem_barGroup (hF X hmax.1).bars hpre.block hg he
      barAfter := fun X hmax _ _ _ _ _ _ _ hg he hσ => prem_barAfter (hR X hmax.1) hg he hσ
      barLag := fun X hmax _ _ _ _ _ _ _ hg hy hcta hG he hσ hle =>
        prem_barLag hpre hsound hs hT (hR X hmax.1) (hF X hmax.1) hmax hg hy hcta hG he hσ hle
      tensorSources := htensor
      storeSources := fun X hmax => by
        obtain ⟨O, U, C⟩ := hU X hmax.1
        exact (hF X hmax.1).storeSources hpre hmax.1 U C }
    hs

end

end PTX.Kernels.FlashKdaFwd.Proof.Progress
