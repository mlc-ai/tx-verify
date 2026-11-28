-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.History
import all Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

/-- Within a call, the full machine takes the role's successor. An observed nonfaulting
next event rules out death or a stub. Only the dispatch-return site leaves the call. -/
theorem mma_successor {Q L m X g k w x r d n e ev}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hs : stateAt (thread Q L) X g k = some (some (workerState w x (.mma r) d n)))
    (he : X.get (g,k) = some e) (hn : X.get (g,k+1) = some ev) (hu : ∀ f, ev.kind ≠ .ub f) :
    ∃ d', Mma.next L g d e = some (some d') ∧ (d'.site ≠ .dispatch →
      stateAt (thread Q L) X g (k+1) = some (some (workerState w x (.mma r) d'
        (Code.bump cls n e)))) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨new,hnew,_⟩ := Frame.good_stateU (fun g hg => thread_sound hp hg) hX hn
    (fun _ f h => hu f (congrArg Event.kind h)) (hf g hg (k+1))
  have hstep := stateAt_succ (C := thread Q L) (X := X) he
  rw [hs] at hstep
  cases hz : Mma.next L g d e with
  | none =>
    simp [workerState,thread,Code.roleThread,Code.counted,Code.toMachine,Code.glue,
      workerCode,Code.loopGlue,workerFrag,Code.withStubs,frag,Mma.code,hz] at hstep
    rw [hnew] at hstep
    contradiction
  | some o =>
    cases o with
    | none =>
      simp [workerState,thread,Code.roleThread,Code.counted,Code.toMachine,Code.glue,
        workerCode,Code.loopGlue,workerFrag,Code.withStubs,frag,Mma.code,hz] at hstep
      rw [hnew] at hstep
      cases hstep
    | some s =>
      refine ⟨s,rfl,fun live => ?_⟩
      simpa only [workerState,thread,Code.roleThread,Code.counted,Code.toMachine,Code.glue,
        workerCode,Code.loopGlue,workerFrag,workerBack,Code.backEnter,Code.withStubs,
        frag,Mma.code,hz,live,↓reduceIte,Option.bind_some,Option.map_some] using hstep

end PTX.Kernels.InklingRelDecode.Proof
