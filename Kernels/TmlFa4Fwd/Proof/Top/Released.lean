-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.Progress.ReleasedU

public import Kernels.TmlFa4Fwd.Proof.Progress.Time
public import Lemmas.Kernel.Goals
public import Lemmas.Kernel.Progress.Released
import Kernels.TmlFa4Fwd.Proof.Lib.MmaLayout
import Kernels.TmlFa4Fwd.Proof.Lib.Guarded
import Kernels.TmlFa4Fwd.Proof.Common.Sound

@[expose] public section

/-! # A released lane at an instruction that needs no partner steps (E5a)

`Descent.released_steps` for tml-fa4's thread machines: a released pending lane of a maximal
execution, at a state whose instruction is outside `Descent.NextKind.Rest` (not an mbarrier
poll, a warp collective, a register request or an allocation), performs it (`nonRest_steps`).
This covers every role at once: the startup's fence, barrier and initializations, the scheduler's
reads, the correction lanes' Tensor Memory loads, stores and arrivals, the MMA warp's MMAs and
commits, the output warp's tensor stores, commits and drains, the loaders' reads, copies and
arrivals, and every exit.

The execution facts of `Descent.NextEnv` that the kernel provides: synchronization stays guarded (no
object fault by safety, `noTma_of_safe`, and `guardedOfTmaSafe`; no releasing store, atomic or
thread fence in the code), MMA layouts are injective (`Mma.actualMmaLayoutInjective`). The facts
still open are named in `NextPrem` (their open part is the class `Top/Prog/Next.lean`): the order of
the conflicting accesses at the bytes that are read, that a new read keeps the read-only input
assumption, that Tensor Memory cells hold 4-byte words, and that a lane whose last event is an
allocation request of lane 0 is not at a store. A lane without events is at the startup's first
shuffle, a warp collective, so a lane outside `Rest` has made an event
(`code25_rest`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0}

/-- **The instruction at a thread state needs a partner or a kernel fact**
(`Descent.NextKind.Rest`). -/
def RestAt (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Prop :=
  ∀ ins, kernel.code[(thread p L g).pc σ]? = some ins → (Descent.opKind ins.op).Rest = true

/-- **The execution facts of a released lane's step still open.** -/
structure NextPrem (p : Params) (L : Launch) (m : Mem0) : Prop where
  /-- The conflicting accesses at the bytes that are read are ordered. -/
  reads : ∀ X, Maximal L kernel Assumptions.all m X → ReadsOrdered L X
  /-- A read with a source at each byte keeps the assumptions' constraints (the read-only
  input assumption: no write covers an input byte it reads). -/
  readWf : ∀ X, Maximal L kernel Assumptions.all m X → ∀ g pc a bs r,
    (∀ e, NewRead L m X g e r a bs) →
    ∀ a' ∈ Assumptions.all, a'.wf L m (X.snoc g ⟨pc, .rd a bs⟩ r)
  /-- Every Tensor Memory write leaves a 4-byte word in its cell. -/
  words : ∀ X, Maximal L kernel Assumptions.all m X →
    ∀ s cell v, TcMma.Wrote L Assumptions.all X s cell v → v.bytes = 4
  /-- A lane whose last event is an allocation request of lane 0 is not at a store. -/
  allocLast : ∀ X, Maximal L kernel Assumptions.all m X → ∀ g σ,
    Frame.stateAt (thread p L) X g (X.tr g).length = some (some σ) →
    ∀ ins, kernel.code[(thread p L g).pc σ]? = some ins → Descent.opKind ins.op = .store →
    ∀ pc grp dst n, X.get (g, (X.tr g).length - 1) =
      some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ → laneOf L g ≠ 0

/-- The startup's first instruction is a warp shuffle. -/
theorem code25_rest : ∀ ins, kernel.code[25]? = some ins → (Descent.opKind ins.op).Rest = true := by
  intro ins h
  have : kernel.code[25]?.map (fun i => (Descent.opKind i.op).Rest) = some true := by
    decide +kernel
  rw [h] at this
  simpa using this

/-- A safe launch has no mbarrier object fault, lifetime or access error (`TmaUnsafe` is a
class of `Unsafe`). -/
theorem noTma_of_safe (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) : ¬ TmaUnsafe L m X :=
  fun hT => hs.2 X hX (.inr (.inr (.inr (.inr (.inr (.inl hT))))))

/-- **A released pending lane at an instruction outside `Rest` steps.** -/
theorem nonRest_steps (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hA : Assumption.WfStep (fun _ => true) L kernel m Assumptions.all) (hN : NextPrem p L m) :
    ∀ X, Maximal L kernel Assumptions.all m X → ∀ g σ, Frame.Pending L X g →
      Step.Released L X g → Frame.stateAt (thread p L) X g (X.tr g).length = some (some σ) →
      ¬ RestAt p L g σ → Sched.Steps (Progress.timed p L) m X (.thread g) := by
  intro X hmax g σ hpd hrel hσ hnr
  have hX := hmax.1
  have env : Descent.NextEnv L kernel Assumptions.all m X :=
    { max := hmax
      noUb := Sched.safe_noUb (hs.2 X hX)
      wf := hA
      readWf := hN.readWf X hmax
      reads := hN.reads X hmax
      guard := guardedOfTmaSafe hX (noTma_of_safe hs hX)
      no_release := fun _ _ _ _ h => noReleasingStore hX h
      no_release_rmw := fun _ _ _ _ _ h => (noAtomicEvent hX h).elim
      no_fence := fun _ _ _ => noThreadFence hX
      layout := Mma.actualMmaLayoutInjective hX
      words := hN.words X hmax }
  have hne : X.tr g ≠ [] := by
    intro h0
    have h0' : Frame.stateAt (thread p L) X g (X.tr g).length =
        some (some (thread p L g).init) := by
      rw [h0]; exact Frame.stateAt_zero
    rw [h0'] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    exact hnr code25_rest
  have hk : ∀ ins, kernel.code[(thread p L g).pc σ]? = some ins →
      (Descent.opKind ins.op).Rest = false := by
    intro ins hins
    by_contra hr
    refine hnr fun ins' h' => ?_
    rw [hins] at h'
    cases h'
    simpa using hr
  exact Descent.released_stepsU env hpd hne hrel (fun g hg => thread_sound hp hg) hσ hk
    (hN.allocLast X hmax g σ hσ)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Top
