-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueRun
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # What the thread layer exports (draft: machine, routing, prologue)

The layers above the thread layer speak of a thread's events through its machine's state before
each event (`Frame.stateAt (code L) X g k`). This draft holds the fields about the machine, the
routing of warps to roles and the prologue (barrier initializations, their fences, the cluster
barrier); the role fields (rings, Tensor Memory, statistics, output staging, exit and rank)
are added with the roles' run invariants.

`PrologueFacts` is proved for every consistent execution (`prologueFacts`); `ThreadFacts`
adds the fields that need every role: that the machine follows every thread (`tracked`, which
holds once every role is composed) and that no role initializes a barrier or uses the cluster
barrier (`init_site`, `cluster_ops`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The machine state of thread `g` before its `k`-th event. -/
abbrev St (L : Launch) (X : Execution) (g k : Nat) : Option (Option ThreadD) :=
  Frame.stateAt (code L) X g k

/-- The thread layer's facts about the machine, the routing and the prologue. -/
structure PrologueFacts (L : Launch) (X : Execution) : Prop where
  /-- Every launched thread is simulated by its machine. -/
  sound : ∀ g < L.threads, (code L g).Sound
  /-- A thread in a role runs it on a warp of that role. -/
  role_warp : ∀ {g k : Nat} {r : Role}, g < L.threads → St L X g k = some (some (.inr r)) →
    r.kind.Warp (warpOf L g)
  /-- Along the prologue: the prologue's run invariant (event kinds, the barriers initialized,
  each once, before the second fence, the fences and cluster-barrier operations so far). -/
  prologue_run : ∀ {g k : Nat} {p : Prologue.D}, g < L.threads →
    St L X g k = some (some (.inl p)) → Prologue.Run L g p ((X.tr g).take k)

/-- The thread layer's facts (draft). -/
structure ThreadFacts (L : Launch) (X : Execution) : Prop extends PrologueFacts L X where
  /-- Every thread is followed by its machine at each of its events. -/
  tracked : Frame.Tracked (code L) X
  /-- Every barrier initialization is the prologue's: warp 0's elected lane initializes the 36
  barriers of its CTA, warp 12's elected lane the handshake barrier, each with its count. -/
  init_site : ∀ {g k pc : Nat} {m : Loc} {c : Nat}, g < L.threads →
    X.get (g, k) = some ⟨pc, .mbInit m c⟩ →
      ∃ b : FBar, m = b.loc L (ctaOf L g) ∧ c = b.count ∧
        (b = .dealloc → warpOf L g = 12) ∧ (b ≠ .dealloc → warpOf L g = 0)
  /-- A thread's cluster-barrier operations are the prologue's arrival and wait, in that order,
  and every later event of the thread is its role's. -/
  cluster_ops : ∀ {g : Nat}, g < L.threads →
    ((X.tr g).filter (fun e => Prologue.isCluster e.kind)).length ≤ 2

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The prologue facts of every consistent execution of a launch satisfying the precondition. -/
theorem prologueFacts (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) :
    PrologueFacts L X where
  sound _ hg := sound hpre hg
  role_warp {_ k r} hg h :=
    role_warp_run hpre hg (Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg) k r h
  prologue_run {_ k p} hg h :=
    Prologue.run hpre hg (Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg) k p h

end
end PTX.Kernels.FlashAttn4Fwd.Proof
