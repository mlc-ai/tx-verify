-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Bound.DComp
public import Kernels.InklingRelDecode.Proof.Bound.WComp
public import Lemmas.Flow.NotBulk

@[expose] public section

/-!
# `BoundGoal` for the Inkling kernel

The kernel's threads are of two kinds: the default partition (warps 0 to 3, `g % block < 128`,
`DComp.code`) and the workers (warps 4 to 7, `WComp.code`). `threadCode L Q` is the family of the
launch's thread machines. Each has a rank on its abstract states (`Bound/DComp.lean`,
`Bound/WComp.lean`) that every step lowers by the step's count, except that a worker's load of the
role byte, which starts one of the four roles, may raise it by `WComp.budget`. The raise is the
only one: the dispatch loop's other events and every role count the rank down.

`bound_goal` assembles them (`Bound.bound_of_rank_resets`): every thread's counted events are at
most its initial rank plus two, plus `WComp.budget` for each load of the role byte of a worker
thread, which the protocol layer bounds (`DispatchBound`).

## What `bound_goal` assumes

* `Pre Q L mem0`, the launch's precondition.
* `hso`: `DComp.SmObligations` for every default-partition thread. The default-partition
  machine's soundness, which the bound needs to follow the thread, is conditional on it; the
  rank itself is a function of the softmax region's abstract states and does not depend on which
  of its sites have step lemmas.
* `htr`: `Frame.Tracked` for `threadCode L Q`: no thread's machine reaches `some none`, the
  places at which a machine stops following the code. Each is a protocol fact (the roles' list
  is in `DComp`'s and `WComp`'s headers: the role bytes, the loaded words, the shuffles, the
  numbers the roles read); it is the interface layer's `tracked`.
* `hR : DispatchBound L mem0 R`: **the role table protocol.** A worker thread loads the byte of
  its role from the table (`Worker.Site.ldRole`) once per round of its dispatch loop, and a role
  ends at the loop's head again. The table is written twice, `0x01000202` and then `0x03030303`,
  each time before a `barrier.sync 1` the workers wait at, so a worker loads at most twice
  (`R = 2`) and its second load is the exit. This file does not prove that; it takes the number
  of loads as `R`.

The bound is `N = L.threads * ((asyncStageBound + 1 + 2 * L.grid) * n) + …` for
`n = DComp.top + 7 + WComp.budget * R + 2`, from `Frame`'s size lemma.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bound
open PTX PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

/-- The launch's thread machines: the default partition's for `g % block < 128`, the workers'
otherwise. -/
def threadCode (L : Launch) (Q : Params) (g : Nat) : Flow.Code kernel Assumptions.all L g :=
  if g % L.block < 128 then DComp.code L g Q else WComp.code L g Q

/-- The events that may raise a rank: the load of the role byte, in a worker thread. -/
def reset (L : Launch) (g : Nat) (e : Event) : Bool :=
  decide (128 ≤ g % L.block) && decide (e.pc = Worker.Site.ldRole.pc)

/-- **The protocol layer's bound on the dispatch.** A worker thread (warps 4 to 7) of a consistent
execution loads the byte of its role (the event at `Worker.Site.ldRole`) at most `R` times. -/
def DispatchBound (L : Launch) (mem0 : Mem0) (R : Nat) : Prop :=
  ∀ X, Consistent L kernel Assumptions.all mem0 X → ∀ g < L.threads, 128 ≤ g % L.block →
    (X.tr g).countP (fun e => decide (e.pc = Worker.Site.ldRole.pc)) ≤ R

/-- The uniform bound on the initial ranks. -/
def initTop : Nat := DComp.top + 7

/-- **Every thread's machine has a rank** that every step lowers by its count, except at a reset
event, and its initial state is at most `initTop`. -/
theorem ranked (L : Launch) (Q : Params) (g : Nat) :
    ∃ rank : (threadCode L Q g).D → Nat,
      (∀ d d' e, (threadCode L Q g).inv d → (threadCode L Q g).inv d' →
        e.pc = (threadCode L Q g).pc d → (threadCode L Q g).next d e = some (some d') →
        rank d' + (if e.counts then 1 else 0) ≤
          rank d + (if reset L g e then WComp.budget else 0)) ∧
      rank (threadCode L Q g).init ≤ initTop := by
  by_cases h : g % L.block < 128
  · have e1 : threadCode L Q g = DComp.code L g Q := by
      simp only [threadCode, h, ↓reduceIte]
    rw [e1]
    refine ⟨DComp.rank, fun d d' e hi hi' _ hn => ?_, ?_⟩
    · have := DComp.rank_step hi hi' hn
      omega
    · have := DComp.rank_init L g Q
      unfold initTop
      omega
  · have e1 : threadCode L Q g = WComp.code L g Q := by
      simp only [threadCode, h, ↓reduceIte]
    rw [e1]
    refine ⟨WComp.rank, fun d d' e hi _ hpc hn => ?_, ?_⟩
    · have := WComp.rank_step hi hpc hn
      have hr : WComp.extra e ≤ (if reset L g e then WComp.budget else 0) := by
        unfold WComp.extra reset
        by_cases hp : e.pc = Worker.Site.ldRole.pc
        · have hg : 128 ≤ g % L.block := by omega
          simp [hp, hg]
        · simp [hp]
      omega
    · rw [WComp.rank_init]
      unfold initTop
      omega

/-! ### The machines are sound -/

variable {Q : Params} {L : Launch} {mem0 : Mem0}

/-- **The launch's thread machines are sound**: a default-partition thread's under
`SmObligations` (`DComp.sound`), a worker's under `Pre` (`WComp.sound`). -/
theorem threadCode_sound (hpre : Pre Q L mem0)
    (hso : ∀ g < L.threads, g % L.block < 128 → DComp.SmObligations Q L mem0 g) :
    ∀ g < L.threads, (threadCode L Q g).Sound := by
  intro g hg
  by_cases h : g % L.block < 128
  · have e1 : threadCode L Q g = DComp.code L g Q := by
      simp only [threadCode, h, ↓reduceIte]
    rw [e1]
    exact DComp.sound hpre hg h (hso g hg h)
  · have e1 : threadCode L Q g = WComp.code L g Q := by
      simp only [threadCode, h, ↓reduceIte]
    rw [e1]
    exact WComp.sound hpre (by
      show 4 ≤ g % L.block / 32
      omega)

/-! ### The kernel has no asynchronous copy -/

theorem kernel_noBulk : kernel.code.all (fun ins => !bulkOp ins.op) = true := by
  decide +kernel

/-- **The kernel has no linear asynchronous copy** (it copies tiles with `cp.async.bulk.tensor`,
which is not a copy event of the model's `AsyncCopy.Spec`). -/
theorem no_copy {X : Execution} (hX : Consistent L kernel Assumptions.all mem0 X) :
    ∀ {i : EvId} {pc : Nat} {s : AsyncCopy.Spec}, X.get i ≠ some ⟨pc, .copy s⟩ :=
  fun he => no_kind_of_code hX bulkOp (fun k => ∃ s, k = .copy s)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_bulk_op hf hk)
    kernel_noBulk he ⟨_, rfl⟩

/-! ### The bound -/

/-- **Consistent executions of the Inkling kernel have bounded size**, given the precondition,
the softmax region's obligations, that the machines follow every thread (`htr`) and the protocol
layer's bound `R` on the dispatch loads of the worker threads. -/
theorem bound_goal (hpre : Pre Q L mem0)
    (hso : ∀ g < L.threads, g % L.block < 128 → DComp.SmObligations Q L mem0 g)
    (htr : ∀ X, Consistent L kernel Assumptions.all mem0 X → Tracked (threadCode L Q) X)
    {R : Nat} (hR : DispatchBound L mem0 R) : BoundGoal kernel Assumptions.all L mem0 := by
  choose rank hstep hinit using ranked L Q
  refine bound_of_rank_resets (C := threadCode L Q) (threadCode_sound hpre hso) htr rank
    (reset L) WComp.budget R initTop (fun g _ => hstep g) (fun g _ => hinit g) ?_
    (fun X hX i s ⟨_, hc⟩ => (no_copy hX hc).elim)
  intro X hX g hg
  by_cases h : 128 ≤ g % L.block
  · have hf : reset L g = fun e => decide (e.pc = Worker.Site.ldRole.pc) := by
      funext e
      simp [reset, h]
    rw [hf]
    exact hR X hX g hg h
  · have hf : reset L g = fun _ => false := by
      funext e
      simp [reset, h]
    rw [hf]
    simp

end

end PTX.Kernels.InklingRelDecode.Proof.Bound
