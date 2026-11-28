-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows
public import Lemmas.Kernel.Progress.NextEv
public import Lemmas.Kernel.Goals
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # A released lane steps or polls and fails: the one case split of the progress classes

`NextRow.Next P L m X` is, for a maximal execution of a safe launch, what a pending released lane
does: it steps, or its trace extends consistently by an event that is no undefined behaviour
(`Sched.NextEv`). It is proved (`Prog.nextRow`, `Top/Prog/NextRow.lean`, from `next_all`,
`Common/Export/NextAll.lean`) and splits, by the lane's next event:

* `place` (proved here, `next_place`): a next event is at a pc of the code of the role whose lane
  condition the lane meets (`Iface/MbarRows.lean`'s regions), or at the final `ret`;
* the quiet row of each role (`NextRow.Quiet`): a lane whose next event is at the role's pc,
  where it has no failed poll as a next event, steps. The final `ret`'s is proved
  (`Prog.tail`, `Top/Prog/Quiet.lean`) and passed to `next_cls`. It is the
  role's `released_stepsQ` / `wait_site_stepsUN` with the state taken privately, for a wait with
  every failed poll ruled out, and for every other instruction. Proved and passed to `next_cls`:
  warpgroup 2 (`Prog.dequantRow`, `Top/Prog/QuietRows.lean`), the index warp (`Prog.indexRow`,
  `QuietIndex.lean`), the TMA warp (`Prog.tmaRow`, `QuietTma.lean`), warpgroup 1 (`Prog.wg1Row`,
  `QuietWg1.lean`), the MMA warp (`Prog.mmaRow`, `QuietMma.lean`), the startup
  (`Prog.startupRow`, `QuietStartup.lean`) and warpgroup 0 (`Prog.wg0Row`, `QuietWg0.lean`).

`WaitRows P L m X` bundles the wait-step rows of the roles that poll (`NextRow.Wait`), the way a
failed-poll class steps a lane once its channel blocks it; the MMA lane's is proved
(`mma_wait`, `Common/Export.lean`).

`next_cls` joins them: a pending released lane steps, or its next event is a failed poll. A
failed poll is a progress class by its channel (`Top/Prog/Classes.lean`). The rows are proved
under `Follow`, from the roles' trace-level exports (`<role>_next`, `<role>_wait`).

Not proved generally here: a quiet row covers named-barrier and collective next events, which
step only with the other lanes (`Descent.released_stepsQ` needs `(opKind ins.op).Rest = false`),
and a successful wait needs its object's final state (`wait_site_stepsUN`'s `hfin`), which is the
polled object's initialization record: both are role facts. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

/-- Lane `g`'s next event can be a failed poll at `pc`. -/
def FailsAt (L : Launch) (m : Mem0) (X : Execution) (g pc : Nat) : Prop :=
  ∃ l q sc, Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q false true sc⟩

/-- **The quiet row of a role** (`At`: its pcs and lane condition): a pending released lane of a
maximal execution of a safe launch, whose next event is at a pc of the role where no failed poll
is a next event, steps. -/
def NextRow.Quiet (P : Params) (L : Launch) (m : Mem0) (X : Execution)
    (At : Nat → Nat → Prop) : Prop :=
  SafeGoal kernel Assumptions.all L m → Maximal L kernel Assumptions.all m X →
    ∀ {g : Nat} {e : Event}, Frame.Pending L X g → Step.Released L X g →
    Sched.NextEv L kernel Assumptions.all m X g e → (∀ f, e.kind ≠ .ub f) → At g e.pc →
    ¬ FailsAt L m X g e.pc → Sched.Steps (timed P L) m X (.thread g)

/-- **A pending released lane steps or has a next event**, for one execution: a maximal
execution of a safe launch, a pending released lane steps, or has a next event without undefined
behaviour. -/
def NextRow.Next (P : Params) (L : Launch) (m : Mem0) (X : Execution) : Prop :=
  SafeGoal kernel Assumptions.all L m → Maximal L kernel Assumptions.all m X →
    ∀ {g : Nat}, Frame.Pending L X g → Step.Released L X g →
    Sched.Steps (timed P L) m X (.thread g) ∨
      ∃ e, Sched.NextEv L kernel Assumptions.all m X g e ∧ ∀ f, e.kind ≠ .ub f

/-- **The wait-step row of a role** (`lane-rules`, rule 2 (b)): a pending released lane of a
maximal execution of a safe launch, whose next event is a failed poll of `l` with parity `q` at a
pc of the role, steps when the channel blocks it as `Sched.WaitBlk` states. -/
def NextRow.Wait (P : Params) (L : Launch) (m : Mem0) (X : Execution)
    (At : Nat → Nat → Prop) : Prop :=
  SafeGoal kernel Assumptions.all L m → Maximal L kernel Assumptions.all m X →
    ∀ {g pc q : Nat} {l : Loc} {sc : MbarScope}, Frame.Pending L X g → Step.Released L X g →
    At g pc → Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q false true sc⟩ →
    Sched.WaitBlk (timed P L) X g l q → Sched.Steps (timed P L) m X (.thread g)

/-- **The wait-step rows of the roles that poll**, for one execution. -/
structure WaitRows (P : Params) (L : Launch) (m : Mem0) (X : Execution) : Prop where
  /-- (lane W1) Warpgroup 0. -/
  wg0 : NextRow.Wait P L m X (Wg0At L)
  /-- (lane A) The TMA lane. -/
  tma : NextRow.Wait P L m X (TmaAt L)
  /-- (lane A) The index warp. -/
  index : NextRow.Wait P L m X (IndexAt L)
  /-- (lane D) The dequantization warpgroup. -/
  dequant : NextRow.Wait P L m X (DequantAt L)

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {e : Event}

/-- **Where a next event is**: at a pc of the code of the role whose lane condition the lane
meets, or at the final `ret`. -/
theorem next_place (hp : Pre P L m) (hFw : Follow P L X)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f) :
    StartupAt e.pc ∨ Wg0At L g e.pc ∨ Wg1At L g e.pc ∨ MmaAt L g e.pc ∨ TmaAt L g e.pc ∨
      IndexAt L g e.pc ∨ DequantAt L g e.pc ∨ e.pc = 3611 := by
  obtain ⟨σ, -, hJ, hi, -, hpc⟩ := next_state hp hFw hn hub
  rw [hpc]
  exact place_state hp hJ hi

/-- **A pending released lane steps, or its next event is a failed poll.** -/
theorem next_cls (hp : Pre P L m) (hFw : Follow P L X) (hN : NextRow.Next P L m X)
    (htail : NextRow.Quiet P L m X fun _ pc => pc = 3611)
    (hdeq : NextRow.Quiet P L m X (DequantAt L)) (hix : NextRow.Quiet P L m X (IndexAt L))
    (htma : NextRow.Quiet P L m X (TmaAt L)) (hwg1 : NextRow.Quiet P L m X (Wg1At L))
    (hmma : NextRow.Quiet P L m X (MmaAt L)) (hwg0 : NextRow.Quiet P L m X (Wg0At L))
    (hst : NextRow.Quiet P L m X fun _ pc => StartupAt pc)
    (hs : SafeGoal kernel Assumptions.all L m) (hmax : Maximal L kernel Assumptions.all m X)
    (hpd : Frame.Pending L X g) (hrel : Step.Released L X g) :
    Sched.Steps (timed P L) m X (.thread g) ∨ ∃ pc, FailsAt L m X g pc := by
  rcases hN hs hmax hpd hrel with h | ⟨e, hn, hub⟩
  · exact .inl h
  by_cases hf : FailsAt L m X g e.pc
  · exact .inr ⟨_, hf⟩
  refine .inl ?_
  rcases next_place hp hFw hn hub with h | h | h | h | h | h | h | h
  · exact hst hs hmax hpd hrel hn hub h hf
  · exact hwg0 hs hmax hpd hrel hn hub h hf
  · exact hwg1 hs hmax hpd hrel hn hub h hf
  · exact hmma hs hmax hpd hrel hn hub h hf
  · exact htma hs hmax hpd hrel hn hub h hf
  · exact hix hs hmax hpd hrel hn hub h hf
  · exact hdeq hs hmax hpd hrel hn hub h hf
  · exact htail hs hmax hpd hrel hn hub h hf

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
