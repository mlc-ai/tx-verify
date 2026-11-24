-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WorkerStep
public import Lemmas.Flow.Step.SiteIte
public import Lemmas.Flow.Compose

@[expose] public section

/-! # The worker's obligations as a code machine

`code` is the worker as a code machine from its first barrier, and `stepAt` its obligation for
every state (by `site_cases`). From it: every site is an event instruction whose guard holds
(`site_ok`: none is guarded), and every event fired at a worker state steps to the state `next`
gives, or leaves the machine, or is a fault (`step`).

The machine has no `Code.Sound` of its own: its start is the common prologue's (pc 0 to 12, in
`WorkerStart.lean`), and it ends at the entries of the roles (`toIdle`, `toLoader`, `toMma`,
`toExit`, whose successor is `some none`: the roles' own machines take over there). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Worker
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Loader (Pro)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-- The worker as a code machine, from its first barrier, with the inherited registers `P`. -/
@[reducible] def code (L : Launch) (g : Nat) (P : Pro) : Flow.Code kernel asms L g where
  D := D
  init := D.start P
  pc := (·.site.pc)
  facts := facts L g
  inv := Inv L g
  next := next L g

/-- Every worker state satisfies the code machine's obligation: `site_cases` over the sites,
except the shuffle of the warp index and the load of the role byte (`WorkerStep`). -/
theorem stepAt (P : Pro) (d : D) : (code L g P).StepAt d := by
  obtain ⟨s, P'⟩ := d
  site_cases s except [.shfl => ⟨fun _ h hi hc hf => step_shfl rfl hi h hc hf⟩,
      .ldRole => ⟨fun _ h hi hc hf => step_ldRole rfl hi h hc hf⟩]
    trans [next]
    seg_by (wk_seg_site)
    inv_by (intro hi; first | exact hi.at | exact Inv.setTm hi _ _ | fail "wk_inv")
    guard_by (first | rfl | fail "wk_guard")

/-- Every worker site is an unguarded event instruction. -/
theorem site_ok (hi : Inv L g d) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts L g d) ins.guard :=
  (stepAt d.P d).site hi

/-- Every event fired at a worker state steps to its successor. -/
theorem step (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u :=
  (stepAt d.P d).step ins h hi hc hf

end
end PTX.Kernels.InklingRelDecode.Proof.Worker
