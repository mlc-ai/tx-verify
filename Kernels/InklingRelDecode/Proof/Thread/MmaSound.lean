-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.MmaStepsQ
public import Kernels.InklingRelDecode.Proof.Thread.MmaStepsP

@[expose] public section

/-! # The MMA warp's obligations as a code machine

`stepAt` (from `MmaStepsQ`, `MmaStepsP`) is the obligation of every state of `code`, the role as a
code machine on its own (from `setmaxnreg.dec`, with the prologue's registers `pro` and the
Tensor Memory base `tm`). From it: every MMA site is an event instruction whose guard holds by
its facts (`site_ok`; the elected-lane guards of the MMAs and commits hold by the facts of those
sites, since the elections send the other lanes past the block), and every event fired at an MMA
state steps to the state `next` gives, or stops the machine (`step`), for the reason `Stop` only
(`stops`). `entry` gives the first state's facts from the prologue's registers live at the role's
`setmaxnreg`, and `handoff` the facts of the dispatch the role returns to. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t u : TState} {e : Event}
  {ins : Instr}

/-- **The steps.** Every MMA state satisfies the code machine's obligation. -/
theorem stepAt (hpre : Pre P L mem0) (tm0 : Nat) (pro0 : Nat → Value) (d : D) :
    (code asms L g tm0 pro0).StepAt d := by
  by_cases h : d.site.pc < 2500
  · exact stepAt_q hpre tm0 pro0 d h
  · exact stepAt_p hpre tm0 pro0 d (by omega)

/-- The continuation of a step of this role: the thread stops following (`some none`), or steps
to `d'` at `t'` by a run of `Tau`. -/
def Cont (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) : Prop :=
  next L g d e = some none ∨ ∃ d' t', next L g d e = some (some d') ∧
    Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ At t' d'.site.pc (facts L d') ∧ Inv d'

/-- A step of the machine: the thread continues to the successor state, or the event faults. -/
def Step (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) : Prop :=
  Cont L g d e u ∨
    (next L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u)

/-- Each site is an event instruction whose guard holds by its facts. -/
theorem site_ok (hpre : Pre P L mem0) {d : D} (hi : Inv d) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts L d) ins.guard :=
  (stepAt (g := 0) hpre 0 (fun _ => b32 0) d).site hi

/-- **The steps.** An event at an MMA state continues to its successor's concrete state by local
steps, or stops the machine (a dead state after an unreadable word or a word without bits). -/
theorem step (hpre : Pre P L mem0) (d : D) (hi : Inv d) (h : At t d.site.pc (facts L d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u :=
  (stepAt hpre 0 (fun _ => b32 0) d).step ins h hi hc hf

/-- Why the machine stops: the read of `num_iters` returned bytes that rebuild no value, the
word at `barrier.sync 1` has no bits, or a broadcast received a word without bits. -/
def Stop (d : D) (e : Event) : Prop :=
  (∃ x bs f, e.kind = .rd x bs ∧ rebuild 3 bs = .error f) ∨
    Raw.word32Of (d.pro 471) = none ∨
    ∃ m av bv cv recv ok, e.kind = .shfl m av bv cv recv ok ∧ Raw.word32Of recv = none

/-- **Why the machine stops.** At a fired event the successor is `none` only for the reason
`Stop`. -/
theorem stops (tm0 : Nat) (pro0 : Nat → Value) (d : D) :
    (code asms L g tm0 pro0).StopsFor Stop d := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  stops_cases s trans [next, Stop] stop_by (first
    | (left; exact ⟨_, _, _, rfl, by assumption⟩)
    | (right; left; assumption)
    | (right; right; exact ⟨_, _, _, _, _, _, rfl, by assumption⟩)
    | fail "stop")

/-- The role is simulated by its code machine from its first state, if the thread reaches that
state: `sound` carries the start (the prologue and the dispatch lead the thread to
`setmaxnreg.dec` with the role's first facts) as a hypothesis. -/
theorem sound (hpre : Pre P L mem0) (tm : Nat) (pro : Nat → Value) (htm : tm + 512 < 2 ^ 32)
    (hcol : tm + 512 ≤ 2 ^ 16)
    (hstart : ∃ t, Relation.ReflTransGen (Tau kernel asms L g) {} t ∧
      At t Flow.setMaxReg_7 (factsAt L Flow.setMaxReg_7 ⟨.setMaxReg, 0, 0, tm, pro⟩)) :
    (code asms L g tm pro).Sound where
  start := by
    obtain ⟨t, hr, ht⟩ := hstart
    exact ⟨t, hr, ht, by simp, htm, hcol, fun _ => rfl, fun h => False.elim h,
      fun h => False.elim h, fun h => absurd trivial h, (fun h => by cases h),
      fun h => False.elim h⟩
  steps := stepAt hpre tm pro

/-- **The return to the dispatch.** After `setmaxnreg.inc` the thread branches back to the worker
dispatch (`pc 2337`) with the registers of the prologue, which the dispatch's facts value by the
state's `pro` and the three registers the role's table gives. -/
theorem handoff (i n tm : Nat) (pro : Nat → Value)
    (h : At t (Site.setMaxRegInc).pc (facts L ⟨.setMaxRegInc, i, n, tm, pro⟩))
    (hc : kernel.code[(Site.setMaxRegInc).pc]? = some ins)
    (hf : Fires (Site.setMaxRegInc).pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧
      At t' Flow.setMaxReg_4 (factsAt L Flow.setMaxReg_4 ⟨.setMaxRegInc, i, n, tm, pro⟩) := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_8)
  obtain rfl := fires_next (show AdvancesOp (.setMaxReg _ _) from trivial) hf
  exact (SegE.rtg (s := 2556) (b := Flow.setMaxReg_4)
    ⟨1, fun t h => by ink_seg h⟩ (At.next h))

/-! ### The entry -/

/-- The registers of the prologue that are live at the role's `setmaxnreg`, and that the table
values itself (`%r2`, `%r3`, `%r73`), are those of the first state. -/
theorem entry_value (pro : Nat → Value) (tm : Nat) (h2 : pro 463 = b32 tm)
    (h73 : pro 534 = b32 L.sharedBase) {r : Nat} (hr : r ∈ common) :
    valueOf L ⟨.setMaxReg, 0, 0, tm, pro⟩ r = pro r := by
  simp only [common, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [valueOf, values, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none,
    h2, h73]

/-- **The entry.** A thread of the dispatch reaches the role's `setmaxnreg.dec` (pc 2422) with
the prologue's registers live there, valued by `pro`; if `pro` gives the Tensor Memory base (`%r2`)
a 32-bit value `tm` with room for the 512 columns and the shared base (`%r73`) the launch's (the
warp index `%r3` is carried as `pro` gives it), then those are the facts of the role's first
state, which satisfies the invariant. -/
theorem entry (pro : Nat → Value) (tm : Nat) (htm : tm + 512 < 2 ^ 32)
    (hcol : tm + 512 ≤ 2 ^ 16) (h2 : pro 463 = b32 tm) (h73 : pro 534 = b32 L.sharedBase)
    (h : At t Flow.setMaxReg_7 (Flow.factsFrom (Flow.live Flow.setMaxReg_7) pro)) :
    At t (Site.setMaxReg).pc (facts L ⟨.setMaxReg, 0, 0, tm, pro⟩) ∧
      Inv (⟨.setMaxReg, 0, 0, tm, pro⟩ : D) := by
  refine ⟨h.mono ?_, by simp, htm, hcol, fun _ => rfl, fun h => False.elim h, fun h => False.elim h,
    fun h => absurd trivial h, (fun h => by cases h), fun h => False.elim h⟩
  have hl : ∀ r ∈ Flow.live Flow.setMaxReg_7, r ∈ common := by table_decide
  refine Flow.holds_of_pointwise fun r hr => ?_
  rw [entry_value (L := L) pro tm h2 h73 (hl r hr)]
  exact holds_mem h.2.2.2.2 (Flow.mem_factsFrom hr)

end
end PTX.Kernels.InklingRelDecode.Proof.Mma
