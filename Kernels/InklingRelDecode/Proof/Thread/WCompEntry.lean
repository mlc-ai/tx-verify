-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WCompBase

@[expose] public section

/-!
# The worker thread machine: entries of the roles, the returns to the dispatch and the exit

The dispatch's successor is a role's first state: the worker's facts at the role's entry
(pc 2344 for the loader, 2422 for the MMA warp, 2333 for the idle role, 2853 for the exit) are
the role's first state's, valued by the table the role carries (`Worker.toLoader`,
`Worker.toMma`, `Worker.Idle.entry`, and `exit_entry` here). A role that ends returns to the
dispatch loop's head (pc 2337) with the registers `Pro.val L g P` of the `Pro` it was handed,
which is the worker's `loop` state when `Rest L g P` holds (`Worker.reenter`):
`loader_return`, `mma_return` and `idle_return` give that from each role's last event. The
exit's `bar.sync 0` (pc 2853) goes through the skipped, `%p3`-guarded `tcgen05.dealloc`
(pc 2854) to the `ret` (pc 2855), where no event follows and no register is live.

The registers of a role's table are the dispatch's on the registers live at the role's entry:
`loader_valueOf_eq` and `mma_valueOf_eq` state that for the loader's and the MMA warp's tables,
which override the inherited table at a few registers (`%r2` the Tensor Memory base word, `%r3`
the warp index, the shared base) with the same values. -/

namespace PTX.Kernels.InklingRelDecode.Proof.WComp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Loader (Pro Pro.val Pro.table)

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {Q : Params} {t u : TState} {e : Event} {ins : Instr}

/-! ### The shared base as a 32-bit word -/

/-- The shared base word `mov.b32 %r141, global_smem` is the launch's `sharedBase` when that is a
32-bit number. -/
theorem baseW_eq (h : L.sharedBase < 2 ^ 32) :
    Loader.baseW L = BitVec.ofNat 64 L.sharedBase := by
  unfold Loader.baseW
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, Nat.add_zero]
  omega

theorem live_bar37 : Flow.live ExitSite.bar.pc = [3, 463] := by decide +kernel

theorem live_exit0 : Flow.live ExitSite.ret.pc = [] := by decide +kernel

/-! ### The exit's registers -/

theorem exit_valueOf_3 (x : ExitD) (hw : 4 ≤ warpOf L g) :
    valueOf L g x 3 = Value.pred false := by
  simp [valueOf, Worker.valueOf, Worker.own, Worker.p3_false hw]

theorem exit_valueOf_463 (x : ExitD) : valueOf L g x 463 = x.P.rest 463 := by
  simp [valueOf, Worker.valueOf, Worker.own, Pro.val, Pro.table, PTX.Flow.lookupLit,
    Option.getD_none]

/-- **The exit's entry**: the worker's facts at pc 2853 (`%p3` false, `%r2` the Tensor Memory
word) are the exit's first state's. -/
theorem exit_entry {P : Pro} {s : TState} (hi : Worker.Inv L g ⟨.toExit, P⟩)
    (h : At s Worker.Site.toExit.pc (Worker.facts L g ⟨.toExit, P⟩)) :
    At s ExitSite.bar.pc (exitFacts L g ⟨.bar, P⟩) ∧ Inv L g (.exit ⟨.bar, P⟩) := by
  obtain ⟨h3, h4⟩ := Worker.toExit h hi.warp
  refine ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩, hi.warp, hi.tid⟩
  rw [exitFacts, exitFactsAt, live_bar37]
  simp only [Flow.factsFrom, List.map_cons, List.map_nil]
  refine ⟨?_, ?_, trivial⟩
  · rw [h3, exit_valueOf_3 ⟨.bar, P⟩ hi.warp]
  · rw [h4, exit_valueOf_463 ⟨.bar, P⟩]

/-! ### The idle role's entry and return -/

/-- **The idle role's entry**: the worker's facts at pc 2333 are the role's first state's. -/
theorem idle_entry {P : Pro} {s : TState} (hi : Worker.Inv L g ⟨.toIdle, P⟩)
    (h : At s Worker.Site.toIdle.pc (Worker.facts L g ⟨.toIdle, P⟩)) :
    At s Worker.Idle.Site.dec.pc (Worker.Idle.facts L g (Worker.Idle.D.start P)) ∧
      Inv L g (.idle (Worker.Idle.D.start P)) :=
  ⟨Worker.Idle.entry h, hi.warp, hi.tid, hi.pins⟩

/-! ### The loader's table at its entry -/

/-- Off its loop registers, the loader's table is the dispatch's. -/
theorem loader_valueOf_eq {d : Loader.D} {P : Pro}
    (hpro : Loader.ProEq L g P d) :
    ∀ r ∈ Worker.entryRegs, Loader.valueOf L g d r = Pro.val L g P r := by
  intro r hr
  have hk : r ∉ Loader.tableKeys ∧ r ≠ 1905 ∧ r ≠ 467 := by
    revert r
    decide +kernel
  rw [Loader.valueOf_pro hk.1]
  exact hpro r hk.2.1 hk.2.2

/-- **The loader's entry**: the worker's facts at pc 2344 are the loader's first state's for
the `Pro` the dispatch hands it, which satisfies the loader's invariant. -/
theorem loader_entry {P : Pro} {s : TState} (hi : Worker.Inv L g ⟨.toLoader, P⟩)
    (h : At s Worker.Site.toLoader.pc (Worker.facts L g ⟨.toLoader, P⟩)) :
    At s Loader.Site.setMaxDec.pc (Loader.facts L g (Loader.D.start L g (handoffPro L g P))) ∧
      Inv L g (.loader (Loader.D.start L g (handoffPro L g P)) (handoffPro L g P)) := by
  obtain ⟨h1, h2⟩ := Worker.toLoader h
  refine ⟨⟨h1.1, ?_, ?_, h1.2.2.2.1, h1.2.2.2.2⟩, h2, fun _ _ _ => rfl,
    Worker.handoff_rest P hi.pins, hi.warp, hi.tid⟩
  · rw [h1.2.1]
  · rw [h1.2.2.1]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **The loader's return**: after its last event (`setmaxnreg.inc`, pc 2420) the thread
branches to the dispatch loop's head (pc 2337) with the `Pro` it was handed; the registers live
there are the ones live at its last event, which the loader has not written. -/
theorem loader_return {d : Loader.D} {P : Pro} (hs : d.site = .setMaxInc)
    (hR : Worker.Rest L g P) (hpro : Loader.ProEq L g P d)
    (hi : Inv L g (.loader d P))
    (h : At t (Loader.Site.setMaxInc).pc (Loader.facts L g d))
    (hc : kernel.code[(Loader.Site.setMaxInc).pc]? = some ins)
    (hf : Fires (Loader.Site.setMaxInc).pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧
      At t' Worker.Site.loop.pc (Worker.facts L g ⟨.loop, Worker.bumpPro P⟩) ∧
      Inv L g (.worker ⟨.loop, Worker.bumpPro P⟩) := by
  have hfacts : Loader.facts L g d =
      Loader.factsAt L g (Loader.Site.setMaxInc).pc d := by
    simp only [Loader.facts, Loader.factsAt, hs]
  have h : At t (Loader.Site.setMaxInc).pc
      (Loader.factsAt L g (Loader.Site.setMaxInc).pc d) := hfacts ▸ h
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_6)
  obtain rfl := fires_next (show AdvancesOp (.setMaxReg _ _) from trivial) hf
  have h1 : At (PTX.next t) 2421 (Loader.factsAt L g (Loader.Site.setMaxInc).pc d) := At.next h
  have hseg : Seg kernel asms L g 1 2421 (Loader.factsAt L g (Loader.Site.setMaxInc).pc d)
      Worker.Site.loop.pc (Loader.factsAt L g (Loader.Site.setMaxInc).pc d) := fun t ht => by
    seg_fp ht using skip
  obtain ⟨t', hr, ht'⟩ := hseg _ h1
  have hl : Flow.live Worker.Site.loop.pc = Worker.entryRegs := Worker.live_entry.2.2
  have hl' : Flow.live (Loader.Site.setMaxInc).pc = Worker.entryRegs := by decide +kernel
  have ht'' : At t' Worker.Site.loop.pc
      (Flow.factsFrom Worker.entryRegs (Loader.valueOf L g d)) := by
    rw [← hl]; exact ht'
  refine ⟨t', run_rtg hr, Worker.reenter hR (at_congr ht'' fun r hr => ?_), hi.2.2.2.1,
    hi.2.2.2.2, hR.pins.bumpPro⟩
  exact loader_valueOf_eq hpro r hr

/-! ### The MMA warp's table at its entry -/

/-- The MMA warp's table is the dispatch's on the registers live at its entry, given the Tensor
Memory base word and the shared base it carries. -/
theorem mma_valueOf_eq {d : Mma.D} {P : Pro} (hR : Worker.Rest L g P)
    (hpro : ∀ r, r ≠ 471 → d.pro r = Pro.val L g P r) (h463 : d.pro 463 = b32 d.tm)
    (hb : Loader.baseW L = BitVec.ofNat 64 L.sharedBase) :
    ∀ r ∈ Worker.entryRegs, Mma.valueOf L d r = Pro.val L g P r := by
  intro r hr
  simp only [Worker.entryRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Mma.valueOf, Mma.values, PTX.Flow.lookupLit, Option.getD_none]
    exact hpro _ (by decide)
  · simp only [Mma.valueOf, Mma.values, PTX.Flow.lookupLit, Option.getD_none]
    exact hpro _ (by decide)
  · simp only [Mma.valueOf, Mma.values, PTX.Flow.lookupLit, Option.getD_some]
    rw [show Pro.val L g P 463 = d.pro 463 from (hpro 463 (by decide)).symm, h463]
  · simp only [Mma.valueOf, Mma.values, PTX.Flow.lookupLit, Option.getD_some]
    exact hpro _ (by decide)
  · simp only [Mma.valueOf, Mma.values, PTX.Flow.lookupLit, Option.getD_none]
    exact hpro _ (by decide)
  · simp only [Mma.valueOf, Mma.values, PTX.Flow.lookupLit, Option.getD_none]
    exact hpro _ (by decide)
  · simp only [Mma.valueOf, Mma.values, PTX.Flow.lookupLit, Option.getD_none]
    exact hpro _ (by decide)
  · simp only [Mma.valueOf, Mma.values, PTX.Flow.lookupLit, Option.getD_none]
    exact hpro _ (by decide)
  · simp only [Mma.valueOf, Mma.values, PTX.Flow.lookupLit, Option.getD_none]
    exact hpro _ (by decide)
  · simp only [Mma.valueOf, Mma.values, PTX.Flow.lookupLit, Option.getD_none]
    exact hpro _ (by decide)
  · simp only [Mma.valueOf, Mma.values, PTX.Flow.lookupLit, Option.getD_none]
    exact hpro _ (by decide)
  · simp only [Mma.valueOf, Mma.values, PTX.Flow.lookupLit, Option.getD_some, Pro.val,
      Pro.table, PTX.Flow.lookupLit, Option.getD_none, hR.base]
    rw [hb]
    rfl
  · simp only [Mma.valueOf, Mma.values, PTX.Flow.lookupLit, Option.getD_none]
    exact hpro _ (by decide)
  · simp only [Mma.valueOf, Mma.values, PTX.Flow.lookupLit, Option.getD_none]
    exact hpro _ (by decide)

/-- **The MMA role's entry**: the worker's facts at pc 2422 are the role's first state's, given
the Tensor Memory base word and the shared base, on any warp. -/
theorem mma_entry {P : Pro} {s : TState} (hi : Worker.Inv L g ⟨.toMma, P⟩)
    (h : At s Worker.Site.toMma.pc (Worker.facts L g ⟨.toMma, P⟩))
    {tm : Nat} (htm : tmOf (P.rest 463) = some tm) (htmb : tm + 512 < 2 ^ 32)
    (hcol : tm + 512 ≤ 2 ^ 16) (hb : Loader.baseW L = BitVec.ofNat 64 L.sharedBase) :
    At s Mma.Site.setMaxReg.pc
        (Mma.facts L ⟨.setMaxReg, 0, 0, tm, Pro.val L g (handoffPro L g P)⟩) ∧
      Inv L g (.mma ⟨.setMaxReg, 0, 0, tm, Pro.val L g (handoffPro L g P)⟩
        (handoffPro L g P)) := by
  obtain ⟨-, -, h463, h464, -, -, -, -, -, -, -, h534, -, -⟩ := Worker.mma_values P
  have h2 : Pro.val L g (handoffPro L g P) 463 = b32 tm := h463.trans (tmOf_spec htm)
  have h73 : Pro.val L g (handoffPro L g P) 534 = b32 L.sharedBase := h534.trans (by
    simp only [b32]; rw [hb])
  obtain ⟨h1, hi1⟩ := Mma.entry (Pro.val L g (handoffPro L g P)) tm htmb hcol h2 h73
    (Worker.toMma h)
  refine ⟨⟨h1.1, ?_, ?_, h1.2.2.2.1, h1.2.2.2.2⟩, hi1, fun _ _ => rfl,
    Worker.handoff_rest P hi.pins, h2, h464, hi.warp, hi.tid⟩
  · exact h1.2.1
  · exact h1.2.2.1

/-- **The MMA warp's return**: after its last event (`setmaxnreg.inc`, pc 2555) the thread
branches to the dispatch loop's head (pc 2337) with the `Pro` it was handed. -/
theorem mma_return {i n tm : Nat} {pro : Nat → Value} {P : Pro} (hR : Worker.Rest L g P)
    (hpro : ∀ r, r ≠ 471 → pro r = Pro.val L g P r) (h463 : pro 463 = b32 tm)
    (hb : Loader.baseW L = BitVec.ofNat 64 L.sharedBase)
    (hi : Inv L g (.mma ⟨.setMaxRegInc, i, n, tm, pro⟩ P))
    (h : At t (Mma.Site.setMaxRegInc).pc (Mma.facts L ⟨.setMaxRegInc, i, n, tm, pro⟩))
    (hc : kernel.code[(Mma.Site.setMaxRegInc).pc]? = some ins)
    (hf : Fires (Mma.Site.setMaxRegInc).pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧
      At t' Worker.Site.loop.pc (Worker.facts L g ⟨.loop, Worker.bumpPro P⟩) ∧
      Inv L g (.worker ⟨.loop, Worker.bumpPro P⟩) := by
  obtain ⟨t', hr, ht'⟩ := Mma.handoff i n tm pro h hc hf
  refine ⟨t', hr, Worker.reenter hR (at_congr ht' fun r hr' => ?_), hi.2.2.2.2.2.1,
    hi.2.2.2.2.2.2, hR.pins.bumpPro⟩
  exact mma_valueOf_eq (d := ⟨.setMaxRegInc, i, n, tm, pro⟩) hR hpro h463 hb r hr'

/-! ### The exit's step -/

/-- **The exit's `bar.sync 0`**: after it the thread skips the `%p3`-guarded
`tcgen05.dealloc` (pc 2854) and is at the `ret` (pc 2855), where no register is live. -/
theorem exit_bar_step {P : Pro} (hi : Inv L g (.exit ⟨.bar, P⟩))
    (h : At t ExitSite.bar.pc (exitFacts L g ⟨.bar, P⟩))
    (hc : kernel.code[ExitSite.bar.pc]? = some ins)
    (hf : Fires ExitSite.bar.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧
      At t' ExitSite.ret.pc (exitFacts L g ⟨.ret, P⟩) ∧
      Inv L g (.exit ⟨.ret, P⟩) := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_37)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSync _ _) from trivial) hf
  have hp3 : (3, Value.pred false) ∈ exitFacts L g ⟨.bar, P⟩ := by
    have hl : (3 : Nat) ∈ Flow.live ExitSite.bar.pc := by rw [live_bar37]; simp
    exact (exit_valueOf_3 ⟨.bar, P⟩ hi.1) ▸ Flow.mem_factsFrom hl
  have hseg : Seg kernel asms L g 1 (ExitSite.bar.pc + 1) (exitFacts L g ⟨.bar, P⟩)
      ExitSite.ret.pc (exitFacts L g ⟨.ret, P⟩) :=
    Seg.weaken_end (Seg.skip (K := kernel) (A := asms) (L := L) (g := g)
      (Flow.code_2854 : kernel.code[ExitSite.bar.pc + 1]? = _) hp3 rfl) fun R _ => by
        rw [exitFacts, exitFactsAt, live_exit0]; trivial
  obtain ⟨t', hr, ht'⟩ := hseg _ (At.next h)
  exact ⟨t', run_rtg hr, ht', hi⟩

end
end PTX.Kernels.InklingRelDecode.Proof.WComp
