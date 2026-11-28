-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Table
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.LoopGlueU
public import Lemmas.Flow.GlueU
public import Lemmas.Flow.CountedU
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Sound
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Steps
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Steps
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Steps.All
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.StepAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Steps
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Steps

@[expose] public section

/-! # The thread machine is sound (UB-tolerant)

`thread_sound`: the glued, counted thread machine follows every launched thread through any final
undefined behaviour (`Code.SoundU`), from the startup's start and steps (`Startup.stepAt_all`),
warpgroup 1's dispatch level (`Code.roleLoop_stepsU`: the head, the idle code, the MMA, TMA
and index warps), warpgroup 0's control machine (`Wg0.Control.stepAt`),
warpgroup 2's control machine (`Dequant.Control.stepAt`), and the hand-offs:

* the startup to a warpgroup: the warpgroup's `setmaxnreg` with the entry registers
  (`Lib/Entry.lean`), the same terms as the startup's table (`startup_wg1`, `startup_dequant`);
* the head to a sub-role: the MMA warp's election and the TMA warp's at pcs 1853 and 2165 with the
  entry registers (`head_mma`, `head_tma`), the idle code's first event with its own table (by
  definition), the index warp's first event with its control table (by definition: the head's
  index exit carries `ixFacts` at `ixFirst`);
* an MMA or TMA lane that lost its election back to the head's idle exit (`mmaLeave`,
  `tmaLeave`): the machine's losing step walks on to the idle code's first event (`idleFirst`)
  with the idle code's registers. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- Every warpgroup's and sub-role's first instruction is an unguarded event instruction. -/
theorem entry_sites (r : Entry) : StubSite kernel r.pc = true := by
  cases r <;> decide +kernel

/-- Every site of the index warp is an unguarded event instruction. -/
theorem ix_sites (s : IxSite) : StubSite kernel s.pc = true := by
  cases s <;> decide +kernel

theorem sub_sites (r : SubEntry) : StubSite kernel (SubEntry.pc P L g r) = true := by
  cases r
  · show StubSite kernel 1853 = true; decide +kernel
  · show StubSite kernel 2165 = true; decide +kernel
  · show StubSite kernel (ixFirst P L g).1.pc = true
    exact ix_sites _
  · simp only [SubEntry.pc, idleFirst, idleAfterA]
    split_ifs <;> decide +kernel

/-- The startup's facts at an entry's pc give the entry registers. -/
theorem startup_entry {d : Startup.D} {t : TState} {pc : Nat} (hs : d.site.pc = pc)
    (hat : (Startup.code L g).AtD d t)
    (hl : ∀ r ∈ Flow.live pc, r ∈ Startup.liveAt pc ∧
      Startup.valueOf L g d r = entryVal L g r) :
    Holds t.regs (Flow.factsFrom (Flow.live pc) (entryVal L g)) := by
  obtain ⟨-, -, -, -, hF⟩ := hat
  change Holds t.regs (Flow.factsFrom (Startup.liveAt d.site.pc) _) at hF
  rw [hs] at hF
  refine holds_of_pointwise fun r hr => ?_
  obtain ⟨h1, h2⟩ := hl r hr
  rw [← h2]
  exact holds_mem hF (mem_factsFrom h1)

/-- **The hand-off to warpgroup 1's head**: the startup's facts at pc 1842. -/
theorem startup_wg1 {d : Startup.D} {t : TState} (hs : d.site = .enter .wg1)
    (hat : (Startup.code L g).AtD d t) : (Wg1.code P L g).AtD .smr t := by
  obtain ⟨site, x1, x2⟩ := d
  simp only at hs
  subst hs
  obtain ⟨h1, h2, h3, h4⟩ := atD_stop hat rfl rfl rfl
  refine ⟨h1, h2, h3, h4, ?_⟩
  refine startup_entry (pc := 1842) rfl hat fun r hr => ?_
  have hl : Flow.live 1842 = [459, 460, 461, 464, 466, 2990, 2991] := by decide +kernel
  rw [hl] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide +kernel, rfl⟩

/-- **The hand-off to warpgroup 2**: the startup's facts at pc 2606 are the dequantizer's first
facts. -/
theorem startup_dequant {d : Startup.D} {t : TState} {w : BitVec 64} (hs : d.site = .enter .wg2)
    (hat : (Startup.code L g).AtD d t) :
    (Dequant.Control.code P L g w).AtD (Dequant.Control.code P L g w).init t := by
  obtain ⟨site, x1, x2⟩ := d
  simp only at hs
  subst hs
  obtain ⟨h1, h2, h3, h4⟩ := atD_stop hat rfl rfl rfl
  refine ⟨h1, h2, h3, h4, ?_⟩
  have hl : Flow.live 2606 = [460, 461, 463, 2991] := by decide +kernel
  have hF := startup_entry (pc := 2606) rfl hat fun r hr => by
    rw [hl] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨by decide +kernel, rfl⟩
  have hc : Dequant.Control.ctlLive 2606 = [460, 461, 463, 2991] := by decide +kernel
  change Holds t.regs (Flow.factsFrom (Dequant.Control.ctlLive 2606) _)
  rw [hc]
  rw [hl] at hF
  exact hF

/-- **The hand-off to warpgroup 0**: the startup's facts at pc 103, with the warp word the
gate checks, are the control machine's first facts. -/
theorem startup_wg0 {d : Startup.D} {t : TState} (hs : d.site = .enter .wg0)
    (hx : d.x2 = warpW L g) (hat : (Startup.code L g).AtD d t) :
    (Wg0.Control.code P L g (warpW L g)).AtD (Wg0.Control.code P L g (warpW L g)).init t := by
  obtain ⟨site, x1, x2⟩ := d
  simp only at hs hx
  subst hs hx
  have hF := atD_holds hat
  obtain ⟨h1, h2, h3, h4⟩ := atD_stop hat rfl rfl rfl
  refine ⟨h1, h2, h3, h4, ?_⟩
  change Holds t.regs (Flow.factsFrom (Startup.liveAt 103) _) at hF
  change Holds t.regs (Flow.factsFrom (Wg0.Control.ctlLive 103) _)
  refine holds_of_pointwise fun r hr => ?_
  have hl : Wg0.Control.ctlLive 103 = [459, 460, 461, 463, 465, 466, 2880, 2990, 2991] := by
    decide +kernel
  rw [hl] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact holds_mem hF (mem_factsFrom (by decide +kernel))

/-- **The hand-off to the MMA warp**: the head's facts at pc 1853 are the MMA warp's first
facts. -/
theorem head_mma {t : TState} (hat : (Wg1.code P L g).AtD .mma t) :
    (Mma.code P L g).AtD (Mma.code P L g).init t := by
  have hF := atD_holds hat
  obtain ⟨h1, h2, h3, h4, -⟩ := hat
  refine ⟨h1, h2, h3, h4, ?_⟩
  change Holds t.regs (Flow.factsFrom (Flow.live 1853) (entryVal L g)) at hF
  refine holds_of_pointwise fun r hr => ?_
  change r ∈ Flow.live 1853 at hr
  have hl : Flow.live 1853 = [459, 460, 793, 794, 2990, 2991] := by decide +kernel
  have hm := holds_mem hF (mem_factsFrom hr)
  rw [hl] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hm

/-- **The hand-off to the TMA warp**: the head's facts at pc 2165 are the TMA warp's first
facts. -/
theorem head_tma {t : TState} (hat : (Wg1.code P L g).AtD .tma t) :
    (Tma.code P L g).AtD (Tma.code P L g).init t := by
  have hF := atD_holds hat
  obtain ⟨h1, h2, h3, h4, -⟩ := hat
  refine ⟨h1, h2, h3, h4, ?_⟩
  change Holds t.regs (Flow.factsFrom (Flow.live 2165) (entryVal L g)) at hF
  refine holds_of_pointwise fun r hr => ?_
  change r ∈ Flow.live 2165 at hr
  have hm := holds_mem hF (mem_factsFrom hr)
  rw [show Flow.live 2165 = [460, 662, 663, 2990, 2991] by decide +kernel] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hm

/-- **Warpgroup 1's dispatch level obeys its UB-tolerant step obligations.** -/
theorem wg1_steps (hp : Pre P L m) : ∀ d, (wg1Code P L g).StepAtU d := by
  refine Code.roleLoop_stepsU (fun d hx => ?_) (fun i d _ => ?_) (fun d r hx _ => ?_)
    (fun d r i t hx hs hat _ => ?_) (fun i d p t hb hat _ => ?_) (fun i => ?_)
  · refine Wg1.stepAt_head hp d ?_
    simpa [wg1Enter] using hx
  · cases i with
    | mma => exact (Mma.stepAt hp d).toStepAtU
    | tma => exact Tma.stepAt hp d
    | index => exact Index.stepAt d
    | idle => exact (Wg1.stepAt_idle hp d).toStepAtU
  · refine ⟨?_, ?_, ?_, sub_sites r⟩
    · cases d <;> simp only [wg1Enter, Wg1.exitOf, Option.map_some, Option.map_none,
        Option.some.injEq, reduceCtorEq] at hx <;> subst hx <;> rfl
    · cases d <;> rfl
    · cases d <;> rfl
  · simp only [subSel] at hs
    split_ifs at hs
    simp only [Option.some.injEq] at hs
    subst hs
    cases d <;> simp only [wg1Enter, Wg1.exitOf, Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq] at hx <;> subst hx
    · exact ⟨head_mma hat, trivial⟩
    · exact ⟨head_tma hat, trivial⟩
    · exact ⟨hat, Index.IxSite.elems_pos _⟩
    · exact ⟨hat, trivial⟩
  · cases i with
    | mma =>
      simp only [subBack] at hb
      split_ifs at hb with hl
      cases hb
      exact ⟨mmaLeave d t hl hat, trivial⟩
    | tma =>
      simp only [subBack] at hb
      split_ifs at hb with hl
      cases hb
      exact ⟨tmaLeave d t hl hat, trivial⟩
    | _ => cases hb
  · cases i <;> rfl

/-- The startup's first state is reached from the empty state. -/
theorem startup_start (hp : Pre P L m) : ∃ t, Relation.ReflTransGen (Tau kernel Assumptions.all L g)
    {} t ∧ (startupCode P L g).AtD (startupCode P L g).init t ∧
      (startupCode P L g).inv (startupCode P L g).init := by
  obtain ⟨t, hr, ha, hi⟩ := Startup.start (g := g) hp
  exact ⟨t, hr, ha, hi⟩

/-- The startup's steps at its states that are not exits. -/
theorem startup_steps (hp : Pre P L m) (d : (startupCode P L g).D)
    (hx : Code.gatedExit (startupEnter P L g) (sel P L g) d = none) :
    (startupCode P L g).StepAt d :=
  Startup.stepAt_all hp d (by simpa [Code.gatedExit, startupEnter] using hx)

/-- The fragments' (UB-tolerant) steps, the stubs' included. -/
theorem frag_stepsU (hp : Pre P L m) :
    ∀ j d, (Code.withStubs (frag P L g) Entry.pc j).StepAtU d
  | .inl .wg0, d => Wg0.Control.stepAt hp d
  | .inl .dequant, d => Dequant.Control.stepAt (w := warpW L g) hp d
  | .inl .wg1, d => wg1_steps hp d
  | .inr r, d => (Code.stop_steps (entry_sites r) d).toStepAtU

/-- **The hand-offs of the startup** to the warpgroups (`startup_wg0`, `startup_wg1`,
`startup_dequant`) and to the stubs. -/
theorem thread_handoff :
    Code.Handoff (startupCode P L g) (Code.withStubs (frag P L g) Entry.pc)
      (Code.gatedExit (startupEnter P L g) (sel P L g)) :=
  Code.handoff_gated
    (fun d r hx _ => by
      obtain ⟨site, x1, x2⟩ := d
      cases site with
      | enter q =>
        cases q <;> simp only [startupEnter, Startup.exitOf, Option.map_some,
          Option.some.injEq] at hx <;> subst hx <;> exact ⟨rfl, rfl, rfl⟩
      | _ => simp [startupEnter, Startup.exitOf] at hx)
    (fun d r i t hx hs hat _ => by
      simp only [sel] at hs
      split_ifs at hs with hgate
      simp only [Option.some.injEq] at hs
      subst hs
      obtain ⟨site, x1, x2⟩ := d
      cases site with
      | enter q =>
        cases q <;> simp only [startupEnter, Startup.exitOf, Option.map_some,
          Option.some.injEq] at hx <;> subst hx
        · exact ⟨startup_wg0 rfl hgate.2 hat, Nat.one_pos⟩
        · exact ⟨startup_wg1 (P := P) rfl hat, trivial, rfl⟩
        · exact ⟨startup_dequant (w := warpW L g) rfl hat, Nat.one_pos⟩
      | _ => simp [startupEnter, Startup.exitOf] at hx)

/-- **The thread machine of every launched thread is sound**, through any final undefined
behaviour (the MMA lanes' hand-back is `mmaLeave`). -/
theorem thread_sound (hp : Pre P L m) :
    (thread P L g).SoundU :=
  Code.counted_soundU (Code.glue_soundU (startup_start hp)
    (fun d hx => (startup_steps hp d hx).toStepAtU) (frag_stepsU hp) thread_handoff)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
