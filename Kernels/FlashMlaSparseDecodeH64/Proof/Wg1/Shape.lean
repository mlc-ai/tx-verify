-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Seg
public import Lemmas.Flow.Step.SiteShape
public import Lemmas.Flow.Step.ShapeClasses

@[expose] public section

/-! # Warpgroup 1's head and idle code: their events by state

The head's `setmaxnreg` releases registers down to 72; its shuffle sends the warp index as the
code computes it (`%tid.x >> 5`) from lane 0; the exits fire their sub-roles' events. The idle
code's two loads are `.nc` loads (or undefined behaviour), its barrier is named barrier 12 over
384 threads (the CTA, so the event names no count), its last event the return. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false

/-- The event-shape table of the head. -/
def Ev (L : Launch) (g : Nat) (s : Site) (e : Event) : Prop :=
  match s with
  | .smr => ∃ inst, e.kind = .setMaxReg false 72 inst
  | .hsh => ∃ r ok, e.kind = .shfl .idx (w32 (shru (tw L g) 5)) 0 31 r ok
  | _ => True

/-- The event-shape table of the idle code. -/
def IEv (s : IdleSite) (e : Event) : Prop :=
  match s with
  | .ldA | .ldB => (∃ a bs, e.kind = .nc a bs) ∨ ∃ f, e.kind = .ub f
  | .bar => e.kind = .bar 12 none .sync
  | .ret => e.kind = .exit

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The event a state of the head fires is the event of its site.** -/
theorem shape (hp : Pre P L m) : (code P L g).Shape (Ev L g) := by
  refine Code.Shape.of_at fun s => ?_
  site_shape s
    skip_by (intro _ _ _ _ _ _ _ _; exact trivial)
    unfolding [Ev]
    reg_vals [headVal, entryVal, entryVals, lookupLit]
    addr_by (rw [hp.block])

theorem ishapeAt_bar (hp : Pre P L m) : (idle P L g).ShapeAt IEv .bar := by
  intro t ins e o hat _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2604)
  have h1 : t.regs 923 = some (w32 (i32 12)) :=
    holds_mem (atD_holds hat) (mem_factsFrom (by decide +kernel))
  have h2 : t.regs 924 = some (w32 (i32 384)) :=
    holds_mem (atD_holds hat) (mem_factsFrom (by decide +kernel))
  exact shape_barSyncN_block (id := i32 12) (n := i32 384) hf
    (by simp only [readBits, readReg, h1]; rfl) (by decide)
    (by simp only [readBits, readReg, h2]; rfl) (by rw [hp.block]; decide) (by rw [hp.block])
    (by simp only [IEv]; rfl)

/-- **The event a state of the idle code fires is the event of its site.** -/
theorem ishape (hp : Pre P L m) : (idle P L g).Shape IEv := by
  refine Code.Shape.of_at fun s => ?_
  site_shape s except [.bar => (fun {_ _ _ _} => ishapeAt_bar hp)]
    unfolding [IEv]
    reg_vals [idleVal, idleVals, entryVal, entryVals, lookupLit]
    addr_by (rw [hp.block])

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
