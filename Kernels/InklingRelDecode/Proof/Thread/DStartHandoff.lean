-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DStartStart

@[expose] public section

/-! # The hand-off from the common start to the prologue

The common start ends at the `setmaxnreg.inc` of pc 27, which is the prologue machine's first
event (`ProA.D.start`: site `sMax`). `ProA.entry` starts at pc 20, after the common code's
`@!%p4 bra`, with the facts `ProA.factsAt L g 20 (ProA.Dat.start P)`, and runs the seven
`ld.param` of pc 20 to 26 to pc 27. This file states the link in three forms, for the inherited
registers `P = inh L g Q tm`, `tm` the Tensor Memory base word the machine read:

* `handoff20`: after the event of the shuffle (the machine's last event but one) the thread
  reaches pc 20 with `ProA.factsAt L g 20 (ProA.Dat.start (inh L g Q (ProA.shW tm)) tm)`;
* `handoff27`: and then pc 27 with `ProA.facts L g (ProA.D.start (inh L g Q (ProA.shW tm)) tm)`;
* `good_toProA`, `reach_toProA`: a concrete state of the machine's last site `toProA` is a
  concrete state of `ProA.code`'s first one (the same facts: `facts_toProA`), and the same for the
  machine's `Reach`.

`ProA.sound` itself cannot be applied to a thread that has fired events: its start hypothesis is
a run of local steps from the empty state, and the barriers and the shuffle are events. A machine
that composes this one with `ProA.code` takes `good_toProA` for the link, and `ProA.stepAt` for
every prologue state.

## What is discharged and what stays a premise

`ProA.ArgsOk L g (inh L g Q tm)` is discharged field by field from `Pre` and the thread's being in
the default partition (`argsOk_inh`: `tid < 128` is the machine's own hypothesis, `Inv.args`; the
`num_splits` word positive, below `2 ^ 31` and above `ctaid.x`; the words `x0, x6, x8, x9, x10,
x11, x15, x16, x17, x25` of the parameters `Pre.param*`). The fields of the inherited registers
`ProA.Inh` are set by the machine: `rest 3 = %p3 = (tid < 32)` (`inh_rest3`) and `rest 1950 =
%rd1` (the address of the kernel parameter `param_1`), `w67 … w71` and `btB` (the words the code
loaded at pc 0 to 7: `Q.strideBt`, `Q.pageRows`, `Q.headRows`, `Q.headCols`, `Q.splits`
modulo `2 ^ 32`, and `Q.btBase`), and `tm` (the base word: below `2 ^ 32` by `Inv.tm`).
`inh_w71` is the premise `hs` of `SmEntry` (`w71 = Q.splits`).

Not discharged, by `next = some none` (the protocol layer must show it does not happen): the load
of the base word returns a 32-bit value below `2 ^ 32` (what the allocation stored: `b32 col`,
`col < 2 ^ 16`), and the shuffle returns the warp index. -/

namespace PTX.Kernels.InklingRelDecode.Proof.DStart
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {Q : Params} {mem0 : Mem0} {tm : Value} {t u : TState} {e : Event}
  {ins : Instr}

/-! ### The inherited registers -/

/-- `%p3` of the inherited registers is `tid < 32`: the premise `hp3` of `SmEntry`. -/
theorem inh_rest3 {tm : Nat} : (inh L g Q tm).rest 3 = .pred (decide (g % L.block < 32)) := by
  simp [inh]

/-- `%r71` of the inherited registers is `num_splits`: the premise `hs` of `SmEntry`. -/
theorem inh_w71 {tm : Nat} (hpre : Pre Q L mem0) : (inh L g Q tm).w71 = Q.splits :=
  Nat.mod_eq_of_lt (by have := hpre.splitsRange; omega)

/-- The registers of the prologue's first state are the machine's at its last site. -/
theorem facts_toProA : facts L g Q ⟨.toProA, tm⟩ =
    ProA.facts L g (ProA.D.start (inh L g Q (ProA.shW tm)) tm) := by
  show Flow.factsFrom (Flow.live 27) (valueOf L g Q tm) =
    Flow.factsFrom (Flow.live 27) (ProA.valueOf L g (ProA.Dat.start (inh L g Q (ProA.shW tm)) tm))
  simp only [Flow.factsFrom]
  exact List.map_congr_left fun r hr => by rw [bridge27 tm r hr]

/-! ### The hand-off after the shuffle -/

/-! ### The link between the two machines -/

/-- **A concrete state of the machine's last site is one of the prologue's first.** -/
theorem good_toProA (hi : Inv L g Q ⟨.toProA, tm⟩)
    (h : (code L g Q).Good (some ⟨.toProA, tm⟩) t) :
    (ProA.code L g (inh L g Q (ProA.shW tm))).Good
      (some (ProA.D.start (inh L g Q (ProA.shW tm)) tm)) t := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, -⟩ := h
  refine ⟨⟨h1, h2, h3, h4, ?_⟩, ProA.inv_start hi.args⟩
  have : Holds t.regs (facts L g Q ⟨.toProA, tm⟩) := h5
  rwa [facts_toProA] at this

end
end PTX.Kernels.InklingRelDecode.Proof.DStart
