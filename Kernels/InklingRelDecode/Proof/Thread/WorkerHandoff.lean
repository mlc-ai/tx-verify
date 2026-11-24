-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WorkerIdle
public import Kernels.InklingRelDecode.Proof.Thread.LoaderSound

@[expose] public section

/-! # The worker's hand-off to the loader, the MMA warp and the exit, and the return to the loop

The worker's states `toLoader` (pc 2344), `toMma` (pc 2422) and `toExit` (pc 2853) are the entries
of the roles the `brx.idx` dispatches to. A role's machine values the registers it inherits by
its own table over `Loader.Pro` (`Pro.val L g P`: the registers the loop reads are numbers, the
others are carried unchanged in `P.rest`). The worker's registers are the same table, with the
registers its own code computes (`Worker.own`) valued directly. So the worker's registers are
`Pro.val L g (handoff L g P)`, where `handoff` puts the worker's values of the registers into
`rest` (`valueOf_eq_handoff`), and `Rest` holds of it (`handoff_rest`).

* `toLoader` turns the worker's facts at pc 2344 into `Loader.entry`'s conclusion (the facts of
  the loader's first state and its invariant) for the loader's `Pro` `handoff L g P`.
* `toMma` states the same for pc 2422 against a `Pro`-style table: **the MMA role must accept the
  registers live at its entry (the 14 registers of `mmaRegs`) as `Pro.val L g (handoff L g P)`**,
  that is, the table of `Loader.Pro` with `P := handoff L g P`; `mma_values` lists their values.
* `toExit` gives the two registers live at the exit (`%p3` false, `%r2` the Tensor Memory word).
* `reenter` is the other direction: a role that ends at the dispatch loop's head with registers
  `Pro.val L g P'`, `Rest L g P'`, is at the worker's `loop` state with `P'`.
  `handoff_rest` says that the registers handed to a role satisfy `Rest`, so a role whose
  own table does not touch the registers of `own` hands them back unchanged.

The facts about the execution that remain for the protocol layer are those of `Worker.lean`: the
role byte of warp 6 is 0 and of warp 7 is 1, so that the dispatch reaches these states. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Worker
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Loader (Pro)

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- The inherited registers a role receives from the worker `P`: the worker's values of all
registers in `rest`. -/
def handoff (L : Launch) (g : Nat) (P : Pro) : Pro :=
  { P with rest := valueOf L g ⟨.loop, P⟩ }

/-- The registers live at the roles' entries (pc 2344, 2422, 2333 and the loop's head 2337). -/
def entryRegs : List Nat :=
  [3, 462, 463, 464, 465, 466, 528, 529, 530, 531, 532, 534, 1949, 2020]

theorem live_entry :
    Flow.live Flow.setMaxReg_5 = entryRegs ∧ Flow.live Flow.setMaxReg_7 = entryRegs ∧
      Flow.live Flow.setMaxReg_4 = entryRegs := by
  decide +kernel

/-- Off `%r75`, the worker's registers are those of the hand-off table. -/
theorem valueOf_eq_handoff (P : Pro) (s : Site) {r : Nat} (hr : r ∈ entryRegs) :
    Pro.val L g (handoff L g P) r = valueOf L g ⟨s, P⟩ r := by
  simp only [entryRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;>
    simp [Pro.val, Pro.table, handoff, valueOf, own, List.lookup]

/-- The registers handed to a role satisfy `Rest`. -/
theorem handoff_rest (P : Pro) (hp : Pins P) : Rest L g (handoff L g P) :=
  ⟨by simp [handoff, valueOf, own], by simp [handoff, valueOf, own, List.lookup],
    by simp [handoff, valueOf, own, List.lookup], by simp [handoff, valueOf, own, List.lookup],
    ⟨hp.bt, by simp [handoff, valueOf, own, List.lookup, Pro.val, Pro.table, hp.rd1], hp.w70⟩⟩

/-- A worker state's facts at a program counter whose live registers are the entry registers are
the facts of the hand-off table there. -/
theorem facts_handoff {pc : Nat} {s : TState} {x : Site} {P : Pro}
    (hl : Flow.live pc = entryRegs)
    (h : At s pc (factsAt L g pc ⟨x, P⟩)) :
    At s pc (Flow.factsFrom (Flow.live pc) (Pro.val L g (handoff L g P))) :=
  at_congr h fun _ hr => (valueOf_eq_handoff P x (hl ▸ hr)).symm

/-- **The hand-off to the loader**: the worker's facts at the loader's entry (pc 2344) are the
facts of the loader's first state for the loader's `Pro` `handoff L g P`, which satisfies the
loader's invariant. -/
theorem toLoader {P : Pro} {s : TState}
    (h : At s Site.toLoader.pc (facts L g ⟨.toLoader, P⟩)) :
    At s Loader.Site.setMaxDec.pc (Loader.facts L g (Loader.D.start L g (handoff L g P))) ∧
      Loader.Inv L g (Loader.D.start L g (handoff L g P)) :=
  Loader.entry (pv := valueOf L g ⟨.toLoader, P⟩) (handoff L g P)
    (fun _ hr => (valueOf_eq_handoff P .toLoader (live_entry.1 ▸ hr)).symm) h

/-- **The hand-off to the MMA warp**: the worker's facts at pc 2422 are the registers live there
valued by `Pro.val L g P'`, for the `Pro` `P' = handoff L g P`. The MMA role must accept its
entry registers in this form (`Loader.Pro` with `P'`), or restate them from `mma_values`. -/
theorem toMma {P : Pro} {s : TState}
    (h : At s Site.toMma.pc (facts L g ⟨.toMma, P⟩)) :
    At s Flow.setMaxReg_7
      (Flow.factsFrom (Flow.live Flow.setMaxReg_7) (Pro.val L g (handoff L g P))) :=
  facts_handoff live_entry.2.1 h

/-- The values of the MMA warp's entry registers, in closed form: `%p3` (thread index below 32),
the thread index `%r1`, the Tensor Memory word `%r2` and `%rd1` carried from `P`, the warp index
(`%r3`, `%r4`), `%r5 = %r71 << 7`, the parameter words `%r67 … %r71`, the shared base `%r73`
and the block-table base `%rd72`. -/
theorem mma_values (P : Pro) :
    Pro.val L g (handoff L g P) 3 = .pred (decide (g % L.block < 32)) ∧
    Pro.val L g (handoff L g P) 462 = b32 (g % L.block) ∧
    Pro.val L g (handoff L g P) 463 = P.rest 463 ∧
    Pro.val L g (handoff L g P) 464 = b32 (warpOf L g) ∧
    Pro.val L g (handoff L g P) 465 = b32 (warpOf L g) ∧
    Pro.val L g (handoff L g P) 466 = b32 (P.w71 * 128 % 2 ^ 32) ∧
    Pro.val L g (handoff L g P) 528 = b32 P.w67 ∧ Pro.val L g (handoff L g P) 529 = b32 P.w68 ∧
    Pro.val L g (handoff L g P) 530 = b32 P.w69 ∧ Pro.val L g (handoff L g P) 531 = b32 P.w70 ∧
    Pro.val L g (handoff L g P) 532 = b32 P.w71 ∧
    Pro.val L g (handoff L g P) 534 = .bits 32 (Loader.baseW L) ∧
    Pro.val L g (handoff L g P) 1949 = P.rest 1949 ∧
    Pro.val L g (handoff L g P) 2020 = b64 P.bt := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Pro.val, Pro.table, handoff, valueOf, own, List.lookup]

/-- **The exit's registers** (pc 2853: `%p3` and the Tensor Memory word `%r2`). -/
theorem toExit {P : Pro} {s : TState}
    (h : At s Site.toExit.pc (facts L g ⟨.toExit, P⟩)) (hw : 4 ≤ warpOf L g) :
    s.regs 3 = some (.pred false) ∧ s.regs 463 = some (P.rest 463) := by
  have hl : Flow.live Site.toExit.pc = [3, 463] := by decide +kernel
  have h3 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (show 3 ∈ Flow.live Site.toExit.pc by
    rw [hl]; simp))
  have h4 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (show 463 ∈ Flow.live Site.toExit.pc by
    rw [hl]; simp))
  refine ⟨?_, ?_⟩
  · rw [h3]
    simp [valueOf, own, p3_false hw]
  · rw [h4]
    simp [valueOf, own, List.lookup, Pro.val, Pro.table]

/-- **A role's return to the dispatch loop**: a thread at the loop's head (pc 2337) whose
registers are `Pro.val L g P'` on the entry registers, with `Rest L g P'`, is at the worker's
`loop` state with `P'` marked as a later round (`bumpPro`). -/
theorem reenter {P : Pro} (hR : Rest L g P) {s : TState}
    (h : At s Flow.setMaxReg_4 (Flow.factsFrom (Flow.live Flow.setMaxReg_4) (Pro.val L g P))) :
    At s Site.loop.pc (facts L g ⟨.loop, bumpPro P⟩) := by
  rw [facts_bumpPro_loop]
  refine at_congr h fun r hr => ?_
  have hr' : r ∈ entryRegs := live_entry.2.2 ▸ hr
  simp only [entryRegs, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;>
    simp [valueOf, own, List.lookup, Pro.val, Pro.table, hR.p3, hR.r3, hR.r4, hR.base]

end
end PTX.Kernels.InklingRelDecode.Proof.Worker
