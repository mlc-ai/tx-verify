-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Steps

@[expose] public section

/-! # The events of the Conversion phase, in closed form

`Ev P g pos d e`: what the event `e` fired at a state `d` of position `pos` is.

* `fence` (`fence.proxy.async.shared::cta`): the proxy fence;
* `ld j u` (the generic `ld.b32 %r, [%rd]`): a read of the four bytes at the swizzled address
  of the element (`rdAddr`), in the FP32 buffer of the thread's own block;
* `st j u` (`st.shared.b16 [%r], %rs`): a write of the two bytes of the element's slot of
  `state_acc` (`wrAddr`), whose bytes are `storeValue 16` of the narrowed value; or, when that
  value does not convert to 16 bits, undefined behaviour;
* `bar j` (`bar.sync 0`): the barrier arrival.

`ev_at`: the event fired at a state of the invariant is the position's. Three of the four
kinds are exact: at a fence, a load and a barrier the event is never undefined behaviour (the
load's address is a multiple of four inside the block's window: `rdAddr_frame`). At a store
the event is undefined behaviour exactly when `storeValue 16` of the stored register faults,
which is a condition on the data (the register holds the outcome of `cvt.rn.bf16.f32`): the
value layer excludes it.

The element at a position is `slotOf g (elemIx j u)`; `elem_lt` bounds it by 16384 and
`slotOf_elem` relates it to the form the invariant uses (`slot0 g (u + q)` and that plus
one). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
  {t : TState} {ins : Instr} {e : Event} {o : Option TState}

/-! ### The element of a position -/

/-- The round condition of load or store `j`: a round of the first loop (`j < 2`) or of the
second. -/
def Round (g j u : Nat) : Prop :=
  if j < 2 then u < head g else ∃ m, m < 10 ∧ u = head g + 4 * m

/-- The opaque slot of the swizzled pointer of load `j` (`%rd53`, `%rd59`, `%rd67`, …). -/
def ptrReg (j : Nat) : Nat :=
  [2299, 2305, 2313, 2319, 2325, 2331, 2337, 2343, 2349, 2355].getD j 0

/-- The register of the address of store `j` (`%r248`, `%r256`, `%r279`, …). -/
def adrReg (j : Nat) : Nat := [554, 562, 585, 593, 607, 615, 629, 637, 651, 659].getD j 0

/-- The element at load or store `j` of a round, in the form of the invariant. -/
theorem slotOf_elem (g j u : Nat) : slotOf g (elemIx j u) = slot0 g (u + qOf j) + j % 2 := by
  unfold slotOf elemIx
  have e1 : (2 * (u + qOf j) + j % 2) / 2 = u + qOf j := by omega
  have e2 : (2 * (u + qOf j) + j % 2) % 2 = j % 2 := by omega
  rw [e1, e2]

theorem ld_round {j : Fin 10} {u : Nat} {d : D} (h : AtPos P g (.ld j u) d) :
    Round g j.val u := by
  fin_cases j <;> exact h.2.1.1

theorem st_round {j : Fin 10} {u : Nat} {d : D} (h : AtPos P g (.st j u) d) :
    Round g j.val u := by
  fin_cases j <;> exact h.2.1.1

/-- The pair of a position is one of the thread's pairs. -/
theorem round_lt {j u : Nat} (hj : j < 10) (h : Round g j u) : u + qOf j < pairs g := by
  have hhd := head_le g
  unfold Round at h
  unfold pairs
  have hq : qOf j ≤ 3 ∧ (j < 2 → qOf j = 0) := by
    interval_cases j <;> simp [qOf]
  split_ifs at h with h2
  · omega
  · obtain ⟨m, hm, rfl⟩ := h
    omega

/-- **The element of a position is below 16384.** -/
theorem elem_lt {j u : Nat} (hj : j < 10) (h : Round g j u) :
    slotOf g (elemIx j u) < 16384 := by
  rw [slotOf_elem]
  have := slot0_lt (round_lt hj h)
  omega

/-- The ordinal of the element of a position is one of the thread's. -/
theorem elemIx_lt {j u : Nat} (hj : j < 10) (h : Round g j u) : elemIx j u < 2 * pairs g := by
  have := round_lt hj h
  unfold elemIx
  omega

/-- The pointer of a load position: the swizzled address of the position's element. -/
theorem ld_ptr {j : Fin 10} {u : Nat} {d : D} (h : AtPos P g (.ld j u) d) :
    d.x (ptrReg j.val) = sptr g (rdAddr P (slotOf g (elemIx j.val u))) := by
  rw [slotOf_elem]
  fin_cases j <;>
    (simp only [AtPos, finVal] at h
     repeat (obtain ⟨-, h⟩ := h)
     exact h)

/-- The address register of a store position: the slot of the position's element. -/
theorem st_adr {j : Fin 10} {u : Nat} {d : D} (h : AtPos P g (.st j u) d) :
    d.w (adrReg j.val) = W (wrAddr P (slotOf g (elemIx j.val u))) := by
  rw [slotOf_elem]
  fin_cases j <;>
    (simp only [AtPos, finVal] at h
     repeat (obtain ⟨-, h⟩ := h)
     exact h)

/-! ### The events -/

/-- **The event of a position**, in closed form. -/
def Ev (P : Params) (g : Nat) : Pos → D → Event → Prop
  | .fence, _, e => e = ⟨387, .fenceProxy (.async (some (.shared .cta))) none⟩
  | .ld j u, _, e => ∃ bs, bs.length = 4 ∧ e = ⟨(Pos.ld j u).site.pc,
      .rd { loc := ⟨.shared, cta g, rdAddr P (slotOf g (elemIx j.val u))⟩, size := 4 } bs⟩
  | .st j u, d, e =>
    (∃ v', storeValue 16 (d.x (nrReg j.val)) = .ok v' ∧ e = ⟨(Pos.st j u).site.pc,
      .wr { loc := ⟨.shared, cta g, wrAddr P (slotOf g (elemIx j.val u))⟩, size := 2 }
        v'.toBytes⟩) ∨
    (∃ f, storeValue 16 (d.x (nrReg j.val)) = .error f ∧ e = ⟨(Pos.st j u).site.pc, .ub f⟩)
  | .bar j, _, e => e = ⟨(Pos.bar j).site.pc, .bar 0 none .sync⟩

/-- `ld_ev r d`: the event of the load through the pointer slot `r` into the slot `d`. -/
syntax "ld_ev " num num : tactic
set_option hygiene false in
macro_rules
  | `(tactic| ld_ev $r $d) => `(tactic| (
      obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      have r1 := (reg_x hat (r := $r) (by lit_mem) rfl).trans (congrArg some hx)
      exact ev_gld hpre hg (d := $d) hf r1 f4 f3 hat.2.1))

/-- `st_ev r s`: the event of the store through the address register `r` of the slot `s`. -/
syntax "st_ev " num num : tactic
set_option hygiene false in
macro_rules
  | `(tactic| st_ev $r $s) => `(tactic| (
      obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      have r1 := (reg_w hat (r := $r) (by lit_mem) (n := 32) rfl).trans
        (congrArg (fun z => some (Value.bits 32 z)) ha)
      have r2 := reg_x hat (r := $s) (by lit_mem) rfl
      exact ev_sst hpre hf r1 r2 f4 f3 hat.2.1))

set_option maxRecDepth 8000 in
/-- **The event of a state of the invariant is the position's.** -/
theorem ev_at (hpre : Pre P L mem0) (hg : g < L.threads) (pos : Pos)
    (h : RefAt P g pos ⟨pos.site, w, p, x⟩) (hat : (code L g).AtD ⟨pos.site, w, p, x⟩ t)
    (hc : kernel.code[pos.site.pc]? = some ins)
    (hf : Fires pos.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Ev P g pos ⟨pos.site, w, p, x⟩ e := by
  cases pos with
  | fence =>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact ev_fence hf
  | ld j u =>
    have hx := ld_ptr h.pos
    obtain ⟨f1, f2, f3, f4⟩ := rdAddr_frame hpre (elem_lt j.isLt (ld_round h.pos))
    fin_cases j
    · ld_ev 2299 539
    · ld_ev 2305 540
    · ld_ev 2313 564
    · ld_ev 2319 565
    · ld_ev 2325 566
    · ld_ev 2331 567
    · ld_ev 2337 568
    · ld_ev 2343 569
    · ld_ev 2349 570
    · ld_ev 2355 571
  | st j u =>
    have ha := st_adr h.pos
    obtain ⟨f1, f2, f3, f4⟩ := wrAddr_frame hpre (elem_lt j.isLt (st_round h.pos))
    fin_cases j
    · st_ev 554 96
    · st_ev 562 97
    · st_ev 585 98
    · st_ev 593 99
    · st_ev 607 100
    · st_ev 615 101
    · st_ev 629 102
    · st_ev 637 103
    · st_ev 651 104
    · st_ev 659 105
  | bar j =>
    fin_cases j
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      exact ev_bar0 hf
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      exact ev_bar0 hf

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion
