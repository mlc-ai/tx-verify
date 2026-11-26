-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Contract
public import Kernels.FlashKdaFwd.Proof.Values.Ends.Contract

@[expose] public section

/-! # Epilogue phase: its share of the value layer's contract for the final state

The value layer's files for the two ends of the tile loop (`Proof/Values/Ends/`) take from the
epilogue where a compute thread stores its carry registers and how the store leader's tensor
stores pair the shared bytes with the bytes of the final state. This file proves those
statements for a thread in the epilogue (`Entered`, `Exports.lean`), in the vocabulary of
`Values/Ends/Defs.lean` and `Contract.lean`.

**The two descriptions agree** (evaluated on the tables, and by arithmetic):
`carryReg_eq` (entry `j` of the value layer's table `carryTable` names the register that store
`j` stores, `stSrc j`), `carryConst_eq` (its constant is `stOff j`), `laneOff_eq`
(`4 * laneOff tid = carryBase tid`), `swzAddr_eq` (`swzAddr` is this phase's `swzN`),
`finalSite_eq` (`finalSite j` is the site of position `st j`); `site_inj`: a site of the
epilogue is the site of one position.

**`FinalRef`**: `final_site` (a write event of the epilogue has seven `bar.sync 0` before it,
is a compute thread's, and its state is at a final-store site), `final_store` (the footprint of
the write at `finalSite j`), `final_first` (a state at `finalSite j` before event `k` is `j`
events after a state at `finalSite 0`).

**`StoreCtl.final`**: `final_ctl` (at `finalSite j`, if the carry register converts to a 32-bit
payload, the event is the write of exactly those bytes; the address never faults).

**The slots of the final-state stores** (`final_slots`): for a tensor store of the epilogue, a
slot that writes byte `b` of the entry `(v, k)` of the final state of `(s, h)` reads the shared
byte `swzAddr (shared_mem + 32768 + 4 * elemOf v k) + b` of the block of `(s, h)`; and
`final_slot_owner`: that byte was written by compute thread `32 (v / 32) + 4 (k % 8) + v / 2 %
4` of the block (`finalOwner`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Frame
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol
open PTX.Kernels.FlashKdaFwd.Proof.Values.Ends (carryReg carryConst laneOff swzAddr finalSite
  elemOf)

noncomputable section
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat} {e : Event}

/-! ### The two descriptions agree -/

theorem carryReg_eq : ∀ j : Fin 128, carryReg j.val = stSrc j.val := by decide +kernel

theorem carryConst_eq : ∀ j : Fin 128, carryConst j.val = stOff j.val := by decide +kernel

theorem laneOff_eq (t : Nat) : 4 * laneOff t = carryBase t := by
  unfold laneOff carryBase
  omega

theorem swzAddr_eq (a : Nat) : swzAddr a = swzN a := (swzN_eq_swzAbs a).symm

theorem finalSite_eq (j : Fin 128) : finalSite j = (Pos.st j).site := rfl

/-- The address of store `j` in the value layer's words. -/
theorem stAddr_eq (hpre : Pre P L mem0) (j : Fin 128) :
    stAddr P g j.val = swzAddr (L.sharedBase + 4 * laneOff (g % L.block) + carryConst j.val) := by
  rw [swzAddr_eq, laneOff_eq, carryConst_eq j, hpre.sharedBase, block_mod hpre]
  rfl

/-- A site of the epilogue is the site of one position. -/
theorem site_inj {pos pos' : Pos} (h : pos.site = pos'.site) : pos = pos' := by
  cases pos <;> cases pos' <;> simp only [Pos.site, Site.store.injEq, Site.tensorCopy.injEq,
    Site.bar.injEq, Fin.mk.injEq, reduceCtorEq] at h <;>
    first
    | rfl
    | (congr 1; exact Fin.ext (by omega))
    | exact absurd h (by decide)

/-- **The compute thread that wrote the shared byte of such a slot**: thread
`32 (v / 32) + 4 (kk % 8) + v / 2 % 4` of the block (`finalOwner`). -/
theorem final_slot_owner (hpre : Pre P L mem0) (v kk : Fin 128) {b : Nat} (hb : b < 4)
    (c : Nat) :
    finalOwner P ⟨.shared, c, swzAddr (L.sharedBase + 32768 + 4 * elemOf v.val kk.val) + b⟩ =
      32 * (v.val / 32) + 4 * (kk.val % 8) + v.val / 2 % 4 := by
  have hk := kk.isLt
  have hv := v.isLt
  have ha := hpre.sharedAlignment
  rw [swzAddr_eq, hpre.sharedBase, ← swzN_add (by unfold elemOf; omega) hb]
  have e1 : P.sharedBase + 32768 + 4 * elemOf v.val kk.val + b =
      P.sharedBase + 32768 + 4096 * (kk.val / 8) + 32 * v.val + 4 * (kk.val % 8) + b := by
    unfold elemOf
    omega
  rw [e1]
  exact final_read_owner ⟨kk.val / 8, by omega⟩ (Nat.mod_lt _ (by decide)) hv hb c

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads) {k0 : Nat} (hE : Entered P L X g k0)
include hpre hX hg hE

/-! ### `FinalRef` -/

/-- `FinalRef.site`: a write event of the epilogue has seven `bar.sync 0` before it and is an
event of a compute thread at one of the 128 final-store sites. -/
theorem final_site {k pc : Nat} {a : Acc} {bs : List Byte} (hk : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) :
    bar0Before X (g, k) = 7 ∧ g % L.block < 128 ∧
      ∃ d, ∃ j : Fin 128, stateAt (code L) X g k = some (some d) ∧ d.site = finalSite j := by
  obtain ⟨s, j, hσ, hs, ht, -, -, -, -, hb⟩ := wr_in hpre hX hg hE hk he
  rw [block_mod hpre]
  exact ⟨hb, ht, s, j, hσ, hs⟩

/-- `FinalRef.store`: the write of the `j`-th final store is of the four bytes at the address
of the `j`-th carry. -/
theorem final_store {k pc : Nat} {d : D} {a : Acc} {bs : List Byte} {j : Fin 128} (hk : k0 ≤ k)
    (hσ : stateAt (code L) X g k = some (some d)) (hs : d.site = finalSite j)
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) :
    a.size = 4 ∧ a.loc = ⟨.shared, g / L.block,
      swzAddr (L.sharedBase + 4 * laneOff (g % L.block) + carryConst j.val)⟩ := by
  obtain ⟨s, j', hσ', hs', -, -, -, rfl, -, -⟩ := wr_in hpre hX hg hE hk he
  rw [hσ] at hσ'
  obtain rfl := Option.some.inj (Option.some.inj hσ')
  obtain rfl : j = j' := by
    have h := site_inj (pos := .st j) (pos' := .st j') (by rw [← hs', ← finalSite_eq, hs])
    cases h
    rfl
  exact ⟨rfl, by rw [← stAddr_eq hpre j]⟩

/-- `FinalRef.first`: the final stores are consecutive events. -/
theorem final_first {k : Nat} {d : D} {j : Fin 128} (hk : k0 ≤ k) (hle : k ≤ (X.tr g).length)
    (hσ : stateAt (code L) X g k = some (some d)) (hs : d.site = finalSite j) :
    j.val ≤ k ∧ ∃ d0, stateAt (code L) X g (k - j.val) = some (some d0) ∧
      d0.site = finalSite 0 := by
  obtain ⟨s0, h0, hin⟩ := hE
  obtain ⟨pos, hr, hon, hkp, -⟩ := epilogue_weak hpre hX hg h0 hin hk hle hσ
  obtain rfl : pos = .st j := site_inj (by rw [← hr.site, hs, finalSite_eq])
  have hkj : k = k0 + 1 + j.val := by rw [hkp]; simp only [ord]; omega
  refine ⟨by omega, ?_⟩
  rcases Nat.eq_zero_or_pos j.val with hj0 | hjp
  · obtain rfl : j = 0 := Fin.ext hj0
    exact ⟨d, by simpa using hσ, hs⟩
  · obtain ⟨s1, hσ1, pos1, hr1, hon1, hkp1, -⟩ :=
      epilogue_all hpre hX hg h0 hin (k := k0 + 1) (by omega) (by omega)
    obtain rfl : pos1 = .st 0 := ord_inj hon1 (show tid g < 128 from hon) (by
      show ord g pos1 = 1 + 0
      omega)
    exact ⟨s1, by rw [show k - j.val = k0 + 1 by omega]; exact hσ1, hr1.site⟩

/-! ### `StoreCtl.final` -/

/-- `StoreCtl.final`: at a final-store site, if the carry register converts to a 32-bit
payload, the event is the write of exactly those bytes. -/
theorem final_ctl {k : Nat} {d : D} {j : Fin 128} (hk : k0 ≤ k)
    (hσ : stateAt (code L) X g k = some (some d)) (hs : d.site = finalSite j)
    (he : X.get (g, k) = some e) {v' : Value}
    (hv : storeValue 32 (d.x (carryReg j.val)) = .ok v') :
    ∃ a, e = ⟨d.site.pc, .wr a v'.toBytes⟩ := by
  obtain ⟨s, pos, hσ', -, hr, -, -, -, -, hex⟩ := event_in hpre hX hg hE hk he
  rw [hσ] at hσ'
  obtain rfl := Option.some.inj (Option.some.inj hσ')
  obtain rfl : pos = .st j := site_inj (by rw [← hr.site, hs, finalSite_eq])
  rw [carryReg_eq j] at hv
  rcases hex with ⟨v, hv1, rfl⟩ | ⟨f, hf, -⟩
  · rw [hv] at hv1
    cases hv1
    exact ⟨_, by rw [hs, finalSite_eq]⟩
  · rw [hv] at hf
    cases hf

/-! ### The slots of the final-state stores -/

/-- **The shared byte of a slot of a final-state store**: a slot of a tensor store of the
epilogue that writes byte `b` of the entry `(v, kk)` of the final state of `(s, h)` reads byte
`b` of the swizzled entry `elemOf v kk` of the FP32 buffer of the block of `(s, h)`. -/
theorem final_slots {k pc al x y z s h b : Nat} {sp : TensorStore.Spec} {v kk : Fin 128}
    (hk : k0 ≤ k) (hh : h < P.heads) (hb : b < 4)
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩)
    (hw : TensorStore.writeLoc sp x y z = some ((P.stateLoc s h v kk).at b)) :
    TensorStore.readLoc sp x y z = some ⟨.shared, blockOf P s h,
      swzAddr (L.sharedBase + 32768 + 4 * elemOf v.val kk.val) + b⟩ := by
  obtain ⟨-, -, rfl, rfl, i, rfl, hx, rfl, hkk, rfl⟩ := ts_state hpre hX hg hE hk hh hb he hw
  have hi := i.isLt
  have ha := hpre.sharedAlignment
  rw [final_readLoc hpre i hx v.isLt hb, blockOf_own hpre, swzAddr_eq, hpre.sharedBase]
  have e1 : P.sharedBase + 32768 + 4096 * i.val + 32 * v.val + 4 * x + b =
      P.sharedBase + 32768 + 4 * elemOf v.val kk.val + b := by
    unfold elemOf
    omega
  rw [e1, swzN_add (by unfold elemOf; omega) hb]

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
