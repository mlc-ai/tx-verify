-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Cnt
public import Lemmas.Flow.Step.ShapeClasses
public import Lemmas.Flow.Step.ShapeTc
public import Lemmas.Flow.Step.Record
public import Lemmas.Flow.Next
public import Lemmas.Flow.Step.SegSym
public import Lemmas.Flow.LoadNcAt
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # The index warp's events by state

`shape`: the event a state of the index warp fires is its site's (`Ev.lean`). The loads and
shuffles by their instruction class; the polls, arrivals and stores by the control table's
address and parity registers (`ixLoop`); the arrivals' words are 8-byte aligned (`ready_m8`), so
an arrival does not fault. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The slot's `valid_coord_ready` word is 8-byte aligned. -/
theorem ready_m8 (hp : Pre P L m) (c : IxCtl) :
    (truncBits 32 (truncBits 32 (readyW L c) + BitVec.ofInt 64 0)).toNat % 8 = 0 :=
  trunc_add_mod8 (m8_addi (m8_add32 (m8_sbw hp) (m8_shl3 _)) (by decide)) (by decide)

/-- A 32-bit read of a register holding a word. -/
theorem readW {t : TState} {r w : Nat} {x : BitVec 64} (h : t.regs r = some (.bits w x)) :
    readBits L g t 32 (.reg r) = .ok (truncBits 32 x) := by
  simp [readBits, readReg, h, bind, Except.bind, pure, Except.pure]

set_option hygiene false in
/-- Open the shape obligation of the state `d` at the site `hs` names. -/
macro "ix_open" : tactic => `(tactic| (
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  intro t ins e o hat hi hc hf
  obtain ⟨hpc, hsub, -, -, hF⟩ := hat
  dsimp only [Flow.Code.AtD, code, IxSite.pc] at hpc hsub hc hF hf hi ⊢
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  simp only [EvK, NcEv, NcAt, PollEv, ShflEv, StoreEv]))

set_option hygiene false in
/-- A register's fact at an opened site. -/
macro "rg " r:num : term => `(regs_of_factsFrom hF (r := $r) (by decide +kernel))

/-- An element of an index pair's load, at its address register's word. -/
theorem shapeAt_pairLd (d : D) {s : IxSite} (hs : d.site = s)
    (hn : s = .pre ∨ s = .pf ∨ s = .xpre ∨ s = .xpf) :
    (code P L g).ShapeAt (EvK P L g) d := by
  rcases hn with rfl | rfl | rfl | rfl <;> ix_open <;>
    change Fires _ (loadTmpl Assumptions.all L g t .global true 32 _ _ 0) e o at hf
  · simpa only [hsub, Nat.reduceDiv] using fires_ncLoad_at (rg 3033) hf
  · simpa only [hsub, Nat.reduceDiv] using fires_ncLoad_at (rg 4029) hf
  · simpa only [hsub, Nat.reduceDiv] using fires_ncLoad_at (rg 3041) hf
  · simpa only [hsub, Nat.reduceDiv] using fires_ncLoad_at (rg 3043) hf

/-- A length's `.nc` load. -/
theorem shapeAt_nc (d : D) {s : IxSite} (hs : d.site = s) (hn : s = .lenA ∨ s = .lenB) :
    (code P L g).ShapeAt (EvK P L g) d := by
  rcases hn with rfl | rfl <;> ix_open <;>
  · refine shape_cont (P := fun e : Event => (∃ a bs, e.kind = .nc a bs) ∨ ∃ f, e.kind = .ub f)
      hf ⟨nofun, nofun⟩ (fun u hf' => ?_) (fun f => .inr ⟨f, rfl⟩)
    rw [← hpc] at hf'
    obtain ⟨loc, bs, -, he, -⟩ := Code.fires_nc rfl rfl rfl rfl rfl rfl (by rw [hpc]; decide) hf'
    exact .inl ⟨loc, bs, by rw [he]⟩

/-- A butterfly shuffle. -/
theorem shapeAt_shfl (d : D) {s : IxSite} (hs : d.site = s)
    (hn : s = .sA1 ∨ s = .sA2 ∨ s = .sB1 ∨ s = .sB2) : (code P L g).ShapeAt (EvK P L g) d := by
  rcases hn with rfl | rfl | rfl | rfl <;> ix_open <;>
  · refine shape_cont (P := fun e : Event =>
      (∃ a b c r ok, e.kind = .shfl .bfly a b c r ok) ∨ ∃ f, e.kind = .ub f)
      hf ⟨nofun, nofun⟩ (fun u hf' => ?_) (fun f => .inr ⟨f, rfl⟩)
    obtain ⟨av, bv, cv, recv, ok, he, -⟩ := fires_shfl (p := some _) hf'
    exact .inl ⟨av, bv, cv, recv, ok, by rw [he]⟩

/-- A poll of `valid_coord_free[slot]`. -/
theorem shapeAt_wait (d : D) {s : IxSite} (hs : d.site = s) (hn : s = .wA ∨ s = .wB) :
    (code P L g).ShapeAt (EvK P L g) d := by
  rcases hn with rfl | rfl <;> ix_open
  · exact fires_wait_reg (by rw [hpc]; decide) (rg 585) (rg 586) hf
  · exact fires_wait_reg (by rw [hpc]; decide) (rg 623) (rg 624) hf

/-- An element of the coordinate pair's store. -/
theorem shapeAt_pair (d : D) {s : IxSite} (hs : d.site = s) (hn : s = .stA ∨ s = .stB) :
    (code P L g).ShapeAt (EvK P L g) d := by
  rcases hn with rfl | rfl <;> ix_open
  · change Fires _ (storeTmpl L g t .shared _ _ 221728 _) e o at hf
    have h := fires_store_el (rg 612) hf
    rw [hsub] at h
    exact h
  · change Fires _ (storeTmpl L g t .shared _ _ 221728 _) e o at hf
    have h := fires_store_el (rg 651) hf
    rw [hsub] at h
    exact h

/-- The validity byte. -/
theorem shapeAt_byte (d : D) {s : IxSite} (hs : d.site = s) (hn : s = .bA ∨ s = .bB) :
    (code P L g).ShapeAt (EvK P L g) d := by
  rcases hn with rfl | rfl <;> ix_open
  · change Fires _ (storeTmpl L g t .shared _ _ 221696 _) e o at hf
    have h := fires_store_el (rg 613) hf
    rw [hsub, show el = 0 by change el < 1 at hi; omega] at h
    exact h
  · change Fires _ (storeTmpl L g t .shared _ _ 221696 _) e o at hf
    have h := fires_store_el (rg 652) hf
    rw [hsub, show el = 0 by change el < 1 at hi; omega] at h
    exact h

/-- An arrival on `valid_coord_ready[slot]`. -/
theorem shapeAt_arr (hp : Pre P L m) (d : D) {s : IxSite} (hs : d.site = s)
    (hn : s = .arrA ∨ s = .arrB) : (code P L g).ShapeAt (EvK P L g) d := by
  rcases hn with rfl | rfl <;> ix_open
  · exact shape_arrive
      (P := fun e : Event => e.kind = .arrive (smLoc L g (readyW L c) 0) 0 1 true .cta)
      hf (by rw [hpc]; decide) rfl rfl (mbarLoc_bits (rg 614) (ready_m8 hp c)) rfl
  · exact shape_arrive
      (P := fun e : Event => e.kind = .arrive (smLoc L g (readyW L c) 0) 0 1 true .cta)
      hf (by rw [hpc]; decide) rfl rfl (mbarLoc_bits (rg 653) (ready_m8 hp c)) rfl

/-- Named barrier 12 of the whole CTA. -/
theorem shapeAt_bar (hp : Pre P L m) (d : D) (hs : d.site = .bar) :
    (code P L g).ShapeAt (EvK P L g) d := by
  ix_open
  exact shape_barSyncN_block (P := fun e : Event => e.kind = .bar 12 none .sync) hf
    (readW (rg 659)) (by decide) (readW (rg 660)) (by rw [hp.block]; rfl) (by rw [hp.block])
    rfl

/-- The exit. -/
theorem shapeAt_exit (d : D) (hs : d.site = .exit) : (code P L g).ShapeAt (EvK P L g) d := by
  ix_open
  simp only [eventTmpl, Fires] at hf
  exact congrArg Event.kind hf.1

/-- The event kind a state of the index warp fires is its site's. -/
theorem shapeK (hp : Pre P L m) : (code P L g).Shape (EvK P L g) := by
  refine Code.Shape.of_at fun d => ?_
  cases hs : d.site with
  | lenA => exact shapeAt_nc d hs (.inl rfl)
  | lenB => exact shapeAt_nc d hs (.inr rfl)
  | pre => exact shapeAt_pairLd d hs (.inl rfl)
  | pf => exact shapeAt_pairLd d hs (.inr (.inl rfl))
  | xpre => exact shapeAt_pairLd d hs (.inr (.inr (.inl rfl)))
  | xpf => exact shapeAt_pairLd d hs (.inr (.inr (.inr rfl)))
  | wA => exact shapeAt_wait d hs (.inl rfl)
  | wB => exact shapeAt_wait d hs (.inr rfl)
  | sA1 => exact shapeAt_shfl d hs (.inl rfl)
  | sA2 => exact shapeAt_shfl d hs (.inr (.inl rfl))
  | sB1 => exact shapeAt_shfl d hs (.inr (.inr (.inl rfl)))
  | sB2 => exact shapeAt_shfl d hs (.inr (.inr (.inr rfl)))
  | stA => exact shapeAt_pair d hs (.inl rfl)
  | stB => exact shapeAt_pair d hs (.inr rfl)
  | bA => exact shapeAt_byte d hs (.inl rfl)
  | bB => exact shapeAt_byte d hs (.inr rfl)
  | arrA => exact shapeAt_arr hp d hs (.inl rfl)
  | arrB => exact shapeAt_arr hp d hs (.inr rfl)
  | bar => exact shapeAt_bar hp d hs
  | exit => exact shapeAt_exit d hs

/-- **The event a state of the index warp fires is the event of its site, at its pc.** -/
theorem shape (hp : Pre P L m) : (code P L g).Shape (Ev P L g) :=
  fun hat hi hc hf => ⟨fires_pc hf, shapeK hp hat hi hc hf⟩

/-- The counted machine's shape table. -/
theorem shape_counted (hp : Pre P L m) : (IC P L g).Shape (fun d e => Ev P L g d.1 e) :=
  Code.Shape.counted (shape hp)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
