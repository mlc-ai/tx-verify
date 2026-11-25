-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Stage
public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Progress

@[expose] public section

/-!
# Where the states of each phase are, and how many `bar.sync 0` precede them

`Stage.lean` says which phase a followed state `s` of thread `g` is in. This file says, for
each phase, at which instructions its states are (`s.site.pc`: the index of the instruction of
the state's site) and how many `bar.sync 0` events the thread has made before the state, and
derives the inverse: the instruction of a followed state decides its phase.

**Words.** The kernel has nine `bar.sync 0` instructions (`Protocol.bar0Pcs`: 85, 110, 379,
620, 621, 1402, 3113, 3775, 3834). `bar0Of pc` of the progress layer is
`(bar0Pcs.filter (· < pc)).length`: the number of them below instruction `pc`. The count of a
thread's earlier `bar.sync 0` events is `((X.tr g).take k).countP (Execution.isBarId 0)`,
which is `Protocol.bar0Before X (g, k)` by definition (`bar0Before_eq`).

## Instruction ranges (`s.site.pc`)

| phase | lemma | from | instructions |
|---|---|---|---|
| startup | `pc_startup` | `Startup.Inv` | at most 384 |
| conversion | `pc_conversion` | `Conversion.Inv` | 387 to 621 |
| carry loads | `pc_carryLoad` | `CarryLoad.Inv` | 765 to 1401 |
| compute loop | `pc_compute` | `Compute.Inv` | 1402, or 2106 to 2944 |
| load loop | `pc_producer` | `Producer.Inv` | 1402 to 2105 (`Producer.region_producer`) |
| store loop | `pc_store` | `StoreWeak` | 1402, or 2945 to 3113 |
| epilogue | `pc_epilogue` | `Epilogue.InvW` | 3113 to 3835 |

The store loop's line is from the weak invariant, so it holds at every followed state; the
instruction 3113 in it is the phase's exit state seen through the weak invariant (only at the
state after a thread's last event, when that event is undefined behaviour; otherwise a state
at 3113 is in the epilogue).

`Stage.pc_cases` is the table as one statement. The inverses `Stage.of_pc_startup`,
`of_pc_conversion`, `of_pc_carryLoad`, `of_pc_producer`, `of_pc_compute`, `of_pc_store`,
`of_pc_epilogue` give, from the instruction of a state, the phase with its invariant and (for
the tile loops) the role. `region` is the field `region` of the progress contract
(`Proof/Schedule/Contract.lean`): which roles are at the instructions of the three tile
loops, for every followed state.

## `bar.sync 0` counts

`Stage.bar0`: at a state of any phase the thread has made `bar0Of s.site.pc` earlier
`bar.sync 0` (the field `bar0` of the progress contract; `bar0` is the same for a followed
state at any position). For the Store phase this needs the guard `NoUb X g k` (the phase's
ledger is part of its guarded invariant). Per phase:
`Startup.bar0_startup`, `bar0_conversion`, `bar0_carryLoad`, `bar0_compute`,
`Producer.bar0_producer`, `bar0_store`, `bar0_epilogue`. In numbers (`Stage.bar0_bounds`): at
most 3 in the startup; 3 or 4 in the Conversion phase (3 up to the barrier of instruction 620,
4 at the one of 621); 5 in the CarryLoad phase; 5 at the entry of a tile loop (the state at
1402) and 6 inside it; 6, 7, 8, 9 in the epilogue (6 at 3113; 7 up to 3775; 8 up to 3834; 9 at
the `ret`).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol (bar0Pcs)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### Counting the `bar.sync 0` instructions below an instruction -/

/-- The protocol layer's count of a thread's earlier `bar.sync 0` events is the count used
here. -/
theorem bar0Before_eq (X : Execution) (g k : Nat) :
    Protocol.bar0Before X (g, k) = ((X.tr g).take k).countP (Execution.isBarId 0) := rfl

/-- **The number of `bar.sync 0` instructions below an instruction of a stretch without one**:
if no `bar.sync 0` instruction is in `[lo, hi)`, every instruction from `lo` to `hi` has as
many below it as `lo`. -/
theorem bar0_range {lo hi n pc : Nat} (hn : (bar0Pcs.filter (· < lo)).length = n)
    (hfree : ∀ x ∈ bar0Pcs, x < lo ∨ hi ≤ x) (h1 : lo ≤ pc) (h2 : pc ≤ hi) :
    (bar0Pcs.filter (· < pc)).length = n := by
  rw [← hn]
  congr 1
  refine List.filter_congr fun x hx => ?_
  rcases hfree x hx with h | h
  · rw [decide_eq_true (by omega : x < pc), decide_eq_true h]
  · rw [decide_eq_false (by omega : ¬ x < pc), decide_eq_false (by omega : ¬ x < lo)]

/-! ### The instructions of the positions of each phase -/

/-- The positions of the startup phase are at the instructions up to 384. -/
theorem startup_pos_pc (pos : Startup.Pos) : pos.site.pc ≤ 384 := by
  rcases pos with j | j | j | j | j | j | _ | j | _ <;> (try fin_cases j) <;> decide

theorem conv_load_pc : ∀ j : Fin 10,
    387 < (Site.load ⟨21 + j.val, by omega⟩).pc ∧ (Site.load ⟨21 + j.val, by omega⟩).pc < 620 := by
  decide

theorem conv_store_pc : ∀ j : Fin 10,
    387 < (Site.store ⟨j.val, by omega⟩).pc ∧ (Site.store ⟨j.val, by omega⟩).pc < 620 := by
  decide

/-- **The instruction of a position of the Conversion phase**: 620 or 621 at the two
barriers, from 387 to 619 elsewhere. -/
theorem conversion_pos_pc (pos : Conversion.Pos) :
    (∃ j : Fin 2, pos = .bar j ∧ pos.site.pc = 620 + j.val) ∨
      ((Conversion.led g pos).bars = 3 ∧ 387 ≤ pos.site.pc ∧ pos.site.pc < 620) := by
  cases pos with
  | fence => exact .inr ⟨rfl, by decide, by decide⟩
  | ld j u => exact .inr ⟨rfl, Nat.le_of_lt (conv_load_pc j).1, (conv_load_pc j).2⟩
  | st j u => exact .inr ⟨rfl, Nat.le_of_lt (conv_store_pc j).1, (conv_store_pc j).2⟩
  | bar j => exact .inl ⟨j, rfl, by fin_cases j <;> rfl⟩

/-- The carry loads are at the instructions 765 to 1400. -/
theorem carry_ld_pc : ∀ j : Fin 128,
    765 ≤ (CarryLoad.ldSite j.val).pc ∧ (CarryLoad.ldSite j.val).pc ≤ 1400 := by
  decide +kernel

/-- The positions of the CarryLoad phase are at the instructions 765 to 1401. -/
theorem carryLoad_pos_pc (pos : CarryLoad.Pos) : 765 ≤ pos.site.pc ∧ pos.site.pc ≤ 1401 := by
  cases pos with
  | ld j => exact ⟨(carry_ld_pc j).1, Nat.le_succ_of_le (carry_ld_pc j).2⟩
  | fence => exact ⟨by decide, by decide⟩

/-- The instruction of the sites of a kind of the Compute phase (the bytes that the second
event of an `ldmatrix` or `stmatrix` site carries do not change its instruction). -/
def skPc : Compute.SK → Nat
  | .wait j => (Site.mbarWait j).pc
  | .ld j => (Site.matrixLoad j).pc
  | .ldMx j => (Site.matrixLoadMx j []).pc
  | .mma j => (Site.warpMma j).pc
  | .mv j => (Site.matrixMove j).pc
  | .st j => (Site.matrixStore j).pc
  | .stWr j => (Site.matrixStoreWr j []).pc
  | .load j => (Site.load j).pc
  | .bar j => (Site.bar j).pc
  | .fence j => (Site.fenceProxy j).pc
  | .arrive j => (Site.mbarArrive j).pc

theorem skPc_at {k : Compute.SK} {s : Site} (h : k.At s) : s.pc = skPc k := by
  cases k <;> simp only [Compute.SK.At] at h
  all_goals first
    | (subst h; rfl)
    | (obtain ⟨row, rfl⟩ := h; rfl)

/-- The 268 positions of a tile of the Compute phase are at the instructions 2106 to 2944. -/
theorem compute_tile_pc : ∀ n < 268,
    2106 ≤ skPc (Compute.skOf n) ∧ skPc (Compute.skOf n) ≤ 2944 := by
  decide +kernel

theorem store_ts_pc : ∀ i : Fin 16,
    2945 ≤ (Site.tensorCopy ⟨226 + i.val, by omega⟩).pc ∧
      (Site.tensorCopy ⟨226 + i.val, by omega⟩).pc ≤ 3112 := by
  decide

theorem store_gst_pc : ∀ j : Fin 8,
    2945 ≤ (Site.store ⟨10 + j.val, by omega⟩).pc ∧
      (Site.store ⟨10 + j.val, by omega⟩).pc ≤ 3112 := by
  decide

/-- **The instruction of a position of the Store phase**: 1402 at the entry, from 2945 to 3112
elsewhere. -/
theorem store_pos_pc (pos : Store.Pos) :
    (pos = .entry ∧ pos.site.pc = 1402) ∨
      (pos ≠ .entry ∧ 2945 ≤ pos.site.pc ∧ pos.site.pc ≤ 3112) := by
  have hld : 2945 ≤ (Site.load 177).pc ∧ (Site.load 177).pc ≤ 3112 := by decide
  cases pos with
  | entry => exact .inl ⟨rfl, rfl⟩
  | wait t =>
    exact .inr ⟨by simp, (by decide : 2945 ≤ (Site.mbarWait 9).pc ∧ (Site.mbarWait 9).pc ≤ 3112)⟩
  | ts t i => exact .inr ⟨by simp, store_ts_pc i⟩
  | commit t =>
    exact .inr ⟨by simp,
      (by decide : 2945 ≤ (Site.bulkCommit 0).pc ∧ (Site.bulkCommit 0).pc ≤ 3112)⟩
  | ld0 t row c => exact .inr ⟨by simp, hld⟩
  | ld1 t row c v0 => exact .inr ⟨by simp, hld⟩
  | ld2 t row c v0 v1 => exact .inr ⟨by simp, hld⟩
  | ld3 t row c v0 v1 v2 => exact .inr ⟨by simp, hld⟩
  | gst t row c j => exact .inr ⟨by simp, store_gst_pc j⟩
  | bwait t =>
    exact .inr ⟨by simp, (by decide : 2945 ≤ (Site.bulkWait 0).pc ∧ (Site.bulkWait 0).pc ≤ 3112)⟩
  | arrive t =>
    exact .inr ⟨by simp,
      (by decide : 2945 ≤ (Site.mbarArrive 6).pc ∧ (Site.mbarArrive 6).pc ≤ 3112)⟩

theorem epi_st_pc : ∀ j : Fin 128,
    3113 < (Site.store ⟨18 + j.val, by omega⟩).pc ∧
      (Site.store ⟨18 + j.val, by omega⟩).pc ≤ 3775 := by
  decide +kernel

theorem epi_ts_pc : ∀ i : Fin 16,
    3775 < (Site.tensorCopy ⟨242 + i.val, by omega⟩).pc ∧
      (Site.tensorCopy ⟨242 + i.val, by omega⟩).pc ≤ 3834 := by
  decide

/-- **The instruction of a position of the epilogue**, by the number of `bar.sync 0` before
the position: 3113 with six; up to 3775 with seven; up to 3834 with eight; 3835 with nine. -/
theorem epilogue_pos_pc (pos : Epilogue.Pos) :
    (Epilogue.bars pos = 6 ∧ pos.site.pc = 3113) ∨
    (Epilogue.bars pos = 7 ∧ 3113 < pos.site.pc ∧ pos.site.pc ≤ 3775) ∨
    (Epilogue.bars pos = 8 ∧ 3775 < pos.site.pc ∧ pos.site.pc ≤ 3834) ∨
    (Epilogue.bars pos = 9 ∧ pos.site.pc = 3835) := by
  cases pos with
  | bar7 => exact .inl ⟨rfl, rfl⟩
  | st j => exact .inr (.inl ⟨rfl, epi_st_pc j⟩)
  | fence => exact .inr (.inl ⟨rfl, by decide, by decide⟩)
  | bar8 => exact .inr (.inl ⟨rfl, by decide, by decide⟩)
  | ts i => exact .inr (.inr (.inl ⟨rfl, epi_ts_pc i⟩))
  | commit => exact .inr (.inr (.inl ⟨rfl, by decide, by decide⟩))
  | bwait => exact .inr (.inr (.inl ⟨rfl, by decide, by decide⟩))
  | bar9 => exact .inr (.inr (.inl ⟨rfl, by decide, by decide⟩))
  | exit => exact .inr (.inr (.inr ⟨rfl, rfl⟩))

/-! ### The instructions of the states of each phase -/

section
variable {k j0 : Nat} {s : D}

/-- A state of the startup phase is at an instruction up to 384. -/
theorem pc_startup (hI : Startup.Inv P X g k s) : s.site.pc ≤ 384 := by
  obtain ⟨pos, hr, -⟩ := hI
  rw [hr.site]
  exact startup_pos_pc pos

/-- A state of the Conversion phase is at an instruction from 387 to 621. -/
theorem pc_conversion (hI : Conversion.Inv P X g j0 k s) :
    387 ≤ s.site.pc ∧ s.site.pc ≤ 621 := by
  obtain ⟨pos, hr, -⟩ := hI
  rw [hr.site]
  rcases conversion_pos_pc (g := g) pos with ⟨j, -, h⟩ | ⟨-, h1, h2⟩
  · have := j.isLt
    omega
  · omega

/-- A state of the CarryLoad phase is at an instruction from 765 to 1401. -/
theorem pc_carryLoad (hI : CarryLoad.Inv P X g j0 k s) :
    765 ≤ s.site.pc ∧ s.site.pc ≤ 1401 := by
  obtain ⟨pos, hr, -⟩ := hI
  rw [hr.site]
  exact carryLoad_pos_pc pos

/-- **The instruction of a state of the Compute phase**, with the number of `bar.sync 0` of
the position's ledger: 1402 at the entry (five), from 2106 to 2944 inside the loop (six). -/
theorem compute_pos_pc {pos : Compute.Pos} (hr : Compute.RefAt P L g pos s) :
    ((Compute.led pos).bar0 = 5 ∧ s.site.pc = 1402) ∨
      ((Compute.led pos).bar0 = 6 ∧ 2106 ≤ s.site.pc ∧ s.site.pc ≤ 2944) := by
  cases pos with
  | entry =>
    have h : s.site = .bar 5 := hr.site
    exact .inl ⟨rfl, by rw [h]; rfl⟩
  | tile t n =>
    have h : (Compute.skOf n).At s.site := hr.site
    have hn : n < 268 := (hr.facts : Compute.Tile P L g t n s.w s.p s.x).pos
    rw [skPc_at h]
    exact .inr ⟨rfl, compute_tile_pc n hn⟩

/-- A state of the Compute phase is at instruction 1402 or at one from 2106 to 2944. -/
theorem pc_compute (hI : Compute.Inv P L X g j0 k s) :
    s.site.pc = 1402 ∨ (2106 ≤ s.site.pc ∧ s.site.pc ≤ 2944) := by
  obtain ⟨pos, hr, -⟩ := hI
  rcases compute_pos_pc hr with ⟨-, h⟩ | ⟨-, h⟩
  · exact .inl h
  · exact .inr h

/-- A state of the Producer phase is at an instruction from 1402 to 2105. -/
theorem pc_producer (hI : Producer.Inv P L X g k s) : 1402 ≤ s.site.pc ∧ s.site.pc ≤ 2105 :=
  Producer.region_producer hI

/-- A state with the weak invariant of the Store phase is at instruction 1402 (the entry), at
one from 2945 to 3112, or at 3113 (the exit state). -/
theorem pc_store (hW : StoreWeak P g s) :
    s.site.pc = 1402 ∨ (2945 ≤ s.site.pc ∧ s.site.pc ≤ 3113) := by
  rcases hW with ⟨pos, hr⟩ | hx
  · rw [hr.site]
    rcases store_pos_pc pos with ⟨-, h⟩ | ⟨-, h1, h2⟩
    · exact .inl h
    · exact .inr ⟨h1, Nat.le_succ_of_le h2⟩
  · rw [hx.site]
    exact .inr ⟨by decide, by decide⟩

/-- A state of the Store phase's invariant is at instruction 1402 or at one from 2945 to
3112. -/
theorem pc_store_inv (hI : Store.Inv P X g k s) :
    s.site.pc = 1402 ∨ (2945 ≤ s.site.pc ∧ s.site.pc ≤ 3112) := by
  obtain ⟨pos, hr, -⟩ := hI
  rw [hr.site]
  rcases store_pos_pc pos with ⟨-, h⟩ | ⟨-, h⟩
  · exact .inl h
  · exact .inr h

/-- A state of the epilogue is at an instruction from 3113 to 3835. -/
theorem pc_epilogue (hW : Epilogue.InvW P X g j0 k s) :
    3113 ≤ s.site.pc ∧ s.site.pc ≤ 3835 := by
  obtain ⟨pos, hr, -⟩ := hW
  rw [hr.site]
  rcases epilogue_pos_pc pos with ⟨-, h⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h⟩ <;> omega

/-! ### The `bar.sync 0` counts of the states of each phase -/

/-- **A state of the Conversion phase has `bar0Of pc` earlier `bar.sync 0`**: three up to the
barrier of instruction 620, four at the one of 621. -/
theorem bar0_conversion (hI : Conversion.Inv P X g j0 k s) :
    ((X.tr g).take k).countP (Execution.isBarId 0) =
      (bar0Pcs.filter (· < s.site.pc)).length := by
  obtain ⟨pos, hr, hl, -⟩ := hI
  have h1 : ((X.tr g).take k).countP (Execution.isBarId 0) = (Conversion.led g pos).bars :=
    congrArg Startup.Led.bars hl
  rw [h1, hr.site]
  rcases conversion_pos_pc (g := g) pos with ⟨j, rfl, h⟩ | ⟨hb, h2, h3⟩
  · rw [h]
    fin_cases j <;> rfl
  · rw [hb]
    exact (bar0_range (lo := 387) (hi := 620) (by decide) (by decide) h2 (Nat.le_of_lt h3)).symm

/-- **A state of the CarryLoad phase has five earlier `bar.sync 0`**, which is `bar0Of pc`. -/
theorem bar0_carryLoad (hI : CarryLoad.Inv P X g j0 k s) :
    ((X.tr g).take k).countP (Execution.isBarId 0) = 5 ∧
      (bar0Pcs.filter (· < s.site.pc)).length = 5 := by
  have hpc := pc_carryLoad hI
  obtain ⟨pos, hr, hl, -⟩ := hI
  exact ⟨congrArg Startup.Led.bars hl,
    bar0_range (lo := 622) (hi := 1402) (by decide) (by decide) (by omega) (by omega)⟩

/-- **A state of the Compute phase has `bar0Of pc` earlier `bar.sync 0`**: five at the entry
(instruction 1402), six inside the loop. -/
theorem bar0_compute (hI : Compute.Inv P L X g j0 k s) :
    ((X.tr g).take k).countP (Execution.isBarId 0) =
      (bar0Pcs.filter (· < s.site.pc)).length := by
  obtain ⟨pos, hr, hl, -⟩ := hI
  have h1 : ((X.tr g).take k).countP (Execution.isBarId 0) = (Compute.led pos).bar0 :=
    congrArg Compute.Led.bar0 hl
  rw [h1]
  rcases compute_pos_pc hr with ⟨hb, h⟩ | ⟨hb, h2, h3⟩
  · rw [hb, h]
    rfl
  · rw [hb]
    exact (bar0_range (lo := 1403) (hi := 3113) (by decide) (by decide) (by omega)
      (by omega)).symm

/-- The ledger of a position of the Store phase other than the entry has six `bar.sync 0`
(the entry has five). -/
theorem store_led_bars {len : Nat} {pos : Store.Pos} (hp : pos ≠ .entry) :
    (Store.led len pos).bars = 6 := by
  cases pos <;> first
    | exact absurd rfl hp
    | rfl
    | (simp only [Store.led]; split <;> rfl)

/-- **A state of the Store phase's invariant has `bar0Of pc` earlier `bar.sync 0`**: five at
the entry (instruction 1402), six inside the loop. -/
theorem bar0_store (hI : Store.Inv P X g k s) :
    ((X.tr g).take k).countP (Execution.isBarId 0) =
      (bar0Pcs.filter (· < s.site.pc)).length := by
  obtain ⟨pos, hr, hl⟩ := hI
  have h1 : ((X.tr g).take k).countP (Execution.isBarId 0) =
      (Store.led (P.length (seqOf P g)) pos).bars := congrArg Store.Led.bars hl
  rw [h1, hr.site]
  rcases store_pos_pc pos with ⟨rfl, h⟩ | ⟨hne, h2, h3⟩
  · rw [h]
    rfl
  · rw [store_led_bars hne]
    exact (bar0_range (lo := 1403) (hi := 3113) (by decide) (by decide) (by omega)
      (by omega)).symm

/-- **A state of the epilogue has `bar0Of pc` earlier `bar.sync 0`**: six at instruction
3113, seven up to 3775, eight up to 3834, nine at the `ret`. From the weak invariant, so at
every followed state of the epilogue. -/
theorem bar0_epilogue (hW : Epilogue.InvW P X g j0 k s) :
    ((X.tr g).take k).countP (Execution.isBarId 0) =
      (bar0Pcs.filter (· < s.site.pc)).length := by
  obtain ⟨pos, hr, -, -, hb⟩ := hW
  rw [hb, hr.site]
  rcases epilogue_pos_pc pos with ⟨hb, h⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h⟩
  · rw [hb, h]
    rfl
  · rw [hb]
    exact (bar0_range (lo := 3114) (hi := 3775) (by decide) (by decide) (by omega) h2).symm
  · rw [hb]
    exact (bar0_range (lo := 3776) (hi := 3834) (by decide) (by decide) (by omega) h2).symm
  · rw [hb, h]
    rfl

/-! ### By stage -/

/-- **The instructions of the states of each stage**, with the roles of the three tile
loops. -/
theorem Stage.pc_cases (h : Stage P L X g k s) :
    s.site.pc ≤ 384 ∨ (387 ≤ s.site.pc ∧ s.site.pc ≤ 621) ∨
    (765 ≤ s.site.pc ∧ s.site.pc ≤ 1401) ∨
    (tid g < 128 ∧ (s.site.pc = 1402 ∨ (2106 ≤ s.site.pc ∧ s.site.pc ≤ 2944))) ∨
    (warp g = 4 ∧ 1402 ≤ s.site.pc ∧ s.site.pc ≤ 2105) ∨
    (warp g = 5 ∧ (s.site.pc = 1402 ∨ (2945 ≤ s.site.pc ∧ s.site.pc ≤ 3113))) ∨
    (3113 ≤ s.site.pc ∧ s.site.pc ≤ 3835) := by
  cases h with
  | startup hI => exact .inl (pc_startup hI.inv)
  | conversion _ _ hI => exact .inr (.inl (pc_conversion hI))
  | carryLoad _ _ hI => exact .inr (.inr (.inl (pc_carryLoad hI)))
  | compute hr _ _ _ hI => exact .inr (.inr (.inr (.inl ⟨hr, pc_compute hI⟩)))
  | producer hr _ _ _ hI => exact .inr (.inr (.inr (.inr (.inl ⟨hr, pc_producer hI⟩))))
  | store hr _ _ _ _ hW => exact .inr (.inr (.inr (.inr (.inr (.inl ⟨hr, pc_store hW⟩)))))
  | epilogue _ _ hW _ => exact .inr (.inr (.inr (.inr (.inr (.inr (pc_epilogue hW))))))

/-- **Every followed state of a stage has `bar0Of pc` earlier `bar.sync 0` events** (the field
`bar0` of the progress contract), given, for the Store phase, that no undefined-behaviour
event precedes the position. -/
theorem Stage.bar0 (h : Stage P L X g k s) (hub : NoUb X g k) :
    ((X.tr g).take k).countP (Execution.isBarId 0) =
      (bar0Pcs.filter (· < s.site.pc)).length := by
  cases h with
  | startup hI => exact Startup.bar0_startup hI.inv
  | conversion _ _ hI => exact bar0_conversion hI
  | carryLoad _ _ hI =>
    obtain ⟨h1, h2⟩ := bar0_carryLoad hI
    rw [h1, h2]
  | compute _ _ _ _ hI => exact bar0_compute hI
  | producer _ _ _ _ hI => exact Producer.bar0_producer hI
  | store _ _ _ _ hI _ => exact bar0_store (hI hub)
  | epilogue _ _ hW _ => exact bar0_epilogue hW

/-- **The `bar.sync 0` counts of the stages, in numbers** (`n` is the thread's count of
earlier `bar.sync 0` events): at most 3 in the startup; 3 or 4 in the Conversion phase; 5 in
the CarryLoad phase; 5 or 6 in a tile loop (5 exactly at instruction 1402); from 6 to 9 in the
epilogue. -/
theorem Stage.bar0_bounds (h : Stage P L X g k s) (hub : NoUb X g k) :
    let n := ((X.tr g).take k).countP (Execution.isBarId 0)
    (s.site.pc ≤ 384 → n ≤ 3) ∧ (387 ≤ s.site.pc → s.site.pc ≤ 620 → n = 3) ∧
    (s.site.pc = 621 → n = 4) ∧ (621 < s.site.pc → s.site.pc ≤ 1402 → n = 5) ∧
    (1402 < s.site.pc → s.site.pc ≤ 3113 → n = 6) ∧ (3113 < s.site.pc → 7 ≤ n ∧ n ≤ 9) := by
  intro n
  have hn : n = (bar0Pcs.filter (· < s.site.pc)).length := h.bar0 hub
  refine ⟨fun h1 => ?_, fun h1 h2 => ?_, fun h1 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_,
    fun h1 => ?_⟩
  · rw [hn]
    have h3 : (bar0Pcs.filter (· < s.site.pc)).length ≤ (bar0Pcs.filter (· < 385)).length :=
      (List.monotone_filter_right _ fun a ha => by
        simp only [decide_eq_true_eq] at ha ⊢
        omega).length_le
    exact h3
  · rw [hn]
    exact bar0_range (lo := 387) (hi := 620) (by decide) (by decide) h1 h2
  · rw [hn, h1]
    rfl
  · rw [hn]
    exact bar0_range (lo := 622) (hi := 1402) (by decide) (by decide) (by omega) h2
  · rw [hn]
    exact bar0_range (lo := 1403) (hi := 3113) (by decide) (by decide) (by omega) h2
  · rw [hn]
    constructor
    · have h3 : (bar0Pcs.filter (· < 3114)).length ≤ (bar0Pcs.filter (· < s.site.pc)).length :=
        (List.monotone_filter_right _ fun a ha => by
          simp only [decide_eq_true_eq] at ha ⊢
          omega).length_le
      exact h3
    · exact List.length_filter_le _ _

/-! ### From the instruction to the stage -/

/-- A followed state at an instruction below 387 is in the startup phase. -/
theorem Stage.of_pc_startup (h : Stage P L X g k s) (hpc : s.site.pc < 387) :
    Startup.InvE P X g k s := by
  cases h with
  | startup hI => exact hI
  | conversion _ _ hI => have := pc_conversion hI; omega
  | carryLoad _ _ hI => have := pc_carryLoad hI; omega
  | compute _ _ _ _ hI => have := pc_compute hI; omega
  | producer _ _ _ _ hI => have := pc_producer hI; omega
  | store _ _ _ _ _ hW => have := pc_store hW; omega
  | epilogue _ _ hW _ => have := pc_epilogue hW; omega

/-- A followed state at an instruction from 387 to 621 is in the Conversion phase. -/
theorem Stage.of_pc_conversion (h : Stage P L X g k s) (h1 : 387 ≤ s.site.pc)
    (h2 : s.site.pc ≤ 621) :
    ∃ j0 s0, StartupDone P L X g j0 s0 ∧ j0 ≤ k ∧ Conversion.Inv P X g j0 k s := by
  cases h with
  | startup hI => have := pc_startup hI.inv; omega
  | conversion past hj hI => exact ⟨_, _, past, hj, hI⟩
  | carryLoad _ _ hI => have := pc_carryLoad hI; omega
  | compute _ _ _ _ hI => have := pc_compute hI; omega
  | producer _ _ _ _ hI => have := pc_producer hI; omega
  | store _ _ _ _ _ hW => have := pc_store hW; omega
  | epilogue _ _ hW _ => have := pc_epilogue hW; omega

/-- A followed state at an instruction from 622 to 1401 is in the CarryLoad phase. -/
theorem Stage.of_pc_carryLoad (h : Stage P L X g k s) (h1 : 621 < s.site.pc)
    (h2 : s.site.pc < 1402) :
    ∃ j0 s0, ConversionDone P L X g j0 s0 ∧ j0 ≤ k ∧ CarryLoad.Inv P X g j0 k s := by
  cases h with
  | startup hI => have := pc_startup hI.inv; omega
  | conversion _ _ hI => have := pc_conversion hI; omega
  | carryLoad past hj hI => exact ⟨_, _, past, hj, hI⟩
  | compute _ _ _ _ hI => have := pc_compute hI; omega
  | producer _ _ _ _ hI => have := pc_producer hI; omega
  | store _ _ _ _ _ hW => have := pc_store hW; omega
  | epilogue _ _ hW _ => have := pc_epilogue hW; omega

/-- A followed state at an instruction of the load leader's loop (1403 to 2105) is a state of
the Producer phase of a thread of the load warp. -/
theorem Stage.of_pc_producer (h : Stage P L X g k s) (h1 : 1402 < s.site.pc)
    (h2 : s.site.pc ≤ 2105) :
    warp g = 4 ∧ ∃ j0 s0, CarryLoadDone P L X g j0 s0 ∧ j0 ≤ k ∧
      Producer.Entered P L X g j0 ∧ Producer.Inv P L X g k s := by
  cases h with
  | startup hI => have := pc_startup hI.inv; omega
  | conversion _ _ hI => have := pc_conversion hI; omega
  | carryLoad _ _ hI => have := pc_carryLoad hI; omega
  | compute _ _ _ _ hI => have := pc_compute hI; omega
  | producer hr past hj hen hI => exact ⟨hr, _, _, past, hj, hen, hI⟩
  | store _ _ _ _ _ hW => have := pc_store hW; omega
  | epilogue _ _ hW _ => have := pc_epilogue hW; omega

/-- A followed state at an instruction of the compute loop (2106 to 2944) is a state of the
Compute phase of a compute thread. -/
theorem Stage.of_pc_compute (h : Stage P L X g k s) (h1 : 2105 < s.site.pc)
    (h2 : s.site.pc ≤ 2944) :
    tid g < 128 ∧ ∃ j0 s0, CarryLoadDone P L X g j0 s0 ∧ j0 ≤ k ∧
      Compute.In P L X g j0 s0 ∧ Compute.Inv P L X g j0 k s := by
  cases h with
  | startup hI => have := pc_startup hI.inv; omega
  | conversion _ _ hI => have := pc_conversion hI; omega
  | carryLoad _ _ hI => have := pc_carryLoad hI; omega
  | compute hr past hj hin hI => exact ⟨hr, _, _, past, hj, hin, hI⟩
  | producer _ _ _ _ hI => have := pc_producer hI; omega
  | store _ _ _ _ _ hW => have := pc_store hW; omega
  | epilogue _ _ hW _ => have := pc_epilogue hW; omega

/-- A followed state at an instruction of the store leader's loop (2945 to 3112) is a state of
the Store phase of a thread of the store warp (its invariant is guarded: `Stage.lean`). -/
theorem Stage.of_pc_store (h : Stage P L X g k s) (h1 : 2944 < s.site.pc)
    (h2 : s.site.pc ≤ 3112) :
    warp g = 5 ∧ ∃ j0 s0, CarryLoadDone P L X g j0 s0 ∧ j0 ≤ k ∧ Store.In P X g j0 s0 ∧
      (NoUb X g k → Store.Inv P X g k s) ∧ StoreWeak P g s := by
  cases h with
  | startup hI => have := pc_startup hI.inv; omega
  | conversion _ _ hI => have := pc_conversion hI; omega
  | carryLoad _ _ hI => have := pc_carryLoad hI; omega
  | compute _ _ _ _ hI => have := pc_compute hI; omega
  | producer _ _ _ _ hI => have := pc_producer hI; omega
  | store hr past hj hin hI hW => exact ⟨hr, _, _, past, hj, hin, hI, hW⟩
  | epilogue _ _ hW _ => have := pc_epilogue hW; omega

/-- A followed state at an instruction after 3113, or at 3113 when no undefined-behaviour
event precedes the position, is a state of the epilogue. -/
theorem Stage.of_pc_epilogue (h : Stage P L X g k s) (h1 : 3113 ≤ s.site.pc)
    (hub : NoUb X g k ∨ 3113 < s.site.pc) :
    ∃ j0 s0, TileDone P L X g j0 s0 ∧ j0 ≤ k ∧ Epilogue.InvW P X g j0 k s ∧
      (NoUb X g k → Epilogue.Inv P L X g j0 k s) := by
  cases h with
  | startup hI => have := pc_startup hI.inv; omega
  | conversion _ _ hI => have := pc_conversion hI; omega
  | carryLoad _ _ hI => have := pc_carryLoad hI; omega
  | compute _ _ _ _ hI => have := pc_compute hI; omega
  | producer _ _ _ _ hI => have := pc_producer hI; omega
  | store _ _ _ _ hI hW =>
    rcases hub with hub | hgt
    · have := pc_store_inv (hI hub)
      omega
    · have := pc_store hW
      omega
  | epilogue past hj hW hI => exact ⟨_, _, past, hj, hW, hI⟩

end

/-! ### The fields `bar0` and `region` of the progress contract -/

/-- **The field `bar0` of the progress contract**, at every position: the followed state of a
launched thread has `bar0Of s.site.pc` earlier `bar.sync 0` events, given that no
undefined-behaviour event precedes the position (needed in the Store phase only). -/
theorem bar0 (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) {k : Nat} {s : D} (hσ : At (code L) X g k s) (hub : NoUb X g k) :
    ((X.tr g).take k).countP (Execution.isBarId 0) =
      (bar0Pcs.filter (· < s.site.pc)).length := by
  rcases Nat.le_total k (X.tr g).length with hk | hk
  · exact (stage hpre hX hg hk hσ).bar0 hub
  · have hσ' : At (code L) X g (X.tr g).length s := by
      rw [At, ← Frame.stateAt_of_le hk]
      exact hσ
    rw [List.take_of_length_le hk, ← List.take_length (l := X.tr g)]
    exact (stage hpre hX hg le_rfl hσ').bar0 (hub.mono hk)


/-- **Who is inside which tile loop**: a launched thread whose followed state is at an
instruction of the load leader's loop (1403 to 2105) is of the load warp, at one of the
compute loop (2106 to 2944) it is a compute thread, at one of the store leader's loop (2945 to
3112) it is of the store warp. For every position `k`. (`block_mod hpre : g % L.block = tid g`
turns the roles into the contract's form.) -/
theorem region (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) {k : Nat} {s : D} (hσ : At (code L) X g k s) :
    (1402 < s.site.pc → s.site.pc ≤ 2105 → 128 ≤ tid g ∧ tid g < 160) ∧
    (2105 < s.site.pc → s.site.pc ≤ 2944 → tid g < 128) ∧
    (2944 < s.site.pc → s.site.pc ≤ 3112 → 160 ≤ tid g) := by
  have hst := stage_any hpre hX hg hσ
  have hc := hst.pc_cases
  have h4 := warp_eq4_iff g
  have h5 := warp_eq5_iff g
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · rcases hc with h | h | h | ⟨hr, h⟩ | ⟨hr, h⟩ | ⟨hr, h⟩ | h
    · omega
    · omega
    · omega
    · omega
    · exact h4.mp hr
    · omega
    · omega
  · rcases hc with h | h | h | ⟨hr, h⟩ | ⟨hr, h⟩ | ⟨hr, h⟩ | h
    · omega
    · omega
    · omega
    · exact hr
    · omega
    · omega
    · omega
  · rcases hc with h | h | h | ⟨hr, h⟩ | ⟨hr, h⟩ | ⟨hr, h⟩ | h
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact h5.mp hr
    · omega

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
