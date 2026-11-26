-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Tracked
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.TileEarly
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.ExportsValues
public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Contract
public import Kernels.FlashKdaFwd.Proof.Ref.Source.Fit
public import Kernels.FlashKdaFwd.Proof.Values.Tile
public import Kernels.FlashKdaFwd.Proof.Protocol.ResultGuard

@[expose] public section

/-!
# The hypotheses of the induction over the tiles, for a whole execution

The value induction over the tile loop is the theorem `Values.tile_induction :
Values.TileInduction P L mem0 X` (`Proof/Values/Tile.lean`), where `Values.TileInduction P L
mem0 X` is `Values.TileHyps P L mem0 X → Values.TileClaim P L mem0 X`
(`Proof/Values/TileClaim.lean`): from a record of hypotheses about the other layers it derives
that every data register of every compute lane holds the real number the algebra says. This
file builds that record for every consistent execution under the launch precondition, from the
layers that proved its parts, and so turns the induction into its conclusion (`tileClaim`).

**Words.** A *followed state* of thread `g` at position `k` is the state `s` of the thread's
machine before the thread's `k`-th event (`Frame.stateAt (code L) X g k = some (some s)`,
written `At (code L) X g k s`); `s.site` is the event instruction the machine is at and
`s.site.pc` its index in the program. A *compute thread* (a *lane* of a *compute warp*) has
index `g % L.block` below 128 in its thread block. The *ordinal* `WarpMatrix.ordinal X g k` is
the number of warp matrix events among the first `k` events of thread `g`; a tile is 182 of
them. A *stage* (`Stage.lean`) is the phase of the thread's run that a followed state is in,
with that phase's invariant. *Undefined behaviour* is an event of kind `.ub`.

## The fields of `Values.TileHyps` and where each comes from

| field | here | from |
|---|---|---|
| `pre` | the hypothesis `hpre` | |
| `followed` | `TileHyps.followed` | `Thread.sound`, `tracked` (`Tracked.lean`) |
| `ref` | `TileHyps.computeRef` | the Compute phase's exports (`Ref/Compute/ExportsValues.lean`) |
| `back` | `TileHyps.readBack` | `stage`: `Ref/Source/Fit.lean`, `tileIssues`; `acc`: a hypothesis |
| `exit` | `TileHyps.loopExit` | `loopExit_out` and the epilogue's weak invariant |
| `bound` | `TileHyps.tileBound` | `tileBound_compute` |
| `warp` | `TileHyps.warp` | the launch shape |
| `first` | `TileHyps.firstLoad` | `firstLoad_compute` |
| `base` | a hypothesis | the carry loads (`TileEnds.lean: tileBase`) |
| `early` | `TileHyps.earlyWrites` | the closed-form events of the phases (`TileEarly.lean`) |

Every field of `Values.ComputeRef`, and `Values.TileBound`, `Values.LoopExit`, quantify over
EVERY followed state or event of a compute thread, while the Compute phase proved its share for
a state that carries the phase's invariant. The join is the case principle of the chain: the
instruction of a state decides the stage (`Stage.of_pc_compute`: an instruction of the tile
loop, 2106 to 2944, is in the Compute stage of a compute thread). Three points need more:

* a field without the premise "the thread is launched": a thread outside the launch has no
  event, and its only state is the initial one, which is at an instruction of the startup
  (`TileHyps.launched`);
* a field about a state without an event (`zero`, `TileBound`, `LoopExit`): the position may
  lie beyond the end of the trace, where the state and the counts are those of the last
  position (`stage_any`, `TileHyps.ordinal_min`);
* `ComputeRef.count`: there need not be a followed state after a thread's last event, so the
  bound is proved along the trace from the matrix events themselves (`TileHyps.ordinal_le`),
  and the equality at an exit from the epilogue's ledger (`Epilogue.matrix_exit`) and the exit
  ledger of the Compute phase.

## The tensor loads of a load leader, by their count

The read-back of the input stage (`Source.readBack_stage`, the field `stage` of
`Values.ReadBack`) and the reads before the tile loop (`Source.earlyRead_init`) take as
hypotheses which copy a tensor load of a block's load leader is, given the mbarrier it
completes on and the number of earlier loads on that mbarrier: `Source.TileIssues` (the seventy
loads of a tile) and `Source.StateIssues` (the sixteen loads of the initial state).
`TileHyps.tileIssues` and `TileHyps.stateIssues` prove both, with no hypothesis: a tensor load
is issued at an instruction of the startup or of the Producer phase (`TileHyps.issue_stage`),
the closed-form event of that phase gives the copy and the count, and the two families
complete on different mbarriers.

Helpers are in the namespace `Assembly.TileHyps`; the final theorems `tileHyps` and `tileClaim`
are in `Assembly`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX.Kernels.FlashKdaFwd.Protocol (Facts UnionFacts StoreCover Owners ctaTiles noEvents Bar
  loadLeader)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

namespace TileHyps

/-! ### Instructions of the sites of the tile loop -/

/-- The first event of an `ldmatrix` (its row read) is at an instruction of the tile loop. -/
theorem ld_pc : ∀ j : Fin 44,
    2105 < (Site.matrixLoad j).pc ∧ (Site.matrixLoad j).pc ≤ 2944 := by decide +kernel

/-- The second event of an `ldmatrix` (its matrix event) is at the same instruction. -/
theorem ldMx_pc (j : Fin 44) (row : List (Option Byte)) :
    2105 < (Site.matrixLoadMx j row).pc ∧ (Site.matrixLoadMx j row).pc ≤ 2944 := ld_pc j

/-- An `mma.sync` is at an instruction of the tile loop. -/
theorem mma_pc : ∀ j : Fin 104,
    2105 < (Site.warpMma j).pc ∧ (Site.warpMma j).pc ≤ 2944 := by decide +kernel

/-- A `movmatrix` is at an instruction of the tile loop. -/
theorem mv_pc : ∀ j : Fin 16,
    2105 < (Site.matrixMove j).pc ∧ (Site.matrixMove j).pc ≤ 2944 := by decide +kernel

/-- The first event of an `stmatrix` (its matrix event) is at an instruction of the tile
loop. -/
theorem st_pc : ∀ j : Fin 18,
    2105 < (Site.matrixStore j).pc ∧ (Site.matrixStore j).pc ≤ 2944 := by decide +kernel

/-- The second event of an `stmatrix` (its row write) is at the same instruction. -/
theorem stWr_pc (j : Fin 18) (row : List (Option Byte)) :
    2105 < (Site.matrixStoreWr j row).pc ∧ (Site.matrixStoreWr j row).pc ≤ 2944 := st_pc j

/-- The eighteen scalar loads of a tile (the machine's load sites 159 to 176) are at
instructions of the tile loop. -/
theorem scalar_pc : ∀ i : Fin 178, 159 ≤ i.val → i.val < 177 →
    2105 < (Site.load i).pc ∧ (Site.load i).pc ≤ 2944 := by decide +kernel

/-- The instructions listed in the value layer's table of the scalar loads are instructions of
the tile loop. -/
theorem scalarForms_pc : ∀ q ∈ Values.Gen.scalarForms, 2105 < q.1 ∧ q.1 ≤ 2944 := by
  decide +kernel

/-- A site that fires a matrix event is at an instruction of the tile loop. -/
theorem matrix_kind_pc (s : Site) (h : s.kind ∈ matrixKinds) : 2105 < s.pc ∧ s.pc ≤ 2944 := by
  cases s with
  | warpMma j => exact mma_pc j
  | matrixMove j => exact mv_pc j
  | matrixStore j => exact st_pc j
  | matrixLoadMx j row => exact ldMx_pc j row
  | _ => simp [Site.kind, matrixKinds] at h

/-! ### From a state at an instruction of the tile loop to the invariant of the Compute phase -/

/-- **A followed state past the startup phase belongs to a launched thread**: a thread outside
the launch has no events, so its only state is the initial one, at an instruction of the
startup phase (at most 384). -/
theorem launched (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {k : Nat} {s : D} (hσ : At (code L) X g k s) (hpc : 384 < s.site.pc) : g < L.threads := by
  by_contra hn
  have h0 : (X.tr g).length = 0 := by rw [hX.outside g (by omega)]; rfl
  rw [At, Frame.stateAt_of_le (by omega), h0, Frame.stateAt_zero] at hσ
  obtain rfl : (code L g).init = s := Option.some.inj (Option.some.inj hσ)
  obtain ⟨pos, hr, -⟩ := Startup.st_init (L := L) (g := g) hpre
  have h1 := startup_pos_pc pos
  rw [← hr.site] at h1
  have h2 : (init L g).site.pc = (code L g).init.site.pc := rfl
  omega

/-- The matrix events before a position beyond the end of the trace are those of the whole
trace. -/
theorem ordinal_min (X : Execution) (g k : Nat) :
    WarpMatrix.ordinal X g (min k (X.tr g).length) = WarpMatrix.ordinal X g k := by
  unfold WarpMatrix.ordinal
  rcases Nat.le_total k (X.tr g).length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.take_length, List.take_of_length_le h]

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- **A followed state at an instruction of the tile loop** (2106 to 2944) is a state of a
launched compute thread in the Compute phase: the thread entered the phase at a followed state
`s0` before its event `j0`, and the phase's invariant holds at the state, at its position cut
at the end of the trace. -/
theorem inv_any {k : Nat} {s : D} (hσ : At (code L) X g k s) (h1 : 2105 < s.site.pc)
    (h2 : s.site.pc ≤ 2944) :
    g < L.threads ∧ tid g < 128 ∧ ∃ j0 s0, At (code L) X g j0 s0 ∧ Compute.In P L X g j0 s0 ∧
      Compute.Inv P L X g j0 (min k (X.tr g).length) s := by
  have hg := launched hpre hX hσ (by omega)
  obtain ⟨hr, j0, s0, past, -, hin, hI⟩ := (stage_any hpre hX hg hσ).of_pc_compute h1 h2
  exact ⟨hg, hr, j0, s0, past.state, hin, hI⟩

/-- **The same before an event**: the invariant holds at the position of the event. -/
theorem inv_event {k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s) (h1 : 2105 < s.site.pc) (h2 : s.site.pc ≤ 2944) :
    g < L.threads ∧ tid g < 128 ∧ ∃ j0 s0, At (code L) X g j0 s0 ∧ Compute.In P L X g j0 s0 ∧
      Compute.Inv P L X g j0 k s := by
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have h := inv_any hpre hX hσ h1 h2
  rwa [Nat.min_eq_left hk.le] at h

/-- **A matrix event is fired at a state of the Compute phase** (a matrix event is fired only
at a matrix site, `Ref/Kinds`, and the matrix sites are instructions of the tile loop). -/
theorem inv_matrix {k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hm : isMatrix e = true) (hσ : At (code L) X g k s) :
    g < L.threads ∧ tid g < 128 ∧ ∃ j0 s0, At (code L) X g j0 s0 ∧ Compute.In P L X g j0 s0 ∧
      Compute.Inv P L X g j0 k s := by
  have hkind : s.site.kind ∈ matrixKinds := by
    by_contra hκ
    rw [not_class_of_kind (sounds hpre) hX firedOnly_isMatrix he hσ hκ] at hm
    cases hm
  obtain ⟨h1, h2⟩ := matrix_kind_pc s.site hkind
  exact inv_event hpre hX he hσ h1 h2

/-! ### `ComputeRef.count` -/

/-- **A matrix event that is not undefined behaviour fires from a followed state.** -/
theorem matrix_state {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hm : isMatrix e = true) : ∃ s, At (code L) X g k s := by
  refine followed_event hpre hX he fun pc f h => ?_
  subst h
  cases hm

/-- **At most 182 matrix events per tile, at every position of the trace.** By induction along
the trace: a matrix event is fired at a matrix position of a tile of the sequence, with fewer
than 182 matrix events of that tile before it (`Compute.Vals.matrix_pos`). No followed state
after the event is needed. -/
theorem ordinal_le : ∀ k, k ≤ (X.tr g).length →
    WarpMatrix.ordinal X g k ≤ 182 * Compute.tilesOf P g := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [WarpMatrix.ordinal]
  | succ k ih =>
    intro hk
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hs : WarpMatrix.ordinal X g (k + 1) =
        WarpMatrix.ordinal X g k + (if isMatrix e = true then 1 else 0) := count_snoc isMatrix he
    have hi := ih (by omega)
    by_cases hm : isMatrix e = true
    · obtain ⟨s, hσ⟩ := matrix_state hpre hX he hm
      obtain ⟨-, -, j0, s0, -, -, hI⟩ := inv_matrix hpre hX he hm hσ
      obtain ⟨op, own, recv, hq⟩ := Compute.Vals.isMatrix_kind hm
      obtain ⟨t, n, m, -, ht, -, -, -, hlt, -, hord⟩ :=
        Compute.Vals.matrix_pos hpre hX he hq hσ hI
      simp only [hm, ↓reduceIte] at hs
      have : 182 * (t + 1) ≤ 182 * Compute.tilesOf P g := Nat.mul_le_mul_left 182 ht
      omega
    · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hs
      omega

/-- **`ComputeRef.count`**: a compute lane makes at most 182 matrix events per tile of its
sequence, and exactly that many when it exits. An exit is fired at the last instruction, in
the epilogue; the epilogue makes no matrix event, and the lane entered it from the exit of the
Compute phase, whose ledger has 182 matrix events per tile. -/
theorem count (hc : g % L.block < 128) :
    (X.tr g).countP isMatrix ≤ 182 * Values.tileCount P L g ∧
      ∀ j pc, X.get (g, j) = some ⟨pc, .exit⟩ →
        (X.tr g).countP isMatrix = 182 * Values.tileCount P L g := by
  refine ⟨?_, ?_⟩
  · have h := ordinal_le (g := g) hpre hX (X.tr g).length le_rfl
    unfold WarpMatrix.ordinal at h
    rw [List.take_length] at h
    rw [Compute.Vals.tileCount_eq hpre]
    exact h
  · intro j pc he
    have hg := Frame.lt_of_get hX he
    obtain ⟨s, hσ⟩ := followed_event hpre hX he fun pc' f h => by cases h
    obtain ⟨hst, -⟩ := stage_event hpre hX hg he hσ
    obtain ⟨-, hpc⟩ := exit_site_pc (sounds hpre) hX he hσ rfl
    obtain ⟨j0, s0, past, hj, -, -⟩ := hst.of_pc_epilogue (by omega) (.inr (by omega))
    have hr : tid g < 128 := by rw [← block_mod hpre]; exact hc
    obtain ⟨j1, s1, -, -, ⟨-, -, hO, -⟩ | ⟨h4, -⟩ | ⟨h5, -⟩⟩ := past.entry
    · have h1 := Epilogue.matrix_exit hpre hX hg ⟨s0, past.state, past.into⟩ hj he
      rw [h1]
      exact Compute.Vals.loopExit_out hpre hO
    · have := (warp_eq4_iff g).mp h4
      omega
    · have := (warp_eq5_iff g).mp h5
      omega

/-! ### `Values.ComputeRef` for the whole execution -/

/-- **The reference layer of the Compute phase, for the whole execution**
(`Values.ComputeRef`, `Proof/Values/Contract.lean`): the seven fields, each from the phase's
export for a state with the invariant, which the instruction of the state supplies. -/
theorem computeRef : Values.ComputeRef P L X where
  site := by
    intro g k N d _ hN hσ
    obtain ⟨⟨e, he, hm⟩, -⟩ := id hN
    obtain ⟨-, -, j0, s0, -, -, hI⟩ := inv_matrix hpre hX he hm hσ
    exact Compute.Vals.site_compute hpre hX hN hσ hI
  count := fun g hc => count hpre hX hc
  zero := by
    intro g k d j _ hσ hs
    obtain ⟨-, -, j0, s0, -, -, hI⟩ :=
      inv_any hpre hX hσ (by rw [hs]; exact (mma_pc j).1) (by rw [hs]; exact (mma_pc j).2)
    exact Compute.Vals.zero_compute hI hs
  polled := by
    intro g k d e _ hσ he hs
    have hpc : 2105 < d.site.pc ∧ d.site.pc ≤ 2944 := by
      rcases hs with ⟨j, hj⟩ | ⟨sz, c, ck, ws, hq⟩
      · rw [hj]
        exact ld_pc j
      · exact scalarForms_pc _ hq
    obtain ⟨-, -, j0, s0, -, -, hI⟩ := inv_event hpre hX he hσ hpc.1 hpc.2
    exact Compute.Vals.polled_compute hI hs
  loadRow := by
    intro g k d e j _ hσ hs he
    obtain ⟨-, -, j0, s0, -, -, hI⟩ :=
      inv_event hpre hX he hσ (by rw [hs]; exact (ld_pc j).1) (by rw [hs]; exact (ld_pc j).2)
    exact Compute.Vals.loadRow_compute hpre hX he hσ hI hs
  storeRow := by
    intro g k d e j row _ hσ hs he
    obtain ⟨-, -, j0, s0, -, -, hI⟩ := inv_event hpre hX he hσ
      (by rw [hs]; exact (stWr_pc j row).1) (by rw [hs]; exact (stWr_pc j row).2)
    exact Compute.Vals.storeRow_compute hpre hX he hσ hI hs
  scalarLoad := by
    intro g k d e pc sz c ck ws _ hσ hq hpc he
    have hr := scalarForms_pc _ hq
    obtain ⟨-, -, j0, s0, -, -, hI⟩ :=
      inv_event hpre hX he hσ (by rw [hpc]; exact hr.1) (by rw [hpc]; exact hr.2)
    exact Compute.Vals.scalarLoad_compute hpre hX he hσ hI hq hpc

/-! ### `Values.TileBound`, `Values.LoopExit`, `Values.FirstLoad`, `Values.Followed` -/

/-- **`Values.TileBound`**: at the first event of an `ldmatrix` and at a scalar load of the
tile loop the lane's tile is below the tile count of its sequence. -/
theorem tileBound : Values.TileBound P L X := by
  intro g k d _ hσ hs
  have hpc : 2105 < d.site.pc ∧ d.site.pc ≤ 2944 := by
    rcases hs with ⟨j, hj⟩ | ⟨i, h1, h2, hi⟩
    · rw [hj]
      exact ld_pc j
    · rw [hi]
      exact scalar_pc i h1 h2
  obtain ⟨-, -, j0, s0, -, -, hI⟩ := inv_any hpre hX hσ hpc.1 hpc.2
  rw [← ordinal_min]
  exact Compute.Vals.tileBound_compute hpre hI hs

/-- **`Values.LoopExit`**: a compute lane at the barrier after the exit branch of the tile
loop (`Site.bar 7`, instruction 3113) has made 182 matrix events per tile of its sequence.
Such a state is the first position of the epilogue (the stage of a compute thread at that
instruction), so its position is the one at which the lane left the Compute phase, whose exit
ledger has that count. -/
theorem loopExit : Values.LoopExit P L X := by
  intro g k d hc hσ hs
  have hpc : d.site.pc = 3113 := by
    rw [hs]
    rfl
  have hg := launched hpre hX hσ (by omega)
  have hr : tid g < 128 := by
    rw [← block_mod hpre]
    exact hc
  have hst := stage_any hpre hX hg hσ
  rw [← ordinal_min]
  cases hst with
  | startup hI => have := pc_startup hI.inv; omega
  | conversion _ _ hI => have := pc_conversion hI; omega
  | carryLoad _ _ hI => have := pc_carryLoad hI; omega
  | compute _ _ _ _ hI => have := pc_compute hI; omega
  | producer h4 _ _ _ _ => have := (warp_eq4_iff g).mp h4; omega
  | store h5 _ _ _ _ _ => have := (warp_eq5_iff g).mp h5; omega
  | epilogue past hj hW _ =>
    obtain ⟨pos, hR, -, hk, -⟩ := hW
    have hpos : Epilogue.ord g pos = 0 := by
      have h := epilogue_pos_pc pos
      rw [← hR.site, hpc] at h
      rcases h with ⟨h6, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h⟩
      · cases pos <;> first | rfl | simp [Epilogue.bars] at h6
      · omega
      · omega
      · omega
    obtain ⟨j1, s1, -, -, ⟨-, -, hO, -⟩ | ⟨h4, -⟩ | ⟨h5, -⟩⟩ := past.entry
    · rw [hk, hpos, Nat.add_zero]
      exact Compute.Vals.loopExit_out hpre hO
    · have := (warp_eq4_iff g).mp h4
      omega
    · have := (warp_eq5_iff g).mp h5
      omega

/-- **`Values.FirstLoad`**, for the lanes `w0 + l` of any thread `w0`: when an event of a lane
exists and the state after it is at the second event of the first `ldmatrix`, the state before
it is at the first event. -/
theorem firstLoad (w0 : Nat) : Values.FirstLoad (L := L) X w0 := by
  intro l _ k e d row he hσ hs
  have hg := Frame.lt_of_get hX he
  have hk : k < (X.tr (w0 + l)).length := (List.getElem?_eq_some_iff.mp he).1
  have hp := ldMx_pc 0 row
  obtain ⟨-, j0, s0, past, -, hin, hI⟩ :=
    (stage hpre hX hg (Nat.succ_le_of_lt hk) hσ).of_pc_compute
      (by rw [hs]; exact hp.1) (by rw [hs]; exact hp.2)
  exact Compute.Vals.firstLoad_compute hpre hX hg past.state hin he hσ hI hs

/-- **The thread layer's contract** `Values.Followed`: the launch has thread blocks of whole
warps, the execution is consistent, every thread's machine is sound (`Thread.sound`) and no
machine gives up (`tracked`, `Tracked.lean`). -/
theorem followed : Values.Followed L mem0 X :=
  ⟨by rw [hpre.block], hX, sounds hpre, tracked hpre hX⟩

end

/-! ### The tensor loads of a load leader, by their count on an mbarrier -/

/-- A tensor load (the machine's tensor-copy sites below 226) is at an instruction of the
startup phase (the sixteen loads of the initial state) or of the Producer phase (the seventy
loads of a tile). -/
theorem load_copy_pc : ∀ j : Fin 258, j.val < firstStoreCopy →
    (Site.tensorCopy j).pc ≤ 384 ∨
      (1402 < (Site.tensorCopy j).pc ∧ (Site.tensorCopy j).pc ≤ 2105) := by decide +kernel

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- **Where a tensor load is issued**: at a followed state with the invariant of the startup
phase, or, for a thread of the load warp, with the invariant of the Producer phase, which the
thread entered at or before the issue. -/
theorem issue_stage {k pc al : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩) :
    ∃ s, At (code L) X g k s ∧
      (Startup.Inv P X g k s ∨
        (warp g = 4 ∧ ∃ j0 ≤ k, Producer.Entered P L X g j0 ∧ Producer.Inv P L X g k s)) := by
  obtain ⟨s, hσ, hst, -⟩ := event_stage hpre hX he (fun f h => by cases h)
  obtain ⟨j, hsite, hj⟩ := tensorIssue_site (sounds hpre) hX he hσ rfl
  rcases load_copy_pc j hj with h | ⟨h1, h2⟩
  · rw [← hsite] at h
    exact ⟨s, hσ, .inl (hst.of_pc_startup (by omega)).inv⟩
  · rw [← hsite] at h1 h2
    obtain ⟨hw, j0, s0, -, hj0, hen, hI⟩ := hst.of_pc_producer h1 h2
    exact ⟨s, hσ, .inr ⟨hw, j0, hj0, hen, hI⟩⟩

/-- **`Source.StateIssues`**: a tensor load of the load leader of block `c` that completes on
the state mbarrier, with `n` earlier loads on it, is the `n`-th load of the initial state, and
`n < 16`. Such a load is issued in the startup phase (`Source.stateIssues_of_startup`): a load
of the Producer phase completes on the "full" mbarrier of an input stage. -/
theorem stateIssues : Source.StateIssues P L X :=
  Source.stateIssues_of_startup hpre hX fun c i pc al sp hiss hm => by
    have hg := Frame.lt_of_get hX hiss
    obtain ⟨st, hσ, hI | ⟨hw, j0, -, -, hI⟩⟩ := issue_stage hpre hX hiss
    · exact ⟨⟨st, hσ⟩, hI.not_left⟩
    · exfalso
      obtain ⟨pos, w, p, x, -, hr, hl, hev, -⟩ :=
        Producer.producer_good hpre hX hg hw hiss hσ hI
      obtain ⟨tt, q, -, -, -, -, rfl, -⟩ := Producer.issue_shape hr hl hev
      have hmb : (Producer.tileLoad P L (loadLeader L c) tt q).mbar =
          (Bar.loadFull (Producer.stage tt)).loc L (loadLeader L c / L.block) := by
        rw [Producer.tileLoad, loadSpec_mbar, Producer.fullLoc_eq hpre]
      cases (Bar.loc_inj (hmb.symm.trans hm)).1

/-- **`Source.TileIssues`**: a tensor load of the load leader of block `c` that completes on
the "full" mbarrier of input stage `s`, with `n` earlier loads on that mbarrier, is the load at
position `n % 70` of tile `3 * (n / 70) + s`, a tile of the block's sequence. Such a load is
issued at a state of the Producer phase, whose ledger gives the count (the body of
`Source.tileIssues_of_producer`, with the invariant taken from the stage of the state); a
load of the startup phase completes on the state mbarrier. -/
theorem tileIssues : Source.TileIssues P L X := by
  intro c s i pc al sp hiss hm
  have hg := Frame.lt_of_get hX hiss
  obtain ⟨hdiv, -, -⟩ := Source.leader_block (P := P) hpre c
  obtain ⟨st, hσ, hI | ⟨hw, j0, -, -, hI⟩⟩ := issue_stage hpre hX hiss
  · exfalso
    rcases Startup.issue_startup hpre hX hg hiss hσ with ⟨j, -, -, rfl, -, -⟩ | hleft
    · have hmb : (Startup.stateSpec P L (loadLeader L c) j.val).mbar =
          Bar.state.loc L (loadLeader L c / L.block) := by
        simp only [Startup.stateSpec, loadSpec_mbar, Bar.loc, Bar.off, hpre.sharedBase]
      cases (Bar.loc_inj (hmb.symm.trans hm)).1
    · exact hI.not_left hleft
  · obtain ⟨pos, w, p, x, -, hr, hl, hev, -⟩ :=
      Producer.producer_good hpre hX hg hw hiss hσ hI
    obtain ⟨tt, q, htt, hq, -, -, rfl, -, hc, -⟩ := Producer.issue_shape hr hl hev
    rw [hdiv] at hc
    have hmb : (Producer.tileLoad P L (loadLeader L c) tt q).mbar =
        (Bar.loadFull (Producer.stage tt)).loc L c := by
      rw [Producer.tileLoad, loadSpec_mbar, Producer.fullLoc_eq hpre, hdiv]
    obtain rfl : Producer.stage tt = s := (Bar.loadFull.inj (Bar.loc_inj (hmb.symm.trans hm)).1)
    have hc' : ((X.tr (loadLeader L c)).take i).countP
        (issuesTo ((Bar.loadFull (Producer.stage tt)).loc L c)) = 70 * (tt / 3) + q := hc
    have h3 : (Producer.stage tt).val = tt % 3 := rfl
    rw [hc', show (70 * (tt / 3) + q) / 70 = tt / 3 by omega,
      show (70 * (tt / 3) + q) % 70 = q by omega, h3,
      show 3 * (tt / 3) + tt % 3 = tt by omega]
    exact ⟨htt, rfl⟩

end

/-- **Each compute warp is a warp**: the thread `c * L.block + 32 * w` of a compute warp
`w < 4` of block `c` has lane 0, and the 32 threads from it on are compute threads. -/
theorem warp (hpre : Pre P L mem0) {c w : Nat} (hw : w < 4) :
    Values.Warp L (c * L.block + 32 * w) where
  lane0 := by
    unfold laneOf
    rw [hpre.block]
    omega
  compute := by
    intro l hl
    rw [hpre.block]
    omega

/-! ### The named hypotheses that remain -/

/-- **The read-back of the bfloat16 state copy** (the field `acc` of `Values.ReadBack`,
verbatim): a 16-byte read by a compute thread `g` of a row of `state_acc` (window offsets 0 to
32767 of its block) returns the bytes of the thread's own last 16-byte write of that row, or,
when it has made no such write yet, the bytes the conversion loop left there
(`Values.accInitByte`). Proved by the assembly of the value ends
(`ValuesEndsAcc.lean: readBack_acc`). -/
def AccRead (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g k pc a bs o, g % L.block < 128 → X.get (g, k) = some ⟨pc, .rd a bs⟩ →
    a.loc = ⟨.shared, g / L.block, P.sharedBase + o⟩ → a.size = 16 → o + 16 ≤ 32768 →
    (∃ k' < k, ∃ pc' a' bs', X.get (g, k') = some ⟨pc', .wr a' bs'⟩ ∧ a'.loc = a.loc ∧
        a'.size = 16 ∧ bs = bs'.map some ∧
        ∀ k'', k' < k'' → k'' < k → ∀ pc'' a'' bs'',
          X.get (g, k'') = some ⟨pc'', .wr a'' bs''⟩ → a''.size = 16 → a''.loc ≠ a.loc) ∨
      ((∀ k' < k, ∀ pc' a' bs', X.get (g, k') = some ⟨pc', .wr a' bs'⟩ → a'.size = 16 →
          a'.loc ≠ a.loc) ∧
        bs = (List.range 16).map fun i =>
          Values.accInitByte P (Values.seqOf P L g) (Values.headOf P L g) (o + i))

/-- **The base case of the induction** (the field `base` of `Values.TileHyps`, verbatim): for
every compute warp `w < 4` of every block `c`, when a lane arrives at the first `ldmatrix` of
the first tile its 128 carry registers hold the initial state (`Values.Base`: the table of
ordinal 0 on the arrays of tile 0). Proved from the carry loads (`TileEnds.lean`). -/
def BaseCase (P : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop :=
  ∀ c w, c < L.grid → w < 4 →
    Values.Base (L := L) (Values.blockInputs P mem0 c) w X (c * L.block + 32 * w)

/-- **The protocol layer's read-back** `Values.ReadBack`: the field `stage` (a read of the
input stage of tile `b`, after `b / 3 + 1` successful polls of the stage's "full" mbarrier,
returns the bytes the tile's tensor loads wrote) from the content of the tile loads
(`Ref/Source/Fit.lean: readBack_stage`, with `tileIssues`) and the protocol contracts; the
field `acc` is the hypothesis `AccRead`. -/
theorem readBack (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {O : Owners} (F : Facts P L X) (U : UnionFacts L X (ctaTiles P) O)
    (hW : Source.WriteFrame P X) (hacc : AccRead P L X) : Values.ReadBack P L mem0 X where
  stage := Source.readBack_stage hpre hX (tileIssues hpre hX) hW U F.life F.load F.store
    F.state F.init F.bars (noEvents hX) (F.syncGuarded hpre hX)
  acc := hacc

end TileHyps

/-! ### The record and the claim -/

/-- **The hypotheses of the induction over the tiles, for a consistent execution under the
launch precondition** (`Values.TileHyps`). What remains as hypotheses, and the theorem that
proves each (`Values.lean: Values.hyps` puts them in):

* `F`, `U`: the protocol contracts (`FactsB.lean: facts`, `Buffers.lean: unionFacts`);
* `hW : Source.WriteFrame P X` (every global write is to an output array):
  `Direct.lean: Direct.writeFrame`;
* `hacc : TileHyps.AccRead P L X`: `ValuesEnds.lean: readBack_acc`;
* `hbase : TileHyps.BaseCase P L mem0 X`: `TileEnds.lean: tileBase`. -/
theorem tileHyps (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {O : Owners} (F : Facts P L X) (U : UnionFacts L X (ctaTiles P) O)
    (hW : Source.WriteFrame P X) (hacc : TileHyps.AccRead P L X)
    (hbase : TileHyps.BaseCase P L mem0 X) : Values.TileHyps P L mem0 X where
  pre := hpre
  followed := TileHyps.followed hpre hX
  ref := TileHyps.computeRef hpre hX
  back := TileHyps.readBack hpre hX F U hW hacc
  exit := TileHyps.loopExit hpre hX
  bound := TileHyps.tileBound hpre hX
  warp := fun _ _ _ hw => TileHyps.warp hpre hw
  base := hbase
  first := fun c w _ _ => TileHyps.firstLoad hpre hX (c * L.block + 32 * w)
  early := TileHyps.earlyWrites hpre hX

/-- **The conclusion of the induction over the tiles** (`Values.TileClaim`: the invariant of
the data registers of every compute lane, a matrix event at every matrix site, a followed
successor, real matrices as the operands of the multiply-accumulates), from the induction
(`Values.tile_induction`) and the hypotheses of `tileHyps`. -/
theorem tileClaim (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {O : Owners} (F : Facts P L X) (U : UnionFacts L X (ctaTiles P) O)
    (hW : Source.WriteFrame P X) (hacc : TileHyps.AccRead P L X)
    (hbase : TileHyps.BaseCase P L mem0 X) : Values.TileClaim P L mem0 X :=
  Values.tile_induction (tileHyps hpre hX F U hW hacc hbase)

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
