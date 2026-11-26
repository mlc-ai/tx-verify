-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.DirectData
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Sites
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.ExportsValues
public import Kernels.FlashKdaFwd.Proof.Values.TileClaim

@[expose] public section

/-!
# The tile loop's data half of "no undefined behaviour"

The two fields `matrixEv` and `tileNext` of `DataHalf` (`DirectData.lean`), for every consistent
execution under the launch precondition, from the conclusion of the induction over the tiles
(`Values.TileClaim`, `Proof/Values/TileClaim.lean`), which is taken as a hypothesis:

* `matrixEv`: the event of a compute thread at a followed state at a matrix site (the second
  event of an `ldmatrix`, an `mma.sync`, a `movmatrix`, the first event of an `stmatrix`) is not
  undefined behaviour;
* `tileNext`: after the event of a compute thread at a followed state at a site of the data path
  of the tile loop (`TileSite`: the matrix sites, the row read of an `ldmatrix`, the row write of
  an `stmatrix`, the eighteen scalar loads), the machine has a state again.

**Words.** A *compute thread* is a thread with index below 128 in its thread block; it is lane
`l` (below 32) of warp `w` (below 4) of block `c`, that is the thread
`c * L.block + 32 * w + l`. A *followed state* of thread `g` at position `k` is the state of
its machine before its `k`-th event (`Frame.stateAt (code L) X g k = some (some s)`, written
`At (code L) X g k s`). The *ordinal* `WarpMatrix.ordinal X g k` is the number of warp matrix
events among the first `k` events of the thread. A *position* of the Compute phase of the
reference layer (`Proof/Ref/Compute/Inv.lean`) is a pair of a tile `t` and an index `n < 268`
in the straight line of the tile's events: 0 and 1 are the two polls, 2 to 263 the events of
the data path, 264 to 267 the named barrier, the fence and the two arrivals. The *ledger* of
the phase is its count of the thread's earlier events by class; at position `n` of tile `t` it
has `182 * t + matOf n` matrix events and `t` named barriers (for `n < 265`).

**The proof.** The induction's invariant `Values.Val` puts a followed state of a compute lane
with `N` matrix events in one of four cases (`Values.Inv`). `tile_cases` shows that at a site
of the data path, before an event, only two of them occur, and these are exactly the two
premises of `TileClaim.alive`:

1. `SiteOk`: the lane is at a program point of count `N % 182` of tile `N / 182` and its data
   registers satisfy the table of that point. Then `TileClaim.matrix` gives that the event at a
   matrix site is a matrix event, and `TileClaim.alive` that the successor is followed.
2. `TailOk` (only when `N % 182 = 0` and `N / 182 ≥ 1`): the lane is in the tail of the tile
   before. A site of the tail that is a site of the data path is the row write of the last
   `stmatrix` (`matrixStoreWr 17 _`), which is the second premise of `TileClaim.alive`; it is no
   matrix site. The other sites of the tail are control sites (`not_tail`).
3. `Left`: the lane was at the site after the exit branch of the loop (`bar_7`, instruction
   3113) at an earlier position. Excluded by `not_left`: at that earlier position the chain
   (`Assembly.stage`, `Stage.of_pc_epilogue`) gives the exit ledger of the Compute phase, with
   one named barrier per tile of the sequence; at the present position it gives the ledger of
   a position of the data path of a tile `t` of the sequence (`tile_pos`), with `t` named
   barriers; a count of earlier events does not decrease along the trace.
4. `N = 0` and the lane has not been at the first `ldmatrix` (`¬ Entered`). Excluded by
   `entered`: the ledger of a position of the data path with no matrix event is that of one of
   the two events of the first `ldmatrix` of tile 0 (`first_table`), so the lane is there now.

No hypothesis remains besides the precondition, consistency and the claim. In particular the
phase facts `Values.LoopExit` and `Values.TileBound` are not needed: the count of named
barriers separates the tile loop from what follows it at every site of the data path, the row
write of the last `stmatrix` of the last tile included (where the count of matrix events does
not).

Everything except the two final theorems is in the namespace `Assembly.TileNoUb`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.TileNoUb
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat} {s : D}
  {e : Event}

/-! ### The sites of the data path -/

/-- A matrix site is a site of the data path of the tile loop. -/
theorem tile_of_matrix {site : Site} (h : MatrixSite site) : TileSite site := by
  cases site <;> first
    | exact False.elim h
    | trivial

/-- A matrix site, as the four alternatives of `TileClaim.matrix`. -/
theorem matrix_shape {site : Site} (h : MatrixSite site) :
    (∃ j row, site = .matrixLoadMx j row) ∨ (∃ j, site = .warpMma j) ∨
      (∃ j, site = .matrixMove j) ∨ ∃ j, site = .matrixStore j := by
  cases site with
  | matrixLoadMx j row => exact .inl ⟨j, row, rfl⟩
  | warpMma j => exact .inr (.inl ⟨j, rfl⟩)
  | matrixMove j => exact .inr (.inr (.inl ⟨j, rfl⟩))
  | matrixStore j => exact .inr (.inr (.inr ⟨j, rfl⟩))
  | _ => exact False.elim h

/-- The sites of the data path are instructions of the compute loop (2106 to 2944). -/
theorem tile_site_pc {site : Site} (h : TileSite site) : 2105 < site.pc ∧ site.pc ≤ 2944 := by
  have h1 : ∀ j : Fin 104, 2105 < (Site.warpMma j).pc ∧ (Site.warpMma j).pc ≤ 2944 := by
    decide +kernel
  have h2 : ∀ j : Fin 16, 2105 < (Site.matrixMove j).pc ∧ (Site.matrixMove j).pc ≤ 2944 := by
    decide +kernel
  have h3 : ∀ j : Fin 18, 2105 < (Site.matrixStore j).pc ∧ (Site.matrixStore j).pc ≤ 2944 := by
    decide +kernel
  have h4 : ∀ j : Fin 44, 2105 < (Site.matrixLoad j).pc ∧ (Site.matrixLoad j).pc ≤ 2944 := by
    decide +kernel
  have h5 : ∀ j : Fin 178, 159 ≤ j.val → j.val ≤ 176 →
      2105 < (Site.load j).pc ∧ (Site.load j).pc ≤ 2944 := by
    decide +kernel
  cases site with
  | warpMma j => exact h1 j
  | matrixMove j => exact h2 j
  | matrixStore j => exact h3 j
  | matrixStoreWr j row => exact h3 j
  | matrixLoad j => exact h4 j
  | matrixLoadMx j row => exact h4 j
  | load j => exact h5 j h.1 h.2
  | _ => exact False.elim h

/-- No site of the tail of a tile (`Values.TailSite`: the named barrier, the fence, the two
arrivals, the two polls, the barrier after the exit branch, five breakpoints) is a site of the
data path. -/
theorem not_tail {site : Site} (h : TileSite site) : ¬ Values.TailSite site := by
  rintro (r | r | r | r | r | r | r | r | r | r | r | r) <;>
    · rw [r] at h
      exact h

/-- The kinds of site (`Compute.SK`) of the data path of the tile loop. -/
def isBody : Compute.SK → Bool
  | .ld _ | .ldMx _ | .mma _ | .mv _ | .st _ | .stWr _ => true
  | .load j => decide (159 ≤ j.val) && decide (j.val ≤ 176)
  | _ => false

/-- The kind of a site of the data path is a kind of the data path. -/
theorem body_of_at {q : Compute.SK} {site : Site} (hat : q.At site) (h : TileSite site) :
    isBody q = true := by
  have hq := Compute.SK.at_iff.mp hat
  cases site <;> first
    | exact False.elim h
    | (simp only [Compute.SK.ofSite, Option.some.injEq] at hq
       subst hq
       first
         | rfl
         | (simp only [isBody, Bool.and_eq_true, decide_eq_true_eq]
            exact h))

/-- **The positions of the data path** of a tile are 2 to 263: after the two polls and before
the named barrier. -/
theorem body_table : ∀ n < 268, isBody (Compute.skOf n) = true → 2 ≤ n ∧ n < 264 := by
  decide +kernel

/-- **A position of the data path before the tile's first matrix event** is one of the two
events of the first `ldmatrix`. -/
theorem first_table : ∀ n < 268, isBody (Compute.skOf n) = true → Compute.matOf n = 0 →
    Compute.skOf n = .ld 0 ∨ Compute.skOf n = .ldMx 0 := by
  decide +kernel

/-! ### The position of a state at a site of the data path -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **A followed state at a site of the data path is at a position of the data path** of a
tile `t` of the sequence, in the Compute phase of a compute thread: position `n` between 2 and
263, with that position's ledger. -/
theorem tile_pos (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k s)
    (hs : TileSite s.site) :
    tid g < 128 ∧ ∃ t n, 2 ≤ n ∧ n < 264 ∧ t < Compute.tilesOf P g ∧
      (Compute.skOf n).At s.site ∧
      Compute.ledOf L (g / L.block) ((X.tr g).take k) = Compute.led (.tile t n) := by
  obtain ⟨h1, h2⟩ := tile_site_pc hs
  obtain ⟨hr, j0, s0, -, -, -, hI⟩ := (stage hpre hX hg hk hσ).of_pc_compute h1 h2
  have hne : s.site ≠ .bar 5 := by
    intro h5
    rw [h5] at hs
    exact hs
  obtain ⟨t, n, hn, ht, -, hR, hled, -⟩ := Compute.Vals.tile_of hI hne
  have hat : (Compute.skOf n).At s.site := hR.site
  obtain ⟨hn2, hn264⟩ := body_table n hn (body_of_at hat hs)
  exact ⟨hr, t, n, hn2, hn264, ht, hat, hled⟩

/-- **A lane at a site of the data path has not left the tile loop**: it was not at the site
after the exit branch (`bar_7`) at an earlier position. At `bar_7` the thread has made one
named barrier per tile of its sequence (the exit ledger of the Compute phase, which the chain
keeps in the history record of the epilogue); at a position of the data path of tile `t` it
has made `t`, and `t` is below the number of tiles. -/
theorem not_left (he : X.get (g, k) = some e) (hσ : At (code L) X g k s)
    (hs : TileSite s.site) : ¬ Values.Left (L := L) X g k := by
  rintro ⟨k', hk', -, d', hσ', hs'⟩
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨hr, t, n, -, hn, ht, -, hled⟩ := tile_pos hpre hX hg hk.le hσ hs
  have hpc : d'.site.pc = 3113 := by
    rw [hs']
    rfl
  obtain ⟨j1, s1, hdone, hj1, -, -⟩ :=
    (stage hpre hX hg (by omega : k' ≤ (X.tr g).length) hσ').of_pc_epilogue (by omega)
      (.inl (noUb_of_lt hX (by omega)))
  obtain ⟨j0, s0, -, -, ⟨-, -, hO, -⟩ | ⟨hr4, -⟩ | ⟨hr5, -⟩⟩ := hdone.entry
  · have h1 : ((X.tr g).take j1).countP (Execution.isBarId 8) = Compute.tilesOf P g :=
      congrArg Compute.Led.bar8 hO.2.1
    have h2 : ((X.tr g).take k).countP (Execution.isBarId 8) = t + Compute.ind 265 n :=
      congrArg Compute.Led.bar8 hled
    have h3 := (List.take_sublist_take_left (l := X.tr g) (show j1 ≤ k by omega)).countP_le
      (p := Execution.isBarId 8)
    have h4 : Compute.ind 265 n = 0 := by
      unfold Compute.ind
      split
      · omega
      · rfl
    omega
  · unfold tid at hr
    unfold warp at hr4
    omega
  · unfold tid at hr
    unfold warp at hr5
    omega

/-- **A lane at a site of the data path that has made no matrix event is at the first
`ldmatrix`**, so it has entered the tile loop (`Values.Entered`). -/
theorem entered (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k s) (hs : TileSite s.site)
    (h0 : WarpMatrix.ordinal X g k = 0) : Values.Entered (L := L) X g k := by
  obtain ⟨-, t, n, -, hn, -, hat, hled⟩ := tile_pos hpre hX hg hk hσ hs
  have hm := Compute.Vals.mats_tile hled
  refine ⟨k, le_rfl, s, hσ, ?_⟩
  rcases first_table n (by omega) (body_of_at hat hs) (by omega) with h | h
  · rw [h] at hat
    exact .inl hat
  · rw [h] at hat
    exact .inr hat

end

/-! ### The cases of the induction's invariant at a site of the data path -/

/-- A launched compute thread is a lane of a compute warp of a thread block. -/
theorem lane_split (hg : g < L.threads) (hc : g % L.block < 128) :
    ∃ c w l, c < L.grid ∧ w < 4 ∧ l < 32 ∧ g = c * L.block + 32 * w + l := by
  refine ⟨g / L.block, g % L.block / 32, g % L.block % 32, ?_, by omega,
    Nat.mod_lt _ (by decide), ?_⟩
  · exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  · have h1 := Nat.div_add_mod g L.block
    rw [Nat.mul_comm] at h1
    omega

/-- **The state of a compute lane before an event at a site of the data path** satisfies one
of the two premises of `TileClaim.alive`: it is at a program point of its count with that
point's table (`Values.SiteOk`), or it is at the row write of the last `stmatrix` of a tile
with the carries of the next tile (`Values.TailOk`). The two other cases of the induction's
invariant, "the lane has left the loop" and "the lane has not entered it", do not occur at
such a site. -/
theorem tile_cases (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (T : Values.TileClaim P L mem0 X) {c w l : Nat} (hc : c < L.grid) (hw : w < 4)
    (hl : l < 32) (hgeq : g = c * L.block + 32 * w + l) (hg : g < L.threads)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (he : X.get (g, k) = some e)
    (hs : TileSite s.site) :
    Values.SiteOk (Values.blockInputs P mem0 c (WarpMatrix.ordinal X g k / 182)) w l
        (WarpMatrix.ordinal X g k % 182) s ∨
      (WarpMatrix.ordinal X g k % 182 = 0 ∧ 1 ≤ WarpMatrix.ordinal X g k / 182 ∧
        (∃ row, s.site = .matrixStoreWr 17 row) ∧
        Values.TailOk (Values.blockInputs P mem0 c (WarpMatrix.ordinal X g k / 182 - 1))
          (Values.blockInputs P mem0 c (WarpMatrix.ordinal X g k / 182)) w l s) := by
  subst hgeq
  have hk : k < (X.tr (c * L.block + 32 * w + l)).length :=
    (List.getElem?_eq_some_iff.mp he).1
  rcases T.val c w hc hw _ l hl k rfl s hσ with h | ⟨h0, h1, ht⟩ | ⟨-, -, hleft⟩ | ⟨h0, hne⟩
  · exact .inl h
  · rcases ht.1 with ⟨row, hrow, -⟩ | htail
    · exact .inr ⟨h0, h1, ⟨row, hrow⟩, ht⟩
    · exact (not_tail hs htail).elim
  · exact (not_left hpre hX hg he hσ hs hleft).elim
  · exact (hne (entered hpre hX hg hk.le hσ hs h0)).elim

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.TileNoUb

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`DataHalf.matrixEv`**, verbatim: the event of a launched compute thread at a followed
state at a matrix site is not undefined behaviour. From the claim of the induction over the
tiles: the state satisfies the table of its program point, so the event is a matrix event. -/
theorem matrixEv (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (T : Values.TileClaim P L mem0 X) : ∀ g k s e, g < L.threads → g % L.block < 128 →
    Frame.stateAt (code L) X g k = some (some s) → MatrixSite s.site →
    X.get (g, k) = some e → ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  intro g k s e hg hc hσ hs he pc f hub
  obtain ⟨c, w, l, hc', hw, hl, hgeq⟩ := TileNoUb.lane_split hg hc
  have hm : isMatrix e = true := by
    rcases TileNoUb.tile_cases hpre hX T hc' hw hl hgeq hg hσ he (TileNoUb.tile_of_matrix hs)
      with h | ⟨-, -, ⟨row, hrow⟩, -⟩
    · subst hgeq
      exact T.matrix c w hc' hw l hl k s e hσ he h (TileNoUb.matrix_shape hs)
    · rw [hrow] at hs
      exact hs.elim
  rw [hub] at hm
  cases hm

/-- **`DataHalf.tileNext`**, verbatim: after the event of a launched compute thread at a
followed state at a site of the data path of the tile loop, the machine has a state again. From
the claim of the induction over the tiles: the state satisfies the table of its program point,
or is at the row write of the last `stmatrix` of a tile with the carries of the next tile, and
in both cases no instruction up to the next event faults. -/
theorem tileNext (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (T : Values.TileClaim P L mem0 X) : ∀ g k s e, g < L.threads → g % L.block < 128 →
    Frame.stateAt (code L) X g k = some (some s) → TileSite s.site →
    X.get (g, k) = some e → ∃ s', Frame.stateAt (code L) X g (k + 1) = some (some s') := by
  intro g k s e hg hc hσ hs he
  obtain ⟨c, w, l, hc', hw, hl, hgeq⟩ := TileNoUb.lane_split hg hc
  have h := TileNoUb.tile_cases hpre hX T hc' hw hl hgeq hg hσ he hs
  subst hgeq
  exact T.alive c w hc' hw l hl k s e hσ he h

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
