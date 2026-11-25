-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Gen.Steps
public import Kernels.FlashKdaFwd.Proof.Values.TileClaim
public import Kernels.FlashKdaFwd.Proof.Values.TileAlgebra
public import Lemmas.Flow.NotClc

@[expose] public section

/-!
# The rows of `state_acc` that the loads of a tile read

`state_acc` is the buffer of shared memory (window bytes 0 to 32767) that holds the bfloat16
copy of the state. In each tile, sixteen of the 44 `ldmatrix` instructions read it, one per
value block `bi < 2` of the warp and key block `m < 8` (`loadSrc j = .state bi m`), and sixteen
of the 18 `stmatrix` instructions write the new state back to it (`storeSrc j' = .state bi m`).
This file proves `acc_rows`: the sixteen bytes a compute lane reads at the first event of such
an `ldmatrix` are the row of the load's source for the real arrays of the lane's tile
(`LoadSrc.RowOk`, for this source the list `LoadSrc.row`): the bfloat16 payloads of the state
before the tile. The induction over the tiles (`Tile.lean`) uses it at each of these loads,
with its own invariant at the lane's earlier positions.

Words and names used below.

* A *compute warp* of thread block `c` has the first thread `w0 = c * L.block + 32 * w`, with
  the warp number `w < 4`; its *lane* `l < 32` is the thread `w0 + l`, whose index in the block
  is `32 * w + l`. A *position* `k` of a lane's trace is the index of an event;
  `stateAt (code L) X g k` is the state of the lane's machine before that event (a *followed*
  state when it is `some (some d)`) and `ordinal X g k` the number of warp matrix events before
  it. A tile has 182 matrix events, so the lane is in tile `ordinal / 182` and has made
  `ordinal % 182` matrix events of that tile, its *count*.
* `blockInputs P mem0 c b` are the real arrays of tile `b` of thread block `c`; their field
  `copy` is the state before the tile. `tileInputs_chain` says the state before tile `b + 1` is
  the state tile `b` leaves (`stateAfter`), and `tileInputs_first` that the state before tile 0
  is the initial state `P.initial`.
* `loadOff j b tid` and `storeOff j b tid` (`Contract.lean`) are the offsets from the start of
  the shared window of the row that the thread with index `tid` reads at the `j`-th `ldmatrix`
  and writes at the `j`-th `stmatrix` of tile `b`; `bitsOff ws tid` is their thread-dependent
  part. `ComputeRef.loadRow` and `ComputeRef.storeRow` say the lane's events are a read and a
  write of sixteen bytes at these offsets.
* `ReadBack.acc` says what a read of sixteen bytes of `state_acc` returns: the bytes of the
  lane's own last write of sixteen bytes at the same address, or, when there is none, the bytes
  the conversion loop of the prologue left there (`accInitByte`).
* The invariant of the value induction (`Induction.lean`): `Inv` for one followed state, `ValAt`
  for a position of a lane. It says the lane is at a program point of its count (`pointsAt`,
  with the points `Pt`: `rd` and `mx` for the two events of a load, `st` and `wr` for the two
  events of a store, `mma`, `mov`, and `ld` for a scalar load) and, at the row write of a store
  (`wr`), that it holds the row of the store for the arrays of its tile (`StoreSrc.row`); or
  that it is in the tail between two tiles (`TailOk`, at the row write of the last store or at
  a control site `TailSite`), has left the loop (`Left`), or has not entered it.

The proof. The read is at the offset of the row of the blocks `bi`, `m` of the lane, which does
not depend on the tile; the store of the same blocks writes at the same offset, the other
stores of `state_acc` at other offsets, and the two stores of the output stage past
`state_acc` (`acc_load`, `acc_store`, `acc_store_unique`: checks of the generated lists). By
the invariant, a write event of a lane that has made a matrix event is the row write of a
store, with the row of the arrays of its tile (`write_of_inv`): at the other points of a tile
the event is a matrix event or a read, and the instructions at the control sites of the tail
are no stores (`tail_no_write`). In a tile `b ≥ 1` the lane has made the row write of the store
of the same blocks in tile `b - 1` (`store_write_before`), so the last write of the row before
the read exists and is not older; it is a row write of that store in tile `b - 1`, because a
tile has no store before its loads of `state_acc`; and the row that store writes is the row
the load of tile `b` reads (`acc_chain_row`: the transposing store writes the new state in the
layout `Math.Fragments.stateTiles` in which the load reads the state copy, and the tiles form
a chain). In tile 0 there is no write of sixteen bytes of the row before the read, and the
bytes the conversion loop left are the row of the initial state (`acc_init_row`).

Besides the contracts, `acc_rows` takes `TileBound` (the read is in a tile of the sequence:
the invariant alone does not exclude a lane that has left the loop) and the hypothesis
`hearly`: the lane makes no write of sixteen bytes before its first matrix event (the field
`early` of `TileHyps`, proved in `Proof/Ref/Assembly/TileEarly.lean`). The invariant says
nothing about a lane that has not entered the tile loop, and `ReadBack.acc` asks for the
absence of such writes in the first tile.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values
open PTX PTX.Flow PTX.Frame PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Math.Fragments
open PTX.Kernels.FlashKdaFwd.Recurrence (tiles)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ## The generated tables: the loads and stores of `state_acc` -/

/-- The weights of the seven bits of the thread index in the address of a row of `state_acc`
(the same list for the sixteen loads and the sixteen stores). -/
def accWeights : List ℕ := [16, 32, 64, 2048, 128, 512, 1024]

/-- The thread-dependent part of the address of a row of `state_acc`, for lane `l` of warp
`w`. -/
theorem bitsOff_acc {w l : ℕ} (hw : w < 4) (hl : l < 32) :
    bitsOff accWeights (32 * w + l) =
      16 * (l % 8) + 2048 * (l / 8 % 2) + 128 * (l / 16) + 512 * (w % 2) + 1024 * (w / 2) := by
  simp [bitsOff, accWeights, List.zipIdx]
  omega

/-- The thread-dependent part of the address of a row of `state_acc` is below 4096, the
distance between the rows of two key blocks. -/
theorem bitsOff_acc_le (tid : ℕ) : bitsOff accWeights tid ≤ 3824 := by
  simp [bitsOff, accWeights, List.zipIdx]
  omega

/-- The ordinal in the tile of the matrix event of the `j`-th `stmatrix`. -/
def storeOrd (j : Fin 18) : ℕ := Gen.ordSites.idxOf (.store j)

/-- The matrix event of each `stmatrix` has an ordinal from 124 to 181, and the site of that
ordinal (`ordSite`) is the store. -/
theorem storeOrd_spec : ∀ j : Fin 18,
    124 ≤ storeOrd j ∧ storeOrd j < 182 ∧ ordSite (storeOrd j) = .store j := by
  decide +kernel

/-- The Boolean check of one load: a load of `state_acc` has its indices in range and the
address form of its row, and the store with index `2 + 2 * m + bi` writes the same source at
the same address. -/
private def loadAcc (j : ℕ) : Bool :=
  match loadSrc j with
  | .state bi m => decide (bi < 2) && decide (m < 8) &&
      (Gen.loadForms[j]? == some (4096 * m + 256 * bi, 0, accWeights)) &&
      (storeSrc (2 + 2 * m + bi) == .state bi m) &&
      (Gen.storeForms[2 + 2 * m + bi]? == some (4096 * m + 256 * bi, 0, accWeights))
  | _ => true

private theorem loadAcc_all : ∀ j : Fin 44, loadAcc j.val = true := by decide +kernel

/-- The Boolean check of one store: a store of the output stage has an address constant of at
least 86912, a store of `state_acc` has its indices in range and the address form of its
row. -/
private def storeAcc (j : ℕ) : Bool :=
  match storeSrc j, Gen.storeForms[j]? with
  | .state bi m, some f => decide (bi < 2) && decide (m < 8) &&
      (f == (4096 * m + 256 * bi, 0, accWeights))
  | .out _, some f => decide (86912 ≤ f.1)
  | _, none => false

private theorem storeAcc_all : ∀ j : Fin 18, storeAcc j.val = true := by decide +kernel

/-- The Boolean check of one program point of count `n`: the row read of a load of `state_acc`
is in the first 96 counts, the row write of a store follows its matrix event, and a scalar load
is one of the load sites 159 to 176. -/
private def ptCheck (n : ℕ) : Pt → Bool
  | .rd j => match loadSrc j with
    | .state _ _ => decide (n < 96)
    | _ => true
  | .wr j => decide (n = storeOrd j + 1)
  | .ld i => decide (159 ≤ i.val ∧ i.val < 177)
  | _ => true

private theorem ptCheck_all : ∀ n : Fin 182,
    ((pointsAt n.val).all fun q => ptCheck n.val q.1) = true := by
  decide +kernel

/-- **A load of `state_acc`**, of value block `bi` and key block `m`: the blocks are in range,
the offset of the row does not depend on the tile, and the `stmatrix` with index
`2 + 2 * m + bi` writes the new state of the same blocks at the same offset. -/
theorem acc_load (j : Fin 44) {bi m : ℕ} (h : loadSrc j = .state bi m) :
    bi < 2 ∧ m < 8 ∧
      (∀ b tid, loadOff j b tid = 4096 * m + 256 * bi + bitsOff accWeights tid) ∧
      storeSrc (2 + 2 * m + bi) = .state bi m ∧
      ∀ b tid, storeOff (2 + 2 * m + bi) b tid =
        4096 * m + 256 * bi + bitsOff accWeights tid := by
  have h0 := loadAcc_all j
  unfold loadAcc at h0
  simp only [h, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h0
  obtain ⟨⟨⟨⟨hbi, hm⟩, hf⟩, hs⟩, hsf⟩ := h0
  refine ⟨hbi, hm, fun b tid => ?_, hs, fun b tid => ?_⟩
  · simp [loadOff, hf]
  · simp [storeOff, hsf]

/-- **The address of a store**: a store of the output stage writes at an offset of at least
86912, past `state_acc`; a store of `state_acc` writes the new state of a value block `bi` and
a key block `m` at the offset of the row of these blocks, in every tile. -/
theorem acc_store (j : Fin 18) :
    (∀ b tid, 86912 ≤ storeOff j b tid) ∨
      ∃ bi m, bi < 2 ∧ m < 8 ∧ storeSrc j = .state bi m ∧
        ∀ b tid, storeOff j b tid = 4096 * m + 256 * bi + bitsOff accWeights tid := by
  have h0 := storeAcc_all j
  unfold storeAcc at h0
  cases hf : Gen.storeForms[j.val]? with
  | none =>
    cases hs : storeSrc j.val <;> simp [hs, hf] at h0
  | some f =>
    obtain ⟨c0, st, ws⟩ := f
    cases hs : storeSrc j.val with
    | out bi =>
      simp only [hs, hf, decide_eq_true_eq] at h0
      refine .inl fun b tid => ?_
      simp only [storeOff, hf]
      omega
    | state bi m =>
      simp only [hs, hf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Prod.mk.injEq] at h0
      obtain ⟨⟨hbi, hm⟩, rfl, rfl, rfl⟩ := h0
      refine .inr ⟨bi, m, hbi, hm, rfl, fun b tid => ?_⟩
      simp [storeOff, hf]

/-- **Only the store of the same blocks writes at the offset of a load of `state_acc`**: a
store whose row offset, in any tile, is the row offset of the load of value block `bi` and key
block `m` for the same thread is the store of the new state of these blocks. So the sixteen
stores of `state_acc` and the two stores of the output stage write at different offsets. -/
theorem acc_store_unique {j : Fin 44} {bi m : ℕ} (h : loadSrc j = .state bi m) {j' : Fin 18}
    {b b' tid : ℕ} (hoff : storeOff j' b' tid = loadOff j b tid) :
    storeSrc j' = .state bi m := by
  obtain ⟨hbi, hm, hload, -, -⟩ := acc_load j h
  have hle := bitsOff_acc_le tid
  rw [hload] at hoff
  rcases acc_store j' with hout | ⟨bi2, m2, hbi2, hm2, hsrc2, hoff2⟩
  · have := hout b' tid
    omega
  · rw [hoff2] at hoff
    obtain rfl : m2 = m := by omega
    obtain rfl : bi2 = bi := by omega
    exact hsrc2

/-- The row read of a load of `state_acc` is a point of one of the first 96 counts. -/
theorem rd_count {n : ℕ} (hn : n < 182) {j : Fin 44} {T : Table} {bi m : ℕ}
    (hq : (Pt.rd j, T) ∈ pointsAt n) (h : loadSrc j = .state bi m) : n < 96 := by
  have h0 := List.all_eq_true.mp (ptCheck_all ⟨n, hn⟩) _ hq
  simpa only [ptCheck, h, decide_eq_true_eq] using h0

/-- The row write of a store is a point of the count after the store's matrix event. -/
theorem wr_count {n : ℕ} (hn : n < 182) {j : Fin 18} {T : Table}
    (hq : (Pt.wr j, T) ∈ pointsAt n) : n = storeOrd j + 1 := by
  have h0 := List.all_eq_true.mp (ptCheck_all ⟨n, hn⟩) _ hq
  simpa only [ptCheck, decide_eq_true_eq] using h0

/-- The scalar loads among the points of a tile are the load sites 159 to 176. -/
theorem ld_range {n : ℕ} (hn : n < 182) {i : Fin 178} {T : Table}
    (hq : (Pt.ld i, T) ∈ pointsAt n) : 159 ≤ i.val ∧ i.val < 177 := by
  have h0 := List.all_eq_true.mp (ptCheck_all ⟨n, hn⟩) _ hq
  simpa only [ptCheck, decide_eq_true_eq] using h0

/-! ## The bytes of a row: real numbers only -/

/-- **The row a store of `state_acc` writes is the row the next tile's load reads.** `x` are
the arrays of a tile and `x'` those of the next one, whose state copy is the state the tile
leaves (`hnext`). The transposing `stmatrix` of the new state of value block `bi` and key block
`m` gives lane `l` the sixteen bytes that the `ldmatrix` of these blocks reads in the next
tile. -/
theorem acc_chain_row {x x' : Inputs}
    (hnext : ∀ k ch, k < 128 → ch < 128 → x'.copy k ch = stateAfter x k ch) {w l bi m : ℕ}
    (hw : w < 4) (hl : l < 32) (hbi : bi < 2) (hm : m < 8) :
    (StoreSrc.state bi m).row x w l = (LoadSrc.state bi m).row x' w l := by
  unfold StoreSrc.row LoadSrc.row rowPart
  refine List.map_congr_left fun k hk => ?_
  have hk' := List.mem_range.mp hk
  show bf16Enc (transposeMats (ofFrag (pairFrag fun q => nextState x (halfBase w bi q) m))
      (l / 8) (l % 8) (k / 2)) (k % 2) =
    bf16Enc (stateTiles x'.copy (halfBase w bi 0) m (l / 8) (l % 8) (k / 2)) (k % 2)
  rw [transpose_pairFrag _ _ _ (by omega)]
  simp only [stateTiles]
  rw [hnext _ _ (by omega) (by rw [halfBase_zero]; omega), stateAfter]
  have e1 : 8 * ((halfBase w bi 0 + 8 * (l / 8 / 2) + l % 8) / 8) = halfBase w bi (l / 8 / 2) := by
    unfold halfBase
    omega
  have e2 : (16 * m + 8 * (l / 8 % 2) + k / 2) / 16 = m := by omega
  have e3 : (16 * m + 8 * (l / 8 % 2) + k / 2) % 16 = 8 * (l / 8 % 2) + k / 2 := by omega
  have e4 : (halfBase w bi 0 + 8 * (l / 8 / 2) + l % 8) % 8 = l % 8 := by
    unfold halfBase
    omega
  rw [e1, e2, e3, e4]

/-- A byte of `state_acc` after the conversion loop, as the bfloat16 payload of the state before
the first tile: the byte at offset `o` belongs to the key feature `k` and the value channel
`ch` that the element index `o / 2` names. -/
theorem accInitByte_eq (P : Params) (mem0 : Mem0) (s h : ℕ) {o k ch : ℕ} (hk : k < 128)
    (hch : ch < 128) (ek : 8 * (o / 2 / 1024) + o / 2 % 8 = k)
    (ech : 8 * (o / 2 / 64 % 16) + o / 2 / 8 % 8 = ch) :
    accInitByte P s h o = bf16Enc ((tileInputs P mem0 s h 0).copy k ch) (o % 2) := by
  subst ek ech
  rw [tileInputs_copy, tileInputs_first P mem0 s h hk hch]
  exact dite_eq_left ⟨hch, hk⟩

/-- **The row a load of `state_acc` reads in the first tile, before any row write**: the
sixteen bytes the conversion loop left at the offset of the row of value block `bi` and key
block `m` of lane `l` of warp `w` are the row of the load for the arrays of tile 0. -/
theorem acc_init_row (P : Params) (mem0 : Mem0) (s h : ℕ) {w l bi m : ℕ} (hw : w < 4)
    (hl : l < 32) (hbi : bi < 2) (hm : m < 8) :
    ((List.range 16).map fun i =>
        accInitByte P s h (4096 * m + 256 * bi + bitsOff accWeights (32 * w + l) + i)) =
      (LoadSrc.state bi m).row (tileInputs P mem0 s h 0) w l := by
  rw [bitsOff_acc hw hl]
  unfold LoadSrc.row rowPart
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  have h16 : l / 8 / 2 = l / 16 := by omega
  have hp : (4096 * m + 256 * bi + (16 * (l % 8) + 2048 * (l / 8 % 2) + 128 * (l / 16) +
      512 * (w % 2) + 1024 * (w / 2)) + i) / 2 =
      64 * (32 * m + 2 * bi + 16 * (l / 8 % 2) + l / 16 + 4 * (w % 2) + 8 * (w / 2)) +
        (8 * (l % 8) + i / 2) := by omega
  rw [accInitByte_eq P mem0 s h (k := 16 * m + 8 * (l / 8 % 2) + i / 2)
    (ch := halfBase w bi 0 + 8 * (l / 8 / 2) + l % 8) (by omega) (by rw [halfBase_zero]; omega)
    (by rw [hp]; omega) (by rw [hp, halfBase_zero, h16]; omega)]
  rw [show (4096 * m + 256 * bi + (16 * (l % 8) + 2048 * (l / 8 % 2) + 128 * (l / 16) +
    512 * (w % 2) + 1024 * (w / 2)) + i) % 2 = i % 2 by omega]
  rfl

/-! ## The write events of a lane -/

/-- **No write at a control site of the tail of a tile**: the instruction at each of these
sites is a `bar.sync`, a fence, an mbarrier arrival, an mbarrier poll or a `trap`, and only a
store instruction makes a write event (`Flow.fires_write_op`). -/
theorem tail_no_write (F : Followed L mem0 X) {g k : ℕ} {d : D} {e : Event}
    (hσ : stateAt (code L) X g k = some (some d)) (he : X.get (g, k) = some e)
    (hs : TailSite d.site) (a : Acc) (bs : List Byte) : e.kind ≠ .wr a bs := by
  intro hk
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := fired_site F.sound F.consistent he hσ
  have hw := fires_write_op hf hk
  have hc' : kernel.code[d.site.pc]? = some ins := hc
  rcases hs with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at hc'
  · obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_2913)
    cases hw
  · obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_2914)
    cases hw
  · obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_2920)
    cases hw
  · obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_2928)
    cases hw
  · obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_2144)
    cases hw
  · obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_2186)
    cases hw
  · obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_3113)
    cases hw
  · obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_2138)
    cases hw
  · obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_2148)
    cases hw
  · obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_2916)
    cases hw
  · obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_2922)
    cases hw
  · obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_2930)
    cases hw

/-- The matrix event of the last store of a tile is the last matrix event of the tile. -/
theorem storeOrd_last : storeOrd 17 = 181 := by decide +kernel

/-- **A write of a lane in the tile loop is the row write of a store.** A lane whose state
satisfies the invariant, that has made a matrix event (`h0`) and is in a tile of its sequence
(`hlt`), makes a write event only as the row write of a store `j` of a tile `b`, right after
the store's matrix event (the count is `182 * b + storeOrd j + 1`); it writes the row of the
store for the arrays of tile `b`, sixteen bytes at the offset of the store. -/
theorem write_of_inv (F : Followed L mem0 X) (R : ComputeRef P L X) (E : LoopExit P L X)
    {w0 w : ℕ} (W : Warp L w0) {xs : ℕ → Inputs} (hsc : ScalarsRead (L := L) xs X w0)
    {l k : ℕ} (hl : l < 32) {d : D} {pc : ℕ} {a : Acc} {bs : List Byte}
    (hσ : stateAt (code L) X (w0 + l) k = some (some d))
    (he : X.get (w0 + l, k) = some ⟨pc, .wr a bs⟩)
    (hinv : Inv (L := L) xs w l X (w0 + l) k (ordinal X (w0 + l) k) d)
    (h0 : ordinal X (w0 + l) k ≠ 0)
    (hlt : ordinal X (w0 + l) k / 182 < tileCount P L (w0 + l)) :
    ∃ (j : Fin 18) (b : ℕ), ordinal X (w0 + l) k = 182 * b + storeOrd j + 1 ∧
      bs = ((storeSrc j).row (xs b) w l).reduceOption ∧ a.size = 16 ∧
      a.loc = ⟨.shared, (w0 + l) / L.block,
        P.sharedBase + storeOff j (ordinal X (w0 + l) k / 182) ((w0 + l) % L.block)⟩ := by
  have hcomp := W.compute l hl
  have hn : ordinal X (w0 + l) k % 182 < 182 := Nat.mod_lt _ (by decide)
  have hpts := Gen.lpts F R W (w := w) hsc hl (k := k) (N := ordinal X (w0 + l) k) hn
  rcases hinv with ⟨⟨pt, T⟩, hq, hat, hT⟩ | ⟨hz, h1, hs | hs, -⟩ |
    ⟨hz, h1, k0, hk0, ho, d0, hσ0, hs0⟩ | ⟨hz, -⟩
  · cases pt with
    | rd j =>
      have hs : d.site = .matrixLoad j := hat
      obtain ⟨a', bs', h, -⟩ := R.loadRow _ k d _ j hcomp hσ hs he
      cases h
    | ld i =>
      have hs : d.site = .load i := hat
      obtain ⟨hi, hi'⟩ := ld_range hn hq
      obtain ⟨pc', a', bs', h, -⟩ := hsc l hl k d _ i hi hi' hσ hs he
      cases h
    | wr j =>
      obtain ⟨row, hs, hrow⟩ := hat
      obtain ⟨a', h, hsz, hloc⟩ := R.storeRow _ k d _ j row hcomp hσ hs he
      injection h with h1 h2
      injection h2 with h3 h4
      subst h3 h4
      have hc := wr_count hn hq
      exact ⟨j, ordinal X (w0 + l) k / 182, by omega, by rw [hrow], hsz, hloc⟩
    | mx j =>
      have hm := ((hpts.mem _ hq).2 rfl d _ hσ he ⟨hat, hT⟩).1
      cases hm
    | mma j =>
      have hm := ((hpts.mem _ hq).2 rfl d _ hσ he ⟨hat, hT⟩).1
      cases hm
    | mov j =>
      have hm := ((hpts.mem _ hq).2 rfl d _ hσ he ⟨hat, hT⟩).1
      cases hm
    | st j =>
      have hm := ((hpts.mem _ hq).2 rfl d _ hσ he ⟨hat, hT⟩).1
      cases hm
  · obtain ⟨row, hs, hrow⟩ := hs
    obtain ⟨a', h, hsz, hloc⟩ := R.storeRow _ k d _ 17 row hcomp hσ hs he
    injection h with h1 h2
    injection h2 with h3 h4
    subst h3 h4
    have h17 := storeOrd_last
    refine ⟨17, ordinal X (w0 + l) k / 182 - 1, by omega, ?_, hsz, hloc⟩
    rw [hrow]
    rfl
  · exact absurd rfl (tail_no_write F hσ he hs a bs)
  · exfalso
    have h := E (w0 + l) k0 d0 hcomp hσ0 hs0
    rw [ho] at h
    omega
  · exact absurd hz h0

/-- **The row write of a store, found in the trace.** A lane that has made more than `N`
matrix events before position `k`, where `N` is the count of the matrix event of the `j`-th
`stmatrix` of a tile, and that is not at the row write of that store at `k`, has made the row
write at a position `k1 + 1` before `k`: a write of sixteen bytes at the offset of the store,
right after the matrix event (the count there is `N + 1`). -/
theorem store_write_before (F : Followed L mem0 X) (R : ComputeRef P L X) {w0 : ℕ}
    (W : Warp L w0) {l k : ℕ} (hl : l < 32) {d : D} {e : Event}
    (hσ : stateAt (code L) X (w0 + l) k = some (some d)) (he : X.get (w0 + l, k) = some e)
    (j : Fin 18) (hns : ∀ row, d.site ≠ .matrixStoreWr j row) {N : ℕ}
    (hN : N % 182 = storeOrd j) (hlt : N < ordinal X (w0 + l) k) :
    ∃ k1, k1 + 1 < k ∧ ordinal X (w0 + l) (k1 + 1) = N + 1 ∧
      ∃ pc a bs, X.get (w0 + l, k1 + 1) = some ⟨pc, .wr a bs⟩ ∧ a.size = 16 ∧
        a.loc = ⟨.shared, (w0 + l) / L.block,
          P.sharedBase + storeOff j ((N + 1) / 182) ((w0 + l) % L.block)⟩ := by
  have hcomp := W.compute l hl
  have hg : w0 + l < L.threads := lt_of_get F.consistent he
  have hcnt : N < (X.tr (w0 + l)).countP isMatrix :=
    lt_of_lt_of_le hlt (List.take_sublist _ _).countP_le
  obtain ⟨k1, hk1⟩ := exists_matrixK_of_lt_countP hcnt
  have hk1lt : k1 < k := by
    by_contra hge
    have h1 : ordinal X (w0 + l) k ≤ ordinal X (w0 + l) k1 := ordinal_mono (by omega)
    have h2 := matrixK_ordinal hk1
    omega
  obtain ⟨e0, d0, he0, hm0, hσ0⟩ := state_of_matrixK F hk1
  have hsite := R.site (w0 + l) k1 N d0 hcomp hk1 hσ0
  rw [hN, (storeOrd_spec j).2.2] at hsite
  have hs0 : d0.site = .matrixStore j := hsite
  obtain ⟨pc0, kd⟩ := e0
  cases kd with
  | matrix op own recv =>
    have hσ1 : stateAt (code L) X (w0 + l) (k1 + 1) = stRecv d0 recv (.matrixStoreWr j) := by
      rw [stateAt_next he0 hσ0]
      exact Gen.store_next j _ d0 pc0 op own recv hs0
    obtain ⟨d1, hd1⟩ := stateAt_live F.tracked hg hσ (show k1 + 1 ≤ k by omega)
    have hs1 : d1.site = .matrixStoreWr j recv := by
      rw [hσ1] at hd1
      unfold stRecv at hd1
      split_ifs at hd1
      obtain rfl := Option.some.inj (Option.some.inj hd1)
      rfl
    have hk1' : k1 + 1 < k := by
      rcases Nat.lt_or_ge (k1 + 1) k with h | h
      · exact h
      · exfalso
        have hk : k1 + 1 = k := by omega
        subst hk
        have hdd : d = d1 := Option.some.inj (Option.some.inj (hσ.symm.trans hd1))
        exact hns recv (hdd ▸ hs1)
    have hlen : k1 + 1 < (X.tr (w0 + l)).length := by
      have h : k < (X.tr (w0 + l)).length := (List.getElem?_eq_some_iff.mp he).1
      omega
    obtain ⟨e1, he1⟩ : ∃ e1, X.get (w0 + l, k1 + 1) = some e1 :=
      ⟨_, List.getElem?_eq_getElem hlen⟩
    obtain ⟨a, rfl, hsz, hloc⟩ := R.storeRow _ (k1 + 1) d1 e1 j recv hcomp hd1 hs1 he1
    have hord := ordinal_succ_of_matrixK hk1
    rw [hord] at hloc
    exact ⟨k1, hk1', hord, _, a, _, he1, hsz, hloc⟩
  | _ => cases hm0

/-! ## The rows the loads of `state_acc` read -/

/-- **The row a lane reads from `state_acc`.** Lane `l` of the compute warp `w` of thread block
`c`, at the first event of an `ldmatrix` whose source is `state_acc` (value block `bi`, key
block `m`), reads the row of that source for the arrays of its tile: the bfloat16 copy of the
state before the tile. `hist` is the invariant at the positions of the lane up to the read.
`hT` says the read is in a tile of the sequence. `hearly` says the lane makes no write of
sixteen bytes before its first matrix event (the conversion loop of the prologue stores two
bytes at a time); the invariant says nothing about the lane there. -/
theorem acc_rows (hpre : Pre P L mem0) (F : Followed L mem0 X) (R : ComputeRef P L X)
    (B : ReadBack P L mem0 X) (E : LoopExit P L X) (hT : TileBound P L X) {c w : ℕ}
    (hc : c < L.grid) (hw : w < 4) (W : Warp L (c * L.block + 32 * w))
    (hsc : ScalarsRead (L := L) (blockInputs P mem0 c) X (c * L.block + 32 * w))
    {l k : ℕ} (hl : l < 32)
    (hearly : ∀ k' pc a bs, ordinal X (c * L.block + 32 * w + l) k' = 0 →
      X.get (c * L.block + 32 * w + l, k') = some ⟨pc, .wr a bs⟩ → a.size ≠ 16)
    {d : D} {e : Event}
    (hist : ∀ k' ≤ k, ValAt (L := L) (blockInputs P mem0 c) w X (c * L.block + 32 * w) l k')
    (hσ : stateAt (code L) X (c * L.block + 32 * w + l) k = some (some d))
    (he : X.get (c * L.block + 32 * w + l, k) = some e)
    {j : Fin 44} {bi m : ℕ} (hsrc : loadSrc j = .state bi m) (hs : d.site = .matrixLoad j) :
    ∃ pc a row, e = ⟨pc, .rd a row⟩ ∧
      (loadSrc j).RowOk
        (blockInputs P mem0 c (ordinal X (c * L.block + 32 * w + l) k / 182)) w l row := by
  have hblk := hpre.block
  have hcomp : (c * L.block + 32 * w + l) % L.block < 128 := W.compute l hl
  have hdiv : (c * L.block + 32 * w + l) / L.block = c := by rw [hblk]; omega
  have hmod : (c * L.block + 32 * w + l) % L.block = 32 * w + l := by rw [hblk]; omega
  have hsS : c % P.sequences < P.sequences := Nat.mod_lt _ hpre.sequencesPos
  have hhH : c / P.sequences < P.heads := Nat.div_lt_of_lt_mul (hpre.grid ▸ hc)
  obtain ⟨hbi, hm, hload, -, hstore⟩ := acc_load j hsrc
  obtain ⟨js, hjs⟩ : ∃ js : Fin 18, js.val = 2 + 2 * m + bi :=
    ⟨⟨2 + 2 * m + bi, by omega⟩, rfl⟩
  rw [← hjs] at hstore
  have hsjs := storeOrd_spec js
  obtain ⟨a, bs, rfl, hsz, hloc⟩ := R.loadRow _ k d e j hcomp hσ hs he
  refine ⟨_, a, bs, rfl, ?_⟩
  rw [hsrc]
  show bs = (LoadSrc.state bi m).row _ w l
  -- the tile of the read is a tile of the sequence, and its count is one of the first 96
  have htc := hT _ k d hcomp hσ (Or.inl ⟨j, hs⟩)
  have hb : ordinal X (c * L.block + 32 * w + l) k / 182 <
      tiles (P.length (c % P.sequences)) := by
    have h := htc
    rwa [tileCount, seqOf, hdiv] at h
  have hn96 : ordinal X (c * L.block + 32 * w + l) k % 182 < 96 := by
    rcases hist k le_rfl d hσ with ⟨⟨pt, T⟩, hq, hat, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · have hpt : pt = .rd j := Pt.shape_inj hat.shape (show (Pt.rd j).Shape d.site from hs)
      subst hpt
      exact rd_count (Nat.mod_lt _ (by decide)) hq hsrc
    · omega
    · omega
    · omega
  have hloc0 := hloc
  rw [hload, hmod] at hloc
  have ho : 4096 * m + 256 * bi + bitsOff accWeights (32 * w + l) + 16 ≤ 32768 := by
    have := bitsOff_acc_le (32 * w + l)
    omega
  -- in a tile after the first, the lane wrote the row in the tile before
  have hprev : ∀ b', ordinal X (c * L.block + 32 * w + l) k / 182 = b' + 1 →
      ∃ k1, k1 + 1 < k ∧ ordinal X (c * L.block + 32 * w + l) (k1 + 1) =
          182 * b' + storeOrd js + 1 ∧
        ∃ pc a' bs', X.get (c * L.block + 32 * w + l, k1 + 1) = some ⟨pc, .wr a' bs'⟩ ∧
          a'.size = 16 ∧ a'.loc = a.loc := by
    intro b' hb'
    obtain ⟨k1, hk1, hord, pc1, a1, bs1, he1, hsz1, hloc1⟩ :=
      store_write_before F R W hl hσ he js (fun row h => by rw [hs] at h; cases h)
        (N := 182 * b' + storeOrd js) (by omega) (by omega)
    rw [hstore, hmod] at hloc1
    exact ⟨k1, hk1, hord, pc1, a1, bs1, he1, hsz1, hloc1.trans hloc.symm⟩
  rcases B.acc _ k _ a bs _ hcomp he hloc hsz ho with
    ⟨k', hk', pc', a', bs', he', hloc', hsz', hbs, hlast⟩ | ⟨hnone, hbs⟩
  · -- the last write of the row: by the invariant it is the row write of a store
    have hNle : ordinal X (c * L.block + 32 * w + l) k' ≤
        ordinal X (c * L.block + 32 * w + l) k := ordinal_mono (le_of_lt hk')
    have hN0 : ordinal X (c * L.block + 32 * w + l) k' ≠ 0 :=
      fun h0 => hearly k' pc' a' bs' h0 he' hsz'
    obtain ⟨d', hσ'⟩ := event_state F.sound F.consistent F.tracked he'
      (fun pc f h => by cases h)
    obtain ⟨j', b', hord, hrow, -, hloc2⟩ := write_of_inv F R E W hsc hl hσ' he'
      (hist k' (le_of_lt hk') d' hσ') hN0 (lt_of_le_of_lt (Nat.div_le_div_right hNle) htc)
    have hsj' := storeOrd_spec j'
    -- it writes at the offset of the load, so it is the store of the same blocks
    have hsrc' : storeSrc j' = .state bi m := by
      have h := hloc2.symm.trans (hloc'.trans hloc0)
      injection h with _ _ h3
      exact acc_store_unique hsrc (Nat.add_left_cancel h3)
    -- a tile has no store before its loads of `state_acc`: the write is in an earlier tile
    obtain ⟨bp, hbp⟩ : ∃ bp, ordinal X (c * L.block + 32 * w + l) k / 182 = bp + 1 :=
      ⟨ordinal X (c * L.block + 32 * w + l) k / 182 - 1, by omega⟩
    -- and no earlier than the row write of the tile before, which is a write of the row
    obtain ⟨k1, hk1, hord1, pc1, a1, bs1, he1, hsz1, hloc1⟩ := hprev bp hbp
    have hbb : b' = bp := by
      rcases Nat.lt_or_ge k' (k1 + 1) with hlt | hge
      · exact absurd hloc1 (hlast (k1 + 1) hlt hk1 pc1 a1 bs1 he1 hsz1)
      · have := ordinal_mono (X := X) (g := c * L.block + 32 * w + l) hge
        omega
    subst hbb
    rw [hbs, hrow, reduceOption_all (StoreSrc.row_all _ _ _ _), hsrc', hbp]
    exact acc_chain_row (x := blockInputs P mem0 c b') (x' := blockInputs P mem0 c (b' + 1))
      (tileInputs_chain hpre hsS hhH b' (by omega)) hw hl hbi hm
  · rcases Nat.eq_zero_or_pos (ordinal X (c * L.block + 32 * w + l) k / 182) with hb0 | hbpos
    · -- the first tile: the bytes the conversion loop left
      rw [hbs, hb0, seqOf, headOf, hdiv]
      exact acc_init_row P mem0 _ _ hw hl hbi hm
    · -- a later tile: the row write of the tile before is a write of the row
      exfalso
      obtain ⟨k1, hk1, -, pc1, a1, bs1, he1, hsz1, hloc1⟩ :=
        hprev (ordinal X (c * L.block + 32 * w + l) k / 182 - 1) (by omega)
      exact hnone (k1 + 1) hk1 pc1 a1 bs1 he1 hsz1 hloc1

end

end PTX.Kernels.FlashKdaFwd.Proof.Values
