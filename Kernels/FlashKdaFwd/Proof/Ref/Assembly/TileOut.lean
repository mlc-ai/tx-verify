-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.TileOutMma
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.ExportsValues
public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Contract
public import Kernels.FlashKdaFwd.Proof.Values.TileAlgebra
public import Kernels.FlashKdaFwd.Proof.Protocol.ResultGlue

@[expose] public section

/-!
# The outputs of a tile, from the claim of the tile induction

The field `stage` of `Protocol.OutContent P L X O` (`Proof/Protocol/ResultGlue.lean`) says:
for a byte of a live row of the output buffer of tile `b` (offset `off < 4096` of output
buffer `b % 2` of the thread block of sequence `s` and head `h`; the row `off % 256 / 16` is a
token of the sequence), the last write event of a compute thread `ga` that covers the byte and
has `b / 2` arrivals on the "full" mbarrier of that buffer before it carries the byte
`outStage P s h b off`: the byte `off % 2` of the bfloat16 payload of the specified output of
token `16 * b + off % 256 / 16` and value channel `8 * (off / 256) + off % 16 / 2`.

`outContent_stage` proves the field, for any `O`, from the precondition, consistency and the
conclusion `Values.TileClaim` of the tile value induction. It is in fact proved for EVERY write
event of a compute thread with these two properties (the hypotheses "it is the last one" and
"the thread is the owner `O.out` names" are not used).

Words. A *compute thread* is a thread whose index in its thread block (`tid`) is below 128; it
is lane `tid % 32` of the compute warp `tid / 32` of its block. A *tile* is 16 consecutive
tokens of the block's sequence. A *followed state* of a thread at position `k` is the state of
its machine before its event `k` (`Frame.stateAt (code L) X g k = some (some d)`). The
*ordinal* `WarpMatrix.ordinal X g k` is the number of warp matrix events among the first `k`
events of the thread; a tile has 182 of them. An `stmatrix` instruction is two events of a
lane: its warp matrix event, in which the lane receives 16 bytes (a *row*), and the *row write*
of these bytes to shared memory (the machine's site `matrixStoreWr j row` for the `j`-th
`stmatrix` of the tile, which holds the row).

The proof has two halves.

* **Where the write is** (`TileOut.out_write`, reference layer). The write event fires from a
  followed state in a stage of the chain of the phases (`event_stage`). A write is fired only
  at a store instruction or at the row write of an `stmatrix` (`Ref/Kinds: wr_site`), and the
  instruction decides the phase:
  - a store of the conversion loop writes two bytes of the bfloat16 state copy, the first 32768
    bytes of the window (`Conversion.access_conversion`): it covers no byte of an output buffer;
  - an element store of a partial tile is at an instruction of the store warp, not of a compute
    thread;
  - a store of the final state is in the epilogue, where the thread has arrived on the "full"
    mbarrier of buffer `b % 2` once for every tile that uses the buffer (the exit ledger of the
    Compute phase and `Epilogue.arrivals_in`): more than `b / 2` times, since tile `b` is one of
    them (`Protocol.div_lt_uses`);
  - the row write of the `j`-th `stmatrix` of a tile `t` is at the offset `Values.storeOff`
    (`Compute.Vals.storeRow_compute`): inside the bfloat16 state copy for `j ≥ 2`, and for
    `j < 2` at offset `86912 + 4096 * (t % 2) + 512 * j + 1024 * (tid / 32) + 16 * (tid % 32)`,
    with `t / 2` arrivals on the "full" mbarrier of buffer `t % 2` before it (the ledger of the
    Compute phase). So `t % 2 = b % 2` and `t / 2 = b / 2`: the tile is `b`, and the thread has
    made `182 * b + 125 + j` matrix events.
* **What it writes** (value layer). Inside a tile the state satisfies the invariant of the
  induction at one of the program points of its count (`TileClaim.inside`). At the site
  `matrixStoreWr j row` that point is the row write of the `j`-th `stmatrix`, which says that
  `row` is the row of the store's source for the real arrays of the tile (`TileOut.row_of`):
  for `j < 2` the bfloat16 payloads of the outputs of token row `lane % 16` and of the eight
  value channels `16 * (2 * warp + j) + 8 * (lane / 16) + i` (`TileOut.row_byte`). The arrays of
  the tile compute the specified outputs in the live rows (`Values.tileInputs_output`).

The layout facts used are closed checks on the generated tables (`TileOut.storeOff_table`,
`stWr_table`, `store_site_pc`), by evaluation in the kernel.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX.Kernels.FlashKdaFwd.Protocol (Bar uses Owners OutLast outByte outStage blockOf stageOf
  computeThread)
open PTX.Kernels.FlashKdaFwd.Math.Fragments (Inputs halfBase)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace TileOut

/-! ### Closed checks on the tables -/

/-- **The store sites by family**: the ten stores of the conversion loop are at instructions
388 to 620, the eight element stores of a partial tile at 2945 to 3112 (the store warp's loop),
the 128 stores of the final state after 3113 (the epilogue). -/
theorem store_site_pc : ∀ j : Fin 146,
    (387 < (Site.store j).pc ∧ (Site.store j).pc ≤ 620) ∨
    (2944 < (Site.store j).pc ∧ (Site.store j).pc ≤ 3112) ∨ 3113 < (Site.store j).pc := by
  decide +kernel

/-- The row writes of the `stmatrix` instructions are at instructions of the compute loop. -/
theorem stWr_site_pc (j : Fin 18) (row : List (Option Byte)) :
    2105 < (Site.matrixStoreWr j row).pc ∧ (Site.matrixStoreWr j row).pc ≤ 2944 := by
  have h : ∀ j : Fin 18,
      2105 < (Site.matrixStoreWr j []).pc ∧ (Site.matrixStoreWr j []).pc ≤ 2944 := by
    decide +kernel
  exact h j

/-- **The position of a row write in its tile** (`Compute.skTab`: the 268 positions of a tile)
is before the tile's two arrivals, and for the first two `stmatrix` (the outputs) the lane has
made some but not all of the tile's 182 matrix events there. -/
theorem stWr_table : ∀ j : Fin 18, Compute.skTab.idxOf (.stWr j) < 264 ∧
    (j.val < 2 → 0 < Compute.matOf (Compute.skTab.idxOf (.stWr j)) ∧
      Compute.matOf (Compute.skTab.idxOf (.stWr j)) < 182) := by
  decide +kernel

/-- **Where the `j`-th `stmatrix` writes its row** (`Values.storeOff`, an offset in the block's
window), for the output buffer `p` and the thread of index `x` in its block: the first two
write a row of the output buffer, at `512 * j + 1024 * (x / 32) + 16 * (x % 32)` in it; the
sixteen others write a row of the bfloat16 state copy (the first 32768 bytes). -/
theorem storeOff_table : ∀ j : Fin 18, ∀ p < 2, ∀ x < 128,
    (j.val < 2 ∧ Values.storeOff j p x =
      86912 + 4096 * p + 512 * j.val + 1024 * (x / 32) + 16 * (x % 32)) ∨
    (2 ≤ j.val ∧ Values.storeOff j p x + 16 ≤ 32768) := by
  decide +kernel

/-- The offset of a row write depends on the tile only through its output buffer. -/
theorem storeOff_mod (j b x : ℕ) : Values.storeOff j b x = Values.storeOff j (b % 2) x := by
  unfold Values.storeOff
  rw [Nat.mod_mod]

/-- The first two `stmatrix` of a tile write its outputs: value blocks 0 and 1 of the warp. -/
theorem storeSrc_out : ∀ j : Fin 18, j.val < 2 → Values.storeSrc j = .out j.val := by decide

/-! ### Counts -/

/-- **The arrivals on the "full" mbarrier of the output buffer of tile `b`**, read off a ledger
of the Compute phase whose arrival count is that of `n` tiles: one per tile below `n` that uses
the buffer. -/
theorem af_stage {c n b a1 a2 a3 a5 a6 : ℕ} {es : List Event}
    (h : Compute.ledOf L c es = Compute.ledAt a1 a2 a3 n a5 a6) :
    arrivals ((Bar.storeFull (stageOf b)).loc L c) es = uses 2 n (b % 2) := by
  rcases Nat.mod_two_eq_zero_or_one b with h0 | h1
  · have hst : stageOf b = (0 : Fin 2) := Fin.ext h0
    rw [hst, h0]
    exact congrArg Compute.Led.af0 h
  · have hst : stageOf b = (1 : Fin 2) := Fin.ext h1
    rw [hst, h1]
    exact congrArg Compute.Led.af1 h

/-- Tile `t` is use number `t / 2` of its output buffer. -/
theorem uses_own (t : ℕ) : uses 2 t (t % 2) = t / 2 := by
  unfold uses
  omega

/-! ### Where the write is -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- **A write of a compute thread that covers a byte of the output buffer of tile `b`, with
`b / 2` arrivals on the buffer's "full" mbarrier before it, is the row write of one of the two
output `stmatrix` of tile `b`.** The thread's machine is at the site `matrixStoreWr j row` with
`j < 2`; the bytes written are the row the site holds; the thread has made the matrix events of
`b` tiles and some, not all, of tile `b`; the 16 bytes go to offset
`512 * j + 1024 * (tid / 32) + 16 * (tid % 32)` of the buffer. -/
theorem out_write {g k pc b off : ℕ} {a : Acc} {bs : List Byte} (hc : tid g < 128)
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hoff : off < 4096)
    (hcov : a.Covers (outByte L (g / L.block) (b % 2) off)) (hb : b < Compute.tilesOf P g)
    (harr : arrivals ((Bar.storeFull (stageOf b)).loc L (g / L.block)) ((X.tr g).take k) =
      b / 2) :
    ∃ (d : D) (j : Fin 18) (row : List (Option Byte)),
      Frame.stateAt (code L) X g k = some (some d) ∧ d.site = .matrixStoreWr j row ∧
      j.val < 2 ∧ bs = row.reduceOption ∧ WarpMatrix.ordinal X g k / 182 = b ∧
      WarpMatrix.ordinal X g k % 182 ≠ 0 ∧ a.size = 16 ∧
      a.loc.addr = L.sharedBase +
        (86912 + 4096 * (b % 2) + 512 * j.val + 1024 * (tid g / 32) + 16 * (tid g % 32)) := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hS := hpre.sharedBase
  obtain ⟨d, hσ, hst, -⟩ := event_stage hpre hX he (fun f h => by cases h)
  obtain ⟨-, -, c3, c4⟩ := hcov
  simp only [outByte] at c3 c4
  rcases wr_site (sounds hpre) hX he hσ rfl with ⟨j, hs⟩ | ⟨j, row, hs⟩
  · rcases store_site_pc j with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
    · -- a store of the conversion loop: two bytes of the bfloat16 state copy
      rw [← hs] at h1 h2
      obtain ⟨j0, s0, -, -, hI⟩ := hst.of_pc_conversion (by omega) (by omega)
      obtain ⟨-, hw⟩ := Conversion.access_conversion hpre hX hg hσ hI (a := a) (w := true)
        (.inr (.inl ⟨bs, ⟨pc, he⟩, rfl⟩))
      rcases hw with ⟨hw, -⟩ | ⟨-, el, hel, -, rfl⟩
      · cases hw
      · have hfr := Conversion.wrAddr_frame hpre hel
        simp only at c3 c4
        omega
    · -- an element store of a partial tile: an instruction of the store warp
      rw [← hs] at h1 h2
      obtain ⟨hr, -⟩ := hst.of_pc_store h1 h2
      unfold warp at hr
      unfold tid at hc
      omega
    · -- a store of the final state: all arrivals of the tile loop are made
      rw [← hs] at h1
      obtain ⟨j0, s0, past, hj0, -, -⟩ := hst.of_pc_epilogue (by omega) (.inr h1)
      have hE : Epilogue.Entered P L X g j0 := ⟨s0, past.state, past.into⟩
      have hlt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
      have hkeep := Epilogue.arrivals_in hpre hX hg hE hj0 hlt
        ((Bar.storeFull (stageOf b)).loc L (g / L.block))
      have huse := Protocol.div_lt_uses (n := 2) (by omega) hb
      obtain ⟨j1, s1, -, -, hcase⟩ := past.entry
      rcases hcase with ⟨-, -, hout, -⟩ | ⟨hr, -⟩ | ⟨hr, -⟩
      · have hex := af_stage (b := b) hout.2.1
        omega
      · unfold warp at hr
        unfold tid at hc
        omega
      · unfold warp at hr
        unfold tid at hc
        omega
  · -- the row write of an `stmatrix`
    obtain ⟨h1, h2⟩ := stWr_site_pc j row
    rw [← hs] at h1 h2
    obtain ⟨-, j0, s0, -, -, -, hI⟩ := hst.of_pc_compute h1 h2
    obtain ⟨a', hev, hsz, hloc⟩ := Compute.Vals.storeRow_compute hpre hX he hσ hI hs
    obtain ⟨-, hkd⟩ := Event.mk.inj hev
    obtain ⟨rfl, rfl⟩ := Kind.wr.inj hkd
    obtain ⟨t, n, hn, ht, -, hR, hled, -⟩ := Compute.Vals.tile_of hI (by rw [hs]; nofun)
    have hmat := Compute.Vals.mats_tile hled
    have hsk : Compute.skOf n = .stWr j := Compute.Vals.skOf_of_at hR.site (by rw [hs]; rfl)
    have hidx : Compute.skTab.idxOf (.stWr j) = n := by
      rw [← hsk]
      exact Compute.pos_idx n hn
    obtain ⟨hn264, hmatj⟩ := stWr_table j
    rw [hidx] at hn264 hmatj
    have hind : Compute.ind 267 n = 0 := by
      unfold Compute.ind
      split <;> omega
    have haf := af_stage (b := b) (n := t + Compute.ind 267 n) hled
    rw [hind, Nat.add_zero] at haf
    have haddr : a.loc.addr = P.sharedBase +
        Values.storeOff j (WarpMatrix.ordinal X g k / 182 % 2) (tid g) := by
      rw [hloc, ← storeOff_mod, block_mod hpre]
    rcases storeOff_table j (WarpMatrix.ordinal X g k / 182 % 2) (Nat.mod_lt _ (by omega))
      (tid g) hc with ⟨hj, hoffj⟩ | ⟨hj, hoffj⟩
    · obtain ⟨hm0, hm182⟩ := hmatj hj
      have htile : WarpMatrix.ordinal X g k / 182 = t := by omega
      rw [htile] at hoffj haddr
      have hpar : t % 2 = b % 2 := by omega
      rw [← hpar, uses_own] at haf
      have htb : t = b := by omega
      subst htb
      exact ⟨d, j, row, hσ, hs, hj, rfl, htile, by omega, hsz, by omega⟩
    · omega

end

/-! ### What it writes -/

/-- **The row a lane holds at the row write of an `stmatrix`**, from the invariant of the tile
induction: a state at the site `matrixStoreWr j row` that is at a program point of its count
holds the row of the store's source for the arrays of the tile. -/
theorem row_of {x : Inputs} {w l n : ℕ} {d : D} {j : Fin 18} {row : List (Option Byte)}
    (h : Values.SiteOk x w l n d) (hs : d.site = .matrixStoreWr j row) :
    row = (Values.storeSrc j).row x w l := by
  obtain ⟨q, -, hat, -⟩ := h
  have hq : q.1 = .wr j := Values.Pt.shape_inj hat.shape (show (Values.Pt.wr j).Shape d.site from
    ⟨row, hs⟩)
  rw [hq] at hat
  obtain ⟨row', hs', hrow⟩ := hat
  rw [hs] at hs'
  obtain ⟨-, rfl⟩ := Site.matrixStoreWr.inj hs'
  exact hrow

/-- A list of known bytes, with the unknown ones dropped, is the list of the bytes. -/
theorem reduceOption_some {α : Type} (f : ℕ → α) (n : ℕ) :
    ((List.range n).map fun k => some (f k)).reduceOption = (List.range n).map f := by
  simp [List.reduceOption, List.filterMap_map]

/-- The sixteen bytes of the row of lane `l` of four 8 × 8 matrices of bfloat16 payloads: byte
`k` is byte `k % 2` of the payload of element `k / 2` of row `l % 8` of matrix `l / 8`. -/
theorem matRows_bf16 (M : ℕ → ℕ → ℕ → ℝ) (l : ℕ) :
    WarpMatrix.matRows WarpMatrix.bf16Enc M l =
      fun k => some ((Value.float .bf16 (M (l / 8) (l % 8) (k / 2))).byteAt (k % 2)) := rfl

/-- **Byte `i` of the row that lane `l` of warp `w` writes in the output `stmatrix` of value
block `bi`**: byte `i % 2` of the bfloat16 payload of the output of token row `l % 16` and
value channel `16 * (2 * w + bi) + 8 * (l / 16) + i / 2` (column `i / 2` of the half
`halfBase w bi (l / 16)`). -/
theorem row_byte (x : Inputs) (w l bi : ℕ) {i : ℕ} (hi : i < 16) :
    ((Values.StoreSrc.out bi).row x w l).reduceOption[i]? =
      some ((Value.float .bf16
        (Math.Fragments.output x (halfBase w bi (l / 16)) (l % 16) (i / 2))).byteAt (i % 2)) := by
  simp only [Values.StoreSrc.row, Values.StoreSrc.trans, Values.StoreSrc.frag,
    Values.StoreSrc.mat, WarpMatrix.rowPart, Bool.false_eq_true, ↓reduceIte]
  rw [matRows_bf16, reduceOption_some, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Math.Fragments.ofFrag_pairFrag _ _ _ (by omega : i / 2 < 8),
    show l / 8 / 2 = l / 16 by omega, show 8 * (l / 8 % 2) + l % 8 = l % 16 by omega]
  rfl

/-! ### The layout of an output buffer -/

/-- **The byte of a row write, by its offset in the buffer.** A 16-byte write at offset `K` of
an output buffer (the buffer starts at address `B`) that covers the byte at offset `off` covers
it with its byte `i = off - K`, and `i < 16`. -/
theorem offset_split {A B off K : ℕ} (hA : A = B + K) (h3 : A ≤ B + off)
    (h4 : B + off < A + 16) : ∃ i, i < 16 ∧ off = K + i ∧ B + off - A = i :=
  ⟨off - K, by omega, by omega, by omega⟩

/-- **Which output a byte of an output buffer holds.** Lane `l` of warp `w` writes the row of
value block `j` at offset `512 * j + 1024 * w + 16 * l`; its byte `i` is at offset `off`. Then
the token row `off % 256 / 16` of the buffer's layout is `l % 16`, the value channel
`8 * (off / 256) + off % 16 / 2` is column `i / 2` of the half that starts at channel
`halfBase w j (l / 16) = 16 * (2 * w + j) + 8 * (l / 16)`, and the byte of the payload is
`i % 2`. -/
theorem layout {j w l i off : ℕ} (hj : j < 2) (hw : w < 4) (hl : l < 32) (hi : i < 16)
    (h : off = 512 * j + 1024 * w + 16 * l + i) :
    halfBase w j (l / 16) = 8 * ((8 * (off / 256) + off % 16 / 2) % 128 / 8) ∧
      l % 16 = off % 256 / 16 ∧ i / 2 = (8 * (off / 256) + off % 16 / 2) % 128 % 8 ∧
      i % 2 = off % 2 := by
  subst h
  unfold halfBase
  refine ⟨by omega, by omega, by omega, by omega⟩

end TileOut

/-- **The field `stage` of `Protocol.OutContent`**, for any `O`, from the claim of the tile
induction: a write event of a compute thread `ga` of the block of sequence `s` and head `h`
that covers the byte at offset `off` of the output buffer of tile `b`, in a live row of the
tile, and has `b / 2` arrivals on the buffer's "full" mbarrier before it, has there the byte
`off % 2` of the bfloat16 payload of the specified output of token `16 * b + off % 256 / 16`
and value channel `8 * (off / 256) + off % 16 / 2`. (The premises that it is the thread's last
such write and that `O.out` names the thread are not needed.) -/
theorem outContent_stage (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (T : Values.TileClaim P L mem0 X) (O : Owners) :
    ∀ {s h : Nat}, s < P.sequences → h < P.heads → ∀ b off : Nat, off < 4096 →
    16 * b + off % 256 / 16 < P.length s →
    ∀ (ga : Fin 128) (iw : Nat) (aw : Acc) (bw : List Byte),
      O.out (outByte L (blockOf P s h) (stageOf b).val off) = ga.val →
      OutLast L X (blockOf P s h) (stageOf b) ga (b / 2)
        (outByte L (blockOf P s h) (stageOf b).val off) iw aw bw →
        wbyte aw bw (outByte L (blockOf P s h) (stageOf b).val off) = outStage P s h b off := by
  intro s h hs hh b off hoff hlive ga iw aw bw _ hlast
  obtain ⟨⟨pcw, hget⟩, hcov, hcnt, -⟩ := hlast
  have hblk := hpre.block
  have hga := ga.isLt
  have hgeq : computeThread L (blockOf P s h) ga =
      blockOf P s h * L.block + 32 * (ga.val / 32) + ga.val % 32 := by
    unfold computeThread Protocol.thr
    omega
  have hdiv : computeThread L (blockOf P s h) ga / L.block = blockOf P s h := by
    unfold computeThread Protocol.thr
    rw [hblk]
    omega
  have htid : tid (computeThread L (blockOf P s h) ga) = ga.val := by
    unfold computeThread Protocol.thr tid
    rw [hblk]
    omega
  have hseq : seqOf P (computeThread L (blockOf P s h) ga) = s := by
    unfold seqOf
    rw [← hblk, hdiv]
    exact Protocol.blockOf_mod hs
  have hb : b < Compute.tilesOf P (computeThread L (blockOf P s h) ga) := by
    unfold Compute.tilesOf
    rw [hseq]
    unfold Recurrence.tiles
    omega
  rw [← hdiv] at hcov
  have harr : arrivals ((Bar.storeFull (stageOf b)).loc L
      (computeThread L (blockOf P s h) ga / L.block))
      ((X.tr (computeThread L (blockOf P s h) ga)).take iw) = b / 2 := by
    rw [hdiv]
    exact hcnt
  obtain ⟨d, j, row, hσ, hsite, hj, hbw, hord, hne, hsz, haddr⟩ :=
    TileOut.out_write hpre hX (by rw [htid]; exact hga) hget hoff hcov hb harr
  rw [htid] at haddr
  rw [hgeq] at hσ hord hne
  have hok := T.inside (Protocol.blockOf_lt hpre hs hh) (by omega : ga.val / 32 < 4)
    (Nat.mod_lt _ (by omega)) hσ hne
  rw [hord] at hok
  have hrow := TileOut.row_of hok hsite
  rw [TileOut.storeSrc_out j hj] at hrow
  obtain ⟨-, -, c3, c4⟩ := hcov
  rw [hsz] at c4
  obtain ⟨i, hi, hoffeq, hidx⟩ := TileOut.offset_split
    (A := aw.loc.addr) (B := L.sharedBase + (86912 + 4096 * (b % 2))) (off := off)
    (K := 512 * j.val + 1024 * (ga.val / 32) + 16 * (ga.val % 32))
    (by rw [haddr]; omega) (by rw [Nat.add_assoc]; exact c3) (by rw [Nat.add_assoc]; exact c4)
  have hidx' : (outByte L (blockOf P s h) (stageOf b).val off).addr - aw.loc.addr = i := by
    rw [← hidx, Nat.add_assoc]
    rfl
  obtain ⟨e1, e2, e3, e4⟩ := TileOut.layout hj (by omega : ga.val / 32 < 4)
    (Nat.mod_lt _ (by omega : 0 < 32)) hi hoffeq
  have hout := Values.tileInputs_output (mem0 := mem0) hpre hs hh (b := b)
    (t := off % 256 / 16) (ch := (8 * (off / 256) + off % 16 / 2) % 128)
    (Nat.div_lt_of_lt_mul (Nat.mod_lt _ (by omega))) hlive (Nat.mod_lt _ (by decide))
  unfold wbyte outStage
  rw [hidx', hbw, hrow, TileOut.row_byte _ _ _ _ hi, ← hout]
  unfold Values.blockInputs Math.Fragments.outputs
  rw [Protocol.blockOf_mod hs, Protocol.blockOf_div hs, e1, e2, e3, e4]

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
