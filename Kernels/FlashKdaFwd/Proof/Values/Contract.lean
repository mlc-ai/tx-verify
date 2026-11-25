-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Gen.Sites
public import Kernels.FlashKdaFwd.Proof.Thread.Entry
public import Kernels.FlashKdaFwd.Proof.Protocol.Layout
public import Lemmas.Kernel.Frame

@[expose] public section

/-!
# What the value induction takes from the other layers

The value induction (`Proof/Values/`) shows that the data registers of the compute lanes hold
the real numbers of the recurrence. It rests on three layers that are proved elsewhere; this
file states, as one structure each, exactly what it uses from them.

* `Followed`: the thread layer (`Proof/Thread/`). Every thread is followed by the generated
  machine `Thread.code`, which is sound.
* `ComputeRef`: the reference layer of the Compute phase (`Proof/Ref/Compute`, to be written):
  where a compute lane is, and the footprints of its memory events in closed form. Positions in
  the tile loop are indexed by **the number of warp matrix events the lane has made**
  (`WarpMatrix.ordinal X g k`, the count before position `k` of its trace): with `N` such events
  the lane is in tile `N / 182` and the next matrix instruction it reaches has ordinal
  `N % 182` in the tile. This is the index of a warp's matrix instance and the index of
  `SafetyFacts.matrixShape` and `matrixCount`.
* `ReadBack`: the protocol layer (`Proof/Protocol`): for each class of memory read of a compute
  lane in the tile loop, the bytes the read returns, as the bytes of the write that supplied
  them. The bytes of the input stage are given as a function of the launch memory
  (`stageByte`: what the tile's tensor loads wrote); the bytes of a row of `state_acc` as those
  of the lane's own last write of that row, or of the conversion loop before any such write
  (`accInitByte`). The tile of a read of the input stage is tied to the read by the lane's
  successful polls of the stage's "full" mbarrier (`Flow.okPolls` of `Protocol.Bar.loadFull`):
  the same addresses are also read before the tile loop (the FP32 state buffer shares them), so
  the matrix ordinal alone does not identify the tile's loads. `ComputeRef.polled` gives that
  number of polls at the reads of the tile loop.

Words: a *compute lane* is a thread with index below 128 in its thread block; `g / L.block` is
its block, `g % L.block` its index in the block (`tid`). The *input stage* of tile `b` is the
18048-byte buffer at window offset `32768 + 18048 * (b % 3)`; `state_acc` is window bytes 0 to
32767. The address forms (`Gen.loadForms`, …) come from the register table
(`Gen/Tables/matrix_table.json`), which `Gen/matrix_table.py` checked for all 128 threads.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values
open PTX PTX.Flow PTX.Frame PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Recurrence (tiles firstToken)

noncomputable section

/-! ## The generated tables, as functions -/

/-- The site of the matrix event of ordinal `n` of a tile. -/
def ordSite (n : ℕ) : MSite := Gen.ordSites.getD n (.load 0)

/-- What the `j`-th `ldmatrix` of a tile reads. -/
def loadSrc (j : ℕ) : LoadSrc := Gen.loadSrcs.getD j (.values 0)

/-- The table of the data registers live at the matrix instruction of ordinal `n` (empty for
the ordinals not generated yet: no claim). -/
def tableAt (n : ℕ) : Table := Gen.tables.getD n []

/-- The part of an address that depends on the thread: the sum of the weights of the set bits
of its index in the block. -/
def bitsOff (ws : List ℕ) (tid : ℕ) : ℕ := (ws.zipIdx.map fun p => p.1 * (tid / 2 ^ p.2 % 2)).sum

/-- The offset from `shared_mem` of the row the `j`-th `ldmatrix` reads, in tile `b`, for the
thread of index `tid` in its block. -/
def loadOff (j b tid : ℕ) : ℕ :=
  match Gen.loadForms[j]? with
  | some (c, s, ws) => c + s * (b % 3) + bitsOff ws tid
  | none => 0

/-- The offset from `shared_mem` of the row the `j`-th `stmatrix` writes, in tile `b`. -/
def storeOff (j b tid : ℕ) : ℕ :=
  match Gen.storeForms[j]? with
  | some (c, s, ws) => c + s * (b % 2) + bitsOff ws tid
  | none => 0

/-- The sequence that the thread block of `g` works on. -/
def seqOf (P : Params) (L : Launch) (g : ℕ) : ℕ := g / L.block % P.sequences

/-- The head that the thread block of `g` works on. -/
def headOf (P : Params) (L : Launch) (g : ℕ) : ℕ := g / L.block / P.sequences

/-- The number of tiles of the sequence of the thread block of `g`: the trip count of the tile
loop (`Top.tilesOf`). -/
def tileCount (P : Params) (L : Launch) (g : ℕ) : ℕ := tiles (P.length (seqOf P L g))

/-- The position of the first gate logit of a tile in the 32-element `beta` buffer: the global
index of the tile's first token in the `[H, T]` array, modulo 8 (it does not depend on the
tile, whose first token is a multiple of 16 after the sequence's). -/
def gateOff (P : Params) (L : Launch) (g : ℕ) : ℕ :=
  (P.total * headOf P L g + firstToken P.length (seqOf P L g)) % 8

/-- The "full" mbarrier of the input stage of tile `b` in the thread block of `g`: the load
leader completes it with the tile's 70 tensor loads, the compute lanes poll it. -/
abbrev fullBar (L : Launch) (g b : ℕ) : Loc :=
  (Protocol.Bar.loadFull ⟨b % 3, Nat.mod_lt _ (by decide)⟩).loc L (g / L.block)

/-! ## The thread layer -/

/-- **From the thread layer**: the launch has thread blocks of whole warps, the execution is
consistent, every thread's machine is sound and follows its thread. -/
structure Followed (L : Launch) (mem0 : Mem0) (X : Execution) : Prop where
  block : L.block % 32 = 0
  consistent : Consistent L kernel Assumptions.all mem0 X
  sound : ∀ g < L.threads, (code L g).Sound
  tracked : Tracked (code L) X

/-! ## The reference layer of the Compute phase -/

/-- **From the reference layer of the Compute phase.** All fields are about one compute lane
`g` (`g % L.block < 128`) and the state `d` of its machine before position `k` of its trace
(`stateAt (code L) X g k = some (some d)`). -/
structure ComputeRef (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- **Where a lane makes a matrix event.** Before its `N`-th matrix event (counting from 0)
  the machine is at the matrix site of ordinal `N % 182`: the tile loop runs the 182 matrix
  instructions in code order (the machine form of `SafetyFacts.matrixShape`). -/
  site : ∀ g k N d, g % L.block < 128 → X.MatrixK (g, k) N →
    stateAt (code L) X g k = some (some d) → (ordSite (N % 182)).At d.site
  /-- **How many matrix events a lane makes** (`SafetyFacts.matrixCount`): at most 182 per tile
  of its sequence, and exactly that many when it exits. So no lane of a warp exits while
  another is still at a matrix instruction. -/
  count : ∀ g, g % L.block < 128 → (X.tr g).countP isMatrix ≤ 182 * tileCount P L g ∧
    ∀ j pc, X.get (g, j) = some ⟨pc, .exit⟩ → (X.tr g).countP isMatrix = 182 * tileCount P L g
  /-- **The cleared accumulator.** At every `mma.sync` the word register `%r862` (id 1168),
  written once per tile by `mov.b32 %r862, 0`, holds zero. It is the C operand of 44 of the
  104 multiply-accumulates. -/
  zero : ∀ g k d (j : Fin 104), g % L.block < 128 → stateAt (code L) X g k = some (some d) →
    d.site = .warpMma j → d.w 1168 = Arith32.i32 0
  /-- **The tile of a read.** At each read of the input stage in the tile loop (the first
  event of an `ldmatrix`, and the scalar loads of `Gen.scalarForms`), the lane has polled the
  "full" mbarrier of its tile's stage successfully `b / 3 + 1` times, `b` its tile: it has
  polled for tile `b` and has not released the stage. This is what ties the read to the loads
  of tile `b` in `ReadBack.stage`. -/
  polled : ∀ g k d e, g % L.block < 128 → stateAt (code L) X g k = some (some d) →
    X.get (g, k) = some e →
    ((∃ j : Fin 44, d.site = .matrixLoad j) ∨
      ∃ sz c ck ws, (d.site.pc, sz, c, ck, ws) ∈ Gen.scalarForms) →
    okPolls (fullBar L g (ordinal X g k / 182)) ((X.tr g).take k) = ordinal X g k / 182 / 3 + 1
  /-- **The row read of an `ldmatrix`.** At the first event of the `j`-th `ldmatrix` the lane
  reads the 16 bytes of its row, at the offset `loadOff` of its block's shared window; the tile
  is the number of matrix events it has made, divided by 182. (That the event is a read and not
  undefined behaviour is the address being in the window and a multiple of 16.) -/
  loadRow : ∀ g k d e (j : Fin 44), g % L.block < 128 →
    stateAt (code L) X g k = some (some d) → d.site = .matrixLoad j → X.get (g, k) = some e →
    ∃ a bs, e = ⟨d.site.pc, .rd a bs⟩ ∧ a.size = 16 ∧
      a.loc = ⟨.shared, g / L.block,
        P.sharedBase + loadOff j (ordinal X g k / 182) (g % L.block)⟩
  /-- **The row write of an `stmatrix`.** At the second event of the `j`-th `stmatrix` the lane
  writes the 16 bytes it received (`row`) to its row, at the offset `storeOff`. -/
  storeRow : ∀ g k d e (j : Fin 18) row, g % L.block < 128 →
    stateAt (code L) X g k = some (some d) → d.site = .matrixStoreWr j row →
    X.get (g, k) = some e →
    ∃ a, e = ⟨d.site.pc, .wr a row.reduceOption⟩ ∧ a.size = 16 ∧
      a.loc = ⟨.shared, g / L.block,
        P.sharedBase + storeOff j (ordinal X g k / 182) (g % L.block)⟩
  /-- **The scalar loads of the tile loop** (the two gate logits and the sixteen entries of
  `g_total`, listed in `Gen.scalarForms` by instruction position): a read of `sz` bytes of the
  input stage of the tile, at the listed offset. -/
  scalarLoad : ∀ g k d e pc sz c ck ws, g % L.block < 128 →
    stateAt (code L) X g k = some (some d) → (pc, sz, c, ck, ws) ∈ Gen.scalarForms →
    d.site.pc = pc → X.get (g, k) = some e →
    ∃ a bs, e = ⟨pc, .rd a bs⟩ ∧ a.size = sz ∧
      a.loc = ⟨.shared, g / L.block, P.sharedBase +
        (c + 18048 * (ordinal X g k / 182 % 3) + ck * gateOff P L g + bitsOff ws (g % L.block))⟩

/-! ## The protocol layer: what a read returns -/

/-- **The byte at offset `o` of the input stage of tile `b`** of sequence `s` and head `h`, as
the 70 tensor loads of the tile leave it: the launch byte of the global array element that the
load's box puts there (a box of 8 features by 16 rows is one 256-byte piece, row-major), or the
byte of the bfloat16 payload zero where the box of `v` or `beta` is past the end of its array.
The layout of a stage: `v` at 0, `beta` at 4096 (64 bytes, then 64 bytes of padding that no
load writes), `k_decayed` at 4224, `q_decayed` at 8320, `k_restored` at 12416, `g_total` at
16512, `INV` at 17024, `Mqk` at 17536. -/
def stageByte (P : Params) (mem0 : Mem0) (s h b o : ℕ) : Option Byte :=
  let slot := P.slot s h b
  let tok := firstToken P.length s + 16 * b
  if o < 4096 then
    -- `v[T, H, 128]`: piece `o / 256` holds the channels `8 (o / 256) ..`, row `o % 256 / 16`
    if tok + o % 256 / 16 < P.total then
      (mem0 ⟨.global, 0, P.valuesBase + 256 * ((tok + o % 256 / 16) * P.heads + h) +
        16 * (o / 256) + o % 16⟩).join
    else some ((Value.float .bf16 0).byteAt (o % 2))
  else if o < 4160 then
    -- `beta[H * T]`: 32 elements from the index of the tile's first token rounded down to 8
    let i := 8 * ((h * P.total + tok) / 8) + (o - 4096) / 2
    if i < P.heads * P.total then (mem0 ⟨.global, 0, P.logitsBase + 2 * i + o % 2⟩).join
    else some ((Value.float .bf16 0).byteAt (o % 2))
  else if o < 4224 then none
  else if o < 16512 then
    -- `k_decayed`, `q_decayed`, `k_restored`: array `(o - 4224) / 4096`
    let q := (o - 4224) % 4096
    (mem0 ⟨.global, 0, P.array (4096 * ((o - 4224) / 4096)) + 4096 * slot +
      256 * (q % 256 / 16) + 16 * (q / 256) + q % 16⟩).join
  else if o < 17024 then
    (mem0 ⟨.global, 0, P.array 12288 + 512 * slot + (o - 16512)⟩).join
  else if o < 18048 then
    -- `INV`, `Mqk`: array `(o - 17024) / 512`
    let q := (o - 17024) % 512
    (mem0 ⟨.global, 0, P.array (12800 + 512 * ((o - 17024) / 512)) + 512 * slot +
      32 * (q % 256 / 16) + 16 * (q / 256) + q % 16⟩).join
  else none

/-- **The byte at offset `o` of `state_acc` after the conversion loop**: the bfloat16 payload of
the initial state. The element of value channel `n` and key feature `k` is at the element index
`64 (n / 8) + 1024 (k / 8) + 8 (n % 8) + k % 8`. -/
def accInitByte (P : Params) (s h o : ℕ) : Option Byte :=
  let e := o / 2
  if hn : 8 * (e / 64 % 16) + e / 8 % 8 < 128 ∧ 8 * (e / 1024) + e % 8 < 128 then
    some ((Value.float .bf16 (P.initial s h ⟨_, hn.1⟩ ⟨_, hn.2⟩)).byteAt (o % 2))
  else none

/-- **From the protocol layer**: what the memory reads of a compute lane in the tile loop
return. Both fields are about a read event `⟨pc, .rd a bs⟩` at position `k` of the trace of a
compute lane `g`. -/
structure ReadBack (P : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop where
  /-- **A read of the input stage of tile `b`** returns the bytes the tile's tensor loads wrote
  (`stageByte`), when the lane has polled the stage's "full" mbarrier successfully `b / 3 + 1`
  times before the read: it has polled for tile `b`, which observed exactly the loads of that
  tile, and has not yet released the stage, so no later load of these bytes precedes the read.
  The read may be anywhere in the stage but in the 64 bytes at offsets 4160 to 4223, which no
  load of a tile writes. This covers the row reads of `k_decayed`, `q_decayed`, `k_restored`,
  `INV`, `Mqk` and `v`, and the scalar loads of `beta` and `g_total`. -/
  stage : ∀ g k pc a bs b o, g < L.threads → g % L.block < 128 →
    X.get (g, k) = some ⟨pc, .rd a bs⟩ →
    okPolls (fullBar L g b) ((X.tr g).take k) = b / 3 + 1 →
    a.loc = ⟨.shared, g / L.block, P.sharedBase + (32768 + 18048 * (b % 3) + o)⟩ →
    (o + a.size ≤ 4160 ∨ (4224 ≤ o ∧ o + a.size ≤ 18048)) →
    bs = (List.range a.size).map fun i =>
      stageByte P mem0 (seqOf P L g) (headOf P L g) b (o + i)
  /-- **A read of a row of `state_acc`** returns the 16 bytes of the lane's own last 16-byte
  write of that row (its transposing `stmatrix` of the tile before: the rows of the 128 lanes
  are disjoint, so no other thread writes it in the tile loop), or, when the lane has made no
  16-byte write of the row yet (the first tile), the bytes the conversion loop left there. The
  writes are qualified by their size because a lane's own 2-byte store of the conversion loop
  can be at the address of a row it reads in the first tile. -/
  acc : ∀ g k pc a bs o, g % L.block < 128 → X.get (g, k) = some ⟨pc, .rd a bs⟩ →
    a.loc = ⟨.shared, g / L.block, P.sharedBase + o⟩ → a.size = 16 → o + 16 ≤ 32768 →
    (∃ k' < k, ∃ pc' a' bs', X.get (g, k') = some ⟨pc', .wr a' bs'⟩ ∧ a'.loc = a.loc ∧
        a'.size = 16 ∧ bs = bs'.map some ∧
        ∀ k'', k' < k'' → k'' < k → ∀ pc'' a'' bs'',
          X.get (g, k'') = some ⟨pc'', .wr a'' bs''⟩ → a''.size = 16 → a''.loc ≠ a.loc) ∨
      ((∀ k' < k, ∀ pc' a' bs', X.get (g, k') = some ⟨pc', .wr a' bs'⟩ → a'.size = 16 →
          a'.loc ≠ a.loc) ∧
        bs = (List.range 16).map fun i => accInitByte P (seqOf P L g) (headOf P L g) (o + i))

end

end PTX.Kernels.FlashKdaFwd.Proof.Values
