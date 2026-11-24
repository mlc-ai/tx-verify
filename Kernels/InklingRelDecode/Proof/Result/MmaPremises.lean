-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.All
public import Kernels.InklingRelDecode.Proof.Result.MmaLayout
public import Kernels.InklingRelDecode.Proof2.Lib.KvBox

@[expose] public section

/-!
# The premises of the MMA data path

Everything the data path of the MMAs needs from the layers below it, as three structures over an
execution `X`. Each field is a statement about abstract states (`Interface.St`), events and
`Spec`'s quantities; no program counter and no register number occurs. A field is either a fact
the thread layer has not yet exported (a row of "thread-layer gaps" in the development notes) or an
order the
protocol layer proves from its hypotheses (`Ring.Kv.copy_read_order` and the `bar.sync` and
`fence.proxy.async` of the prologue); the file says which.

* `KvCopies`: the K/V copies of every block that exists. For each block `i < num_iters` of a CTA
  and each of the eight boxes (K or V, slab, half) there is a tensor-copy event, of the loader's
  state with `d.i = i` or of the prologue's copy site of block `i`, whose spec is `kvCopySpec`
  at the origin and destination the box has in `Spec`'s terms. *Thread layer*: the loader's
  half is `EvW.loader_shape` with `EvW.ldCopy_origin` once the block-table words of its state are
  the pages (`Q.page`) of its slabs; the prologue's half needs the closed forms of `copyDst`,
  `copyX`, `copyY` (open rows of the gap table); existence is progress (every thread exits).
* `KvOrder`: the order of one such copy and one MMA read of a byte it writes. *Protocol layer*:
  `Ring.Kv.copy_read_order` (RAW, `copyUse ≤ readUse`) for the copy before the read, the copies
  of the other uses of the slot before it or after the read (the ring items), and the absence of
  any other writer of the K/V region (`RingKvFoot`'s footprints plus the region table of shared
  memory, an open row of `Ring.lean`'s list).
* `QTile`: the Q tile. *Thread layer*: the prologue's `st.shared.v4.b32` of the packed query words
  (`ProA.shape_stq`) with the closed forms of `qStoreBase` and of the query loads' addresses (open
  rows) say that the store covering element `(r, d)` of the tile stores the bf16 query of its
  row; *protocol layer*: the `bar.sync` and `fence.proxy.async` before the MMA warp's first QK
  issue order that store before the MMA's read, and nothing else writes the tile.
* `MmaWords`: the loop bound the MMA warp read from shared memory is the split's `num_iters`
  (the reads-from of the word the prologue wrote: `Ring.lean`'s premise `np = Spec.numPre`
  and its sibling).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface (St TSt)
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvCopySpec)

noncomputable section

/-! ### The thread's CTA and the blocks it works on -/

/-- The bf16 query element of tile row `r` and head-dimension index `d` for the thread's CTA:
token `r / 6` of its request, head `6 kvh + r % 6`. -/
def qElem (Q : Params) (L : Launch) (g r d : Nat) : ℝ :=
  Q.q (Q.qStart (reqOf L g) + r / 6) (group * kvhOf L g + r % 6) d

/-- The tile row is a row of a valid token of the thread's request. -/
def QRowValid (Q : Params) (L : Launch) (g r : Nat) : Prop :=
  r < 60 ∧ r / 6 < Q.qLen (reqOf L g)

/-! ### Abstract states of events -/

/-- The event `m` of thread `m.1` is at the MMA warp's state `d`. -/
def AtMma (Q : Params) (L : Launch) (X : Execution) (m : EvId) (d : Mma.D) : Prop :=
  ∃ P, St Q L X m.1 m.2 = some (some (.w (.mma d P)))

/-- The MMA state `d` is an MMA of block `i`: a QK MMA of iteration `i` or a PV MMA of iteration
`i + 1`. -/
def MmaBlock (d : Mma.D) (i : Nat) : Prop :=
  (∃ j, d.site = .qk j ∧ d.i = i) ∨ ∃ j, d.site = .pv j ∧ d.i = i + 1

/-- The event `c` is a copy of block `i`'s K/V tiles: the loader's state at iteration `i` or the
prologue's copy site of block `i` (sites `4 i … 4 i + 3`). -/
def CopyBlock (Q : Params) (L : Launch) (X : Execution) (c : EvId) (i : Nat) : Prop :=
  (∃ d P, St Q L X c.1 c.2 = some (some (.w (.loader d P))) ∧ d.i = i) ∨
  ∃ (d : ProA.D) (j : Nat), St Q L X c.1 c.2 = some (some (.d (.pro d))) ∧ j < 12 ∧
    d.site = ProA.ptcSite j ∧ j / 4 = i

/-! ### The premises -/

/-- **The K/V copies of every block that exists** (see the file header for the rows behind it).
For the CTA of thread `g`, block `i < num_iters`, and each box `(isV, slab, hh)`, there is a
tensor copy, in the same CTA, of block `i`, with the spec `kvCopySpec` at the origin
`(kvh · head_cols + 128 isV + 64 hh, page · page_rows + kvh · head_rows)` of the page of the box's
slab `2 (split + i · num_splits) + slab` and the destination in ring slot `i % 3`. -/
structure KvCopies (Q : Params) (L : Launch) (X : Execution) : Prop where
  exists_copy : ∀ {g i : Nat} (isV slab hh : Nat), g < L.threads →
    i < Q.numIters (reqOf L g) (splitOf L g) → isV ≤ 1 → slab ≤ 1 → hh ≤ 1 →
    ∃ (c : EvId) (o : TensorCopy.Observation) (a : Nat) (bar : Loc),
      c.1 < L.threads ∧ c.1 / L.block = g / L.block ∧ X.TensorIssue c a o.spec ∧
      X.tensor c = some o ∧ CopyBlock Q L X c i ∧
      o.spec = kvCopySpec Q (g / L.block) (kvhOf L g * Q.headCols + 128 * isV + 64 * hh)
        (Q.page (reqOf L g) (2 * blkOf Q L g i + slab) * Q.pageRows + kvhOf L g * Q.headRows)
        (L.sharedBase + 32768 * (i % 3) + 98304 * isV + 8192 * slab + 16384 * hh) bar

/-- **The order of a copy of block `i` and an MMA read of a byte it writes.** For an MMA `m` of
block `i` and a copy `c` of block `i`, at a location `l` the copy writes at slot `(x, y, z)` and
the MMA reads at operand byte `idx`: the byte has been written (the copy completed), the copy is
causally before the read, and every other write covering `l` is the copy, before it, or after the
read. -/
structure KvOrder (Q : Params) (L : Launch) (X : Execution) : Prop where
  order : ∀ {m c : EvId} {d : Mma.D} {i : Nat} {o : TensorCopy.Observation} {a : Nat}
    {x y z : Nat} {l : Loc} {isB : Bool} {idx : Nat} {obs : Option Byte},
    AtMma Q L X m d → MmaBlock d i → CopyBlock Q L X c i → X.tensor c = some o →
    X.TensorIssue c a o.spec → TensorCopy.writeLoc o.spec x y z = some l →
    X.MmaRead m isB idx l obs →
    (∃ b, TensorCopy.writeByte o x y z = some b) ∧
    modelCausality L X l (.async c (.write (.load x y z))) (.async m (.mmaRead isB idx)) ∧
    ∀ other fp bytes, X.MemWrites other fp bytes → fp.Covers l →
      other = .async c (.write (.load x y z)) ∨
      modelCausality L X l other (.async c (.write (.load x y z))) ∨
      modelCausality L X l (.async m (.mmaRead isB idx)) other

/-- **The Q tile.** For a valid row `r` and element `d < 128` of a thread's CTA, byte `z`: a
thread write `w` of the CTA covers the byte of the tile (`qAddr`) and writes byte `z` of the bf16
query element (`qElem`), and for every QK MMA of the CTA that reads that byte as its A operand
the write is causally before the read and every other write covering it is before the write or
after the read. -/
structure QTile (Q : Params) (L : Launch) (X : Execution) : Prop where
  tile : ∀ {g r d z : Nat}, g < L.threads → QRowValid Q L g r → d < 128 → z < 2 →
    ∃ (w : EvId) (a : Acc) (bs : List Byte), (∃ pc, X.get w = some ⟨pc, .wr a bs⟩) ∧
      a.Covers ⟨.shared, g / L.block, qAddr L.sharedBase r d z⟩ ∧
      wbyte a bs ⟨.shared, g / L.block, qAddr L.sharedBase r d z⟩ =
        some ((Value.float .bf16 (qElem Q L g r d)).byteAt z) ∧
      ∀ {m : EvId} {dm : Mma.D} {idx : Nat} {obs : Option Byte},
        AtMma Q L X m dm → (∃ j, dm.site = .qk j) → m.1 / L.block = g / L.block →
        X.MmaRead m false idx ⟨.shared, g / L.block, qAddr L.sharedBase r d z⟩ obs →
        modelCausality L X ⟨.shared, g / L.block, qAddr L.sharedBase r d z⟩ (.thread w)
          (.async m (.mmaRead false idx)) ∧
        ∀ other fp bytes, X.MemWrites other fp bytes →
          fp.Covers ⟨.shared, g / L.block, qAddr L.sharedBase r d z⟩ →
          other = .thread w ∨
          modelCausality L X ⟨.shared, g / L.block, qAddr L.sharedBase r d z⟩ other (.thread w) ∨
          modelCausality L X ⟨.shared, g / L.block, qAddr L.sharedBase r d z⟩
            (.async m (.mmaRead false idx)) other

/-- **The words the MMA warp read**: the loop bound is the split's `num_iters`, and the Tensor
Memory base is the allocation's, column 0 (`SO.tm_ok_zero`, the premise `BaseWordZero`). -/
structure MmaWords (Q : Params) (L : Launch) (X : Execution) : Prop where
  iters : ∀ {m : EvId} {d : Mma.D}, m.1 < L.threads → AtMma Q L X m d →
    (Mma.QkSite d.site ∨ Mma.PvSite d.site) → d.n = Q.numIters (reqOf L m.1) (splitOf L m.1)
  tm : ∀ {m : EvId} {d : Mma.D}, AtMma Q L X m d → d.tm = 0

/-- **The score accumulation chain.** QK MMA `j + 1` of an iteration accumulates onto QK MMA `j`
of the same iteration: the earlier MMA event of the thread at the state of step `j` (the machine's
`qkNext`: its successor state is step `j + 1`'s, after exactly one event) is an MMA event, and for
every cell the later one writes it is the accumulator read source (`ReadSource .acc`: every other
write of the cell, the P store of the block two before and the QK MMAs, is before it or after the
later MMA; *protocol layer*: `SOTmemOrder.pv_before_qk_exec` and the S handoffs). -/
structure QkChain (Q : Params) (L : Launch) (X : Execution) : Prop where
  prev : ∀ {g k j : Nat} {d : Mma.D} {P : Loader.Pro} (hj : j + 1 < 8),
    St Q L X g k = some (some (.w (.mma d P))) → d.site = .qk ⟨j + 1, hj⟩ →
    ∃ k', k' < k ∧ St Q L X g k' =
        some (some (.w (.mma { d with site := .qk ⟨j, by omega⟩ } P))) ∧
      (∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
      ∀ cell, X.MmaCell (g, k) cell → TcMma.ReadSource L X .acc (g, k') (g, k) cell

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Mma
