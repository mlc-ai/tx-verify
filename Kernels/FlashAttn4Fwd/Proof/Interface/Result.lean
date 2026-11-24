-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Output
public import Kernels.FlashAttn4Fwd.Proof.Interface.Schedule
public import Kernels.FlashAttn4Fwd.Proof.Interface.Rings
public import Kernels.FlashAttn4Fwd.Proof.Thread.Store
public import Lemmas.Real.Softmax

@[expose] public section

/-! # What the thread layer exports for the output

Item `j` of a thread's cluster is the work item `workOf L g j`, whose coordinates are the batch,
head and query block of `coordsOf` (`tileBatch`, `tileHead`, `tileBlock`). Stage `st` of the item
in the CTA of rank `r` covers the 128 output rows from `tileRow = 512 m + 256 st + 128 r`. The store
warp (warp 13) writes it with two tensor stores, one per 64-column half `hh`, each a box of the O
map at origin `(64 hh, tileRow, head, batch)` read from the stage's half at
`3072 + 32768 st + 16384 hh` (`oSpec`); slot `(x, y, k)` reads the 128B-swizzled shared byte
`stageLoc` and writes byte `k` of element `(row tileRow + y, column 64 hh + x)`.

The fields are the facts the result layer needs from the roles that are not yet exported:

* `StoreFacts` (the store warp's run): every tensor store is the store of one half of one stage
  of the lane's item, numbered by its free arrivals of the stage, at the site's instruction; and a
  store lane that exited issued all of them.
* `WriteFacts` (every role): every write of a global byte is a tensor store's slot write, and no
  thread is cancelled by a cluster launch control request.
* `OutputValues` (the correction and softmax runs): every staging byte a correction thread
  writes for its row holds the half-precision ratio of the row's final accumulator and row sum,
  which an online softmax over the item's key blocks built (`SoftmaxRun`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The batch of item `j` of thread `g`'s cluster. -/
def tileBatch (L : Launch) (g j : Nat) : Nat := (coordsOf L (workOf L g j)).1

/-- The head of item `j` of thread `g`'s cluster. -/
def tileHead (L : Launch) (g j : Nat) : Nat := (coordsOf L (workOf L g j)).2.1

/-- The query block (512 rows) of item `j` of thread `g`'s cluster. -/
def tileBlock (L : Launch) (g j : Nat) : Nat := (coordsOf L (workOf L g j)).2.2

/-- The first output row of stage `st` of item `j` in the CTA of thread `g`. -/
def tileRow (L : Launch) (g j st : Nat) : Nat := 512 * tileBlock L g j + 256 * st + 128 * rankOf L g

/-- The first shared byte of half `hh` of stage `st`'s staging buffer. -/
def stageBase (L : Launch) (st hh : Nat) : Nat := L.sharedBase + (3072 + 32768 * st + 16384 * hh)

/-- The O map's box: 64 head-dimension elements by 128 rows. -/
def oBox : TensorTile.Box 4 := ⟨![64, 128, 1, 1], fun _ => 1⟩

/-- The origin of the tensor store of half `hh` of stage `st` of item `j` in the CTA of `g`, in
the O map's coordinates (head dimension, row, head, batch). -/
def oOrigin (L : Launch) (g j st hh : Nat) : Fin 4 → Int :=
  ![((64 * hh : Nat) : Int), ((tileRow L g j st : Nat) : Int), ((tileHead L g j : Nat) : Int),
    ((tileBatch L g j : Nat) : Int)]

/-- The tensor store of half `hh` of stage `st` of item `j` by store lane `g`: a box of the O map
at `oOrigin`, read from the half's staging buffer in the lane's CTA. -/
def oSpec (P : Params) (L : Launch) (g j st hh : Nat) : TensorStore.Spec where
  outer := 3
  descriptor := FlashAttn4Fwd.mapO P.oBase P.sq P.h P.b P.oFill P.oClass
  origin := oOrigin L g j st hh
  sharedBase := ⟨.shared, ctaOf L g, stageBase L st hh⟩
  reduce := none

/-- The shared byte that slot `(x, y, k)` of half `hh` of stage `st` reads in CTA `c`: the O map's
128B-swizzled tile layout. -/
def stageLoc (L : Launch) (c st hh x y k : Nat) : Loc :=
  ⟨.shared, c, TensorTile.sharedByte oBox 2 .b128 (stageBase L st hh) x y k⟩

/-- The store warp's export for the output: the shape of its tensor stores and their issue. -/
structure StoreFacts (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- Every tensor store is a store lane's store of half `hh` of stage `st` (`StoreSrc`) at the
  site's instruction, through the O map, of the item numbered by the lane's free arrivals of the
  stage before it, which exists. -/
  spec : ∀ {g k pc a : Nat} {s : TensorStore.Spec}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tensorStore a s⟩ →
      ∃ st hh : Fin 2, warpOf L g = 13 ∧ StoreSrc L X g k pc s st ∧
        pc = Store.Site.pc (.tma st hh) ∧ a = P.oMap ∧
        workOf L g (arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take k)) < totOf L ∧
        s = oSpec P L g (arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take k)) st hh
  /-- A store lane that exited issued the store of every half of every stage of every item of
  its cluster. -/
  issued : ∀ {g : Nat}, g < L.threads → warpOf L g = 13 →
    (∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩) → ∀ j, workOf L g j < totOf L →
      ∀ st hh : Fin 2, ∃ k a s, X.get (g, k) = some ⟨Store.Site.pc (.tma st hh), .tensorStore a s⟩ ∧
        arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take k) = j

/-- Every role's export for the output: the global writes and the threads that run. -/
structure WriteFacts (L : Launch) (X : Execution) : Prop where
  /-- Every write of a global byte is a tensor store's write of a slot. -/
  global : ∀ w a bs, X.MemWrites w a bs → a.loc.space = .global →
    ∃ i x y k, w = .async i (.write (.store x y k))
  /-- No thread is cancelled by a cluster launch control request. -/
  started : ∀ g < L.threads, ¬ ClcCanceled L X g

/-- The key of column `j` of the block of visit `τ`: the blocks are visited last first. -/
def visitKey (P : Params) (τ j : Nat) : Nat := 128 * (kvBlocks P - 1 - τ) + j

/-- **An online softmax of output row `row` of head `head` of batch `batch`.** After visit `τ` of
the key blocks (`visitKey`) the row has reference exponent `c τ`, row sum `l τ` and accumulator
`O τ d` of head-dimension column `d`: the first visit sums its weights `2 ^ (scale · S - c 0)`
(times `V` for the accumulator), each later visit rescales by `2 ^ (c τ - c (τ + 1))` and adds its
own. -/
structure SoftmaxRun (P : Params) (batch head row : Nat) (c l : Nat → ℝ) (O : Nat → Nat → ℝ) :
    Prop where
  acc0 : ∀ d < 128, O 0 d = ∑ j ∈ Finset.range 128,
    (2 : ℝ) ^ (P.scale * score P batch head row (visitKey P 0 j) - c 0) *
      P.v batch head (visitKey P 0 j) d
  accStep : ∀ τ, τ + 1 < kvBlocks P → ∀ d < 128, O (τ + 1) d = O τ d * 2 ^ (c τ - c (τ + 1)) +
    ∑ j ∈ Finset.range 128,
      (2 : ℝ) ^ (P.scale * score P batch head row (visitKey P (τ + 1) j) - c (τ + 1)) *
        P.v batch head (visitKey P (τ + 1) j) d
  sum0 : l 0 = ∑ j ∈ Finset.range 128,
    (2 : ℝ) ^ (P.scale * score P batch head row (visitKey P 0 j) - c 0)
  sumStep : ∀ τ, τ + 1 < kvBlocks P → l (τ + 1) = l τ * 2 ^ (c τ - c (τ + 1)) +
    ∑ j ∈ Finset.range 128,
      (2 : ℝ) ^ (P.scale * score P batch head row (visitKey P (τ + 1) j) - c (τ + 1))

/-- The correction and softmax runs' export for the output values. -/
structure OutputValues (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- A correction thread's write of the staging byte of slot `(x, y, k)` of half `hh` of stage
  `st`, at its item numbered by its staged arrivals of the stage, writes byte `k` of the
  half-precision ratio of the final accumulator of column `64 hh + x` and the final row sum of an
  online softmax of output row `tileRow + y` of the item. -/
  staged : ∀ {g n st hh x y k : Nat} {dst : Acc} {bs : List Byte}, g < L.threads →
    8 ≤ warpOf L g → warpOf L g < 12 → X.Writes (g, n) dst bs → st < 2 → hh < 2 → x < 64 →
    y < 128 → k < 2 → dst.Covers (stageLoc L (ctaOf L g) st hh x y k) →
    ∃ c l O, SoftmaxRun P
        (tileBatch L g (arrivals (stagedBar L (ctaOf L g) st) ((X.tr g).take n)))
        (tileHead L g (arrivals (stagedBar L (ctaOf L g) st) ((X.tr g).take n)))
        (tileRow L g (arrivals (stagedBar L (ctaOf L g) st) ((X.tr g).take n)) st + y) c l O ∧
      wbyte dst bs (stageLoc L (ctaOf L g) st hh x y k) =
        some ((Value.float .f16 (O (kvBlocks P - 1) (64 * hh + x) / l (kvBlocks P - 1))).byteAt k)

/-- **The output values**, for the conclusions: the byte that slot `(x, y, k)` of a store lane's
tensor store of half `hh` of stage `st` of item `j` writes is byte `k` of the half-precision
attention output of its element. -/
def StoreValues (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc a j st hh x y z : Nat} {o : TensorStore.Observation} {b : Byte},
    X.get (g, k) = some ⟨pc, .tensorStore a (oSpec P L g j st hh)⟩ →
    arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take k) = j → st < 2 → hh < 2 → x < 64 →
    y < 128 → z < 2 → X.tensorStores (g, k) = some o → TensorStore.writeByte o x y z = some b →
    b = (Value.float .f16
      (attn P (tileBatch L g j) (tileHead L g j) (tileRow L g j st + y) (64 * hh + x))).byteAt z

/-- The static schedule's coordinates, for the result layer: the item count, the cluster count
and the exact split of every work item into (batch, head, query block). -/
def ItemCoords (P : Params) (L : Launch) : Prop :=
  totOf L = P.items ∧ clusterCount L = P.clusters ∧
    ∀ w < P.items, coordsOf L w = (w / P.blocks / P.h, w / P.blocks % P.h, w % P.blocks)

end
end PTX.Kernels.FlashAttn4Fwd.Proof
