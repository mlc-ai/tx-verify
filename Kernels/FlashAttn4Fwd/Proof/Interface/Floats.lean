-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Tc
public import Kernels.FlashAttn4Fwd.Proof.Interface.Stats

@[expose] public section

/-! # What the thread layer exports for the values of the reads

The protocols of `Protocol/Floats*` show that every read a role machine follows only on a
single-precision float, or on a broadcast of its own value, returns such a value. They need these
facts of the role machines:

* **Tensor Memory.** Every MMA is `kind::f16` with f16 inputs and an f32 accumulator (`mma_kind`,
  the instruction descriptors `Mma.qkIdesc`, `Mma.pvIdesc`); the loads read MMA results only.
* **Statistics words.** Every `ld.shared` of a correction thread is its load of a statistics word
  (`corr_rd`, the sites `ldA`, `ldL`). A softmax thread's store of its statistics word writes the
  bytes of a 4-byte value that reads as a single-precision float (`soft_store_f32`, `F32Word`: a
  float payload, or the bits `0f3F800000` of the factor `1`), it stores the word once per
  generation of its statistics barrier (`soft_store_one`), and every event of the thread on its
  statistics barrier (a `bar.arrive`) but the first of an item follows such a store of the same
  generation (`soft_arrive_store`).
* **Shuffles.** Every shuffle is a full-warp `shfl.sync.idx` from lane 0 (`shfl_form`, `b = 0`,
  `c = 31`); the source values of the `n`-th shuffles of two lanes of a warp are equal
  (`shfl_uniform`: each lane runs the same sites with warp-uniform source registers); and lane 0
  of a warp does not exit before its `n`-th shuffle when another lane of the warp makes one
  (`shfl_live`: the lanes of a warp run the same sites to their exit).

`shfl_uniform` and `shfl_live` speak of two lanes of one warp; the role machines prove them from
the lane-independence of each role's control flow and source registers. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow TcMma

noncomputable section

/-- The thread layer's facts for the values of the reads. -/
structure FloatFacts (L : Launch) (X : Execution) : Prop where
  /-- Every MMA is `kind::f16` with f16 inputs and an f32 accumulator. -/
  mma_kind : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
    X.MmaIssue i d s acc mask → s.descriptor.kind = .f16 .f16 .f32
  /-- Every `ld.shared` of a correction thread loads its row's statistics word of a stage. -/
  corr_rd : ∀ {g i pc : Nat} {a : Acc} {bs : List (Option Byte)}, g < L.threads →
    8 ≤ warpOf L g → warpOf L g < 12 → X.get (g, i) = some ⟨pc, .rd a bs⟩ →
      ∃ st < 2, CorrLoad L X g i a false st
  /-- A softmax thread's store of its statistics word writes the bytes of a 4-byte value that
  reads as a single-precision float, once the thread's earlier Tensor Memory loads returned
  single-precision floats. -/
  soft_store_f32 : ∀ {g i pc : Nat} {a : Acc} {ws : List Byte}, g < L.threads →
    warpOf L g < 8 → X.get (g, i) = some ⟨pc, .wr a ws⟩ → SoftStore L X g i a true →
    (∀ k < i, ∀ pc a' (vals' : List Value),
      X.get (g, k) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals') →
      ∃ x, F32Word ws x
  /-- A softmax thread stores its statistics word once per generation of its statistics
  barrier. -/
  soft_store_one : ∀ {g i i' pc pc' : Nat} {a a' : Acc} {ws ws' : List Byte}, g < L.threads →
    warpOf L g < 8 → X.get (g, i) = some ⟨pc, .wr a ws⟩ → X.get (g, i') = some ⟨pc', .wr a' ws'⟩ →
    SoftStore L X g i a true → SoftStore L X g i' a' true →
    barOrd X g i (warpOf L g + 3) = barOrd X g i' (warpOf L g + 3) → i = i'
  /-- An event of a softmax thread on a statistics barrier of ordinal `(n + 1) j + t + 1` with
  `t < n` (every generation but an item's first) follows its store of its statistics word of the
  same generation. -/
  soft_arrive_store : ∀ {g y pc id : Nat} {cnt : Option Nat} {md : BarMode}, g < L.threads →
    warpOf L g < 8 → X.get (g, y) = some ⟨pc, .bar id cnt md⟩ → id ≠ 2 →
    (∃ j t, t < kvTiles L ∧ barOrd X g y id = (kvTiles L + 1) * j + t + 1) →
      ∃ i < y, ∃ pc' a ws, X.get (g, i) = some ⟨pc', .wr a ws⟩ ∧ SoftStore L X g i a true ∧
        barOrd X g i id = barOrd X g y id
  /-- Every shuffle is a full-warp `shfl.sync.idx` from lane 0. -/
  shfl_form : ∀ {g i pc b c : Nat} {md : ShflMode} {a recv : Value} {ok : Bool}, g < L.threads →
    X.get (g, i) = some ⟨pc, .shfl md a b c recv ok⟩ → md = .idx ∧ b = 0 ∧ c = 31
  /-- The `n`-th shuffles of two lanes of a warp have the same source value. -/
  shfl_uniform : ∀ {g h i j n pc pc' b b' c c' : Nat} {md md' : ShflMode}
    {a a' r r' : Value} {o o' : Bool}, SameWarp L g h → X.ShflK (g, i) n → X.ShflK (h, j) n →
    X.get (g, i) = some ⟨pc, .shfl md a b c r o⟩ →
    X.get (h, j) = some ⟨pc', .shfl md' a' b' c' r' o'⟩ → a = a'
  /-- Lane 0 of a warp does not exit before its `n`-th shuffle when a lane of the warp makes
  one. -/
  shfl_live : ∀ {g i n : Nat}, g < L.threads → X.ShflK (g, i) n →
    ¬ ShflExited X (g - laneOf L g) n

end
end PTX.Kernels.FlashAttn4Fwd.Proof
