-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmTot
public import Kernels.InklingRelDecode.Proof.Thread.LaneWord
public import Lemmas.Flow.ArithCore
public import Lemmas.Flow.CvtBf

@[expose] public section

/-! # The softmax region's register table

The register table of the softmax region's machine (`Sm.lean`): every register of the code as a
function of the state (`valueOf`). The machine, its invariant and its successor function are in
`Sm.lean`; the values of the score stage's second half on any words are in `SmTotV.lean`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Classical

noncomputable section
set_option maxRecDepth 100000

/-! ### The register table -/

/-- The scalar registers of the region: the inherited numbers and what the setup computes of
them and of the thread index. -/
def valuesS (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let T := g % L.block
  let e := d.e
  let sb := L.sharedBase
  [ (1, .pred (decide (half T ≠ 0))), (2, .pred (decide (half T = 0))),
    (3, .pred (decide (T < 32))),
    (85, .pred (act0 e T)), (86, .pred (decide (row T < 60))),
    (87, .pred (decide (tokOf T < e.qlen))),
    (88, .pred (decide (e.nbias ≤ e.split))),
    (89, .pred (rowValid e T && decide (e.nbias ≤ e.split))),
    (90, .pred (decide (0 < e.r25 ∧ e.r25 < 2 ^ 31))),
    (171, .pred true), (175, .pred (rowValid e T)), (177, .pred (decide (T % 128 = 0))),
    (199, z16),
    (462, b32 T), (463, b32 e.tm), (464, b32 (T / 32)), (478, b32 e.split),
    (481, b32 e.qlen), (482, b32 e.past), (483, b32 e.nbias), (484, b32 e.r23),
    (485, b32 e.r24), (486, b32 e.r25), (487, b32 e.r26), (490, b32 e.kvh),
    (491, b32 ((e.tm + 256) % 2 ^ 32)),
    (496, b32 (tokOf T)), (497, b32 ((e.kvh + remOf T) % 2 ^ 32)),
    (498, .float .f32 (e.sc * log2eF32)), (499, .float .f32 (-(e.sc * log2eF32))),
    (500, b32 ((sb + T % 4 * 4) % 2 ^ 32)),
    (501, b32 (e.splits * 128 % 2 ^ 32)),
    (525, b32 e.scb), (527, b32 e.strRel), (532, b32 e.splits), (533, b32 e.ntok),
    (610, b32 e.qs), (623, b32 ((sb + 213312) % 2 ^ 32)), (624, b32 ((sb + 213328) % 2 ^ 32)),
    (666, b32 (sb % 2 ^ 32)), (792, b32 ((sb + 212992) % 2 ^ 32)),
    (793, b32 (T % 16)), (794, b32 (T / 32 % 4 * 32)), (795, b32 (T / 32 % 4 * 16)),
    (796, b32 (row T)), (797, b32 (T * 4)), (798, b32 (half T * 64)),
    (799, b32 (T / 16)), (800, b32 (half T)), (801, b32 (remOf T)), (802, b32 (remOf T)),
    (803, b32 ((e.qs + tokOf T) % 2 ^ 32)), (804, b32 1065353216),
    (805, .float .f32 (1 / e.sc)),
    (806, b32 (r345 e T)), (807, b32 (r346 e)), (808, b32 (T / 32 % 4 * 4)),
    (809, b32 (T % 4 * 4)), (810, b32 (posOf e T)), (811, b32 (pos2Of e T)),
    (1533, b32 ((sb + 212992 + T / 32 % 4 * 4) % 2 ^ 32)),
    (1611, b32 ((d.stg.bw * 2097152 + (e.tm + 256) % 2 ^ 32) % 2 ^ 32)),
    (327, b16 (row T)), (328, b16 (row T * 43)), (329, b16 (tokOf T)),
    (330, b16 (tokOf T * 6)), (331, b16 (remOf T)),
    (1914, d.m), (1915, d.l) ]

/-- The 64-bit registers: the row pointer's stages, the loop counter, the pairs of positions and
the 128 bias pointers. -/
def valuesP (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let T := g % L.block
  let e := d.e
  [ (1956, b64 (half T * 64)), (1957, b64 (p9 e T)),
    (1958, b64 (sxw e.r25)), (1959, b64 e.r26),
    (1960, joinValue (.float .f32 (1 / e.sc)) (.float .f32 (1 / e.sc))),
    (1961, joinValue (b32 (posOf e T)) (b32 (pos2Of e T))),
    (2019, b64 e.rel), (2023, b64 e.rd75),
    (2024, b64 e.rd76),
    (2206, b64 (p258 e T)), (2207, b64 (p259 e T)), (2208, b64 (p260 e T)),
    (2209, b64 (p261 e T)), (2210, b64 (p262 e T)) ]

/-- The 31 position pairs `%rd14 … %rd44` (`pos - 2 j - 2`, `pos - 2 j - 3`) and the 62 sums they
are packed from (`%r351 … %r412`: `%r(351 + k) = pos - (63 - k)`). -/
def valuesQ (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  (List.range 31).map (fun j => (1962 + j, pairPos d.e (g % L.block) (2 + 2 * j) (3 + 2 * j))) ++
  (List.range 62).map fun k => (812 + k, posSum d.e (g % L.block) (63 - k))

/-- The 64 bias pointers of the current block (`%rd193 …`: the first word's, then `2 k` more) and
of the next block (`%rd263 …`). -/
def valuesR (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let T := g % L.block
  (List.range 64).map (fun k => (2141 + k, b64 ((ptrAt d.e T (key d.n) + 2 * k) % 2 ^ 64))) ++
  (List.range 64).map (fun k => (2211 + k,
    b64 ((ptrAt d.e T ((d.e.splits * 128 + d.n * 128) % 2 ^ 32) + 2 * k) % 2 ^ 64)))

/-- The bias words: the half-word registers of the current block (`%rs82 …`) and of the next
(`%rs151`, `%rs153 …`, with the zero constant `%rs152`), and the packed words (`%r1455 …`). -/
def valuesWf (wd vd : Nat → Value) : List (Nat × Value) :=
  (List.range 64).map (fun k => (263 + k, wd k)) ++
  ((332, vd 0) :: (333, z16) :: (List.range 63).map (fun k => (334 + k, vd (k + 1)))) ++
  (List.range 32).map (fun q => (1916 + q, joinValue (wd (2 * q)) (wd (2 * q + 1))))

/-- The bias words of the state `d`. -/
abbrev valuesW (d : D) : List (Nat × Value) := valuesWf d.wd d.vd

/-- The lane bits `b` the broadcast returned, shifted to bit 21 (`%r45`; the code masks the shifted
word with `0x600000`, which keeps `b < 4`). -/
def r45 (b : Nat) : Nat := b * 2097152

/-- The tile column of `%r(47 + k)`, a probability the code keeps as a single register
(`16 (k / 4) + 12 + k % 4`: the columns `12 … 15` of each 16). -/
def colR (k : Nat) : Nat := 16 * (k / 4) + 12 + k % 4

/-- The pair `%rd(46 + q)`: the columns `2 w` and `2 w + 1` with `w = 8 (q / 6) + q % 6` (the
other eight words of the 32 are the single registers `%r47 …`). -/
def pairW (q : Nat) : Nat := 8 * (q / 6) + q % 6

/-- The word `w` of the stored `P` tile (`%r(1216 + w)`): the two `bf16` numbers of the columns
`2 w` and `2 w + 1`. -/
def D.pw (d : D) (w : Nat) : Value :=
  .pair (.float .bf16 (d.pf (2 * w))) (.float .bf16 (d.pf (2 * w + 1)))

/-- The outcome of the conversion that makes the stored word `w` (`%r(1216 + w)`) from the
probability words: for a word of a packed pair (`w % 8 < 6`, the pair `%rd(46 + q)` with
`pairW q = w`) the unpack `mov.b64 {lo, hi}` of the pair (pcs 951 to 997) and
`cvt.rn.bf16x2.f32 w, hi, lo`; for a word of two single registers (pcs 1000 to 1007)
`cvt.rn.bf16x2.f32 w, %r(2 w + 1), %r(2 w)`. -/
def D.pwE (d : D) (w : Nat) : Exec Value :=
  if w % 8 < 6 then
    (unpackE 64 (joinValue (d.stg.pv (2 * w)) (d.stg.pv (2 * w + 1)))).bind
      fun p => cvtBfE p.2 p.1
  else cvtBfE (d.stg.pv (2 * w + 1)) (d.stg.pv (2 * w))

/-- The stored word `w` (`b32 0` where its conversion faults). -/
def D.pwV (d : D) (w : Nat) : Value := okVal (b32 0) (d.pwE w)

/-- The 24 unpacks and conversions before the P store's barrier (pcs 951 to 998) have outcomes. -/
def D.pqOk (d : D) : Prop := ∀ q < 24, (d.pwE (pairW q)).toBool = true

/-- The 8 conversions after the P store's barrier (pcs 1000 to 1007) have outcomes. -/
def D.psOk (d : D) : Prop := ∀ j < 8, (d.pwE (8 * (j / 2) + 6 + j % 2)).toBool = true

/-- The words and pairs of the S tile, the probabilities as single registers and pairs, and the
`bf16` words of the stored tile (`%r415 …`, `%rd499 …`, `%r47 …`, `%rd46 …`, `%r1216 …`). -/
def valuesXt (d : D) : List (Nat × Value) :=
  (List.range 64).map (fun k => (876 + k, (d.sv k).1)) ++
  ((List.range 32).map (fun q => (2447 + q, joinValue (d.sv (2 * q)).1 (d.sv (2 * q + 1)).1)) ++
  ((List.range 16).map (fun k => (508 + k, d.stg.pv (colR k))) ++
  ((List.range 24).map (fun q => (1994 + q, joinValue (d.stg.pv (2 * pairW q))
    (d.stg.pv (2 * pairW q + 1)))) ++
  (List.range 32).map (fun w => (1677 + w, d.pwV w)))))

/-- The product of `alpha` and a loaded word of `O` (`mul.f32 %r(1151 + k), %r46, %r(1086 + k)`):
the outcome's value, `0` where it faults. -/
def prodO (al w : Value) : Value := okVal (b32 0) (mulE false al w)

theorem prodO_bytes (al w : Value) : (prodO al w).bytes = 4 := by
  unfold prodO
  rcases h : mulE false al w with e | v
  · rfl
  · exact mulE_four false al w v h

/-- The registers of the stage's words: the unpacked score words of the row maximum
(`%r954 …`), the words of `O` the rescale loaded (`%r1086 …`) and the rescaled words
(`%r1151 …`, `alpha` times them). -/
def valuesXs (fsv : Nat → { v : Value // v.bytes = 4 }) (ow : Nat → Value) (al : Value) :
    List (Nat × Value) :=
  (List.range 64).map (fun k => (colReg k, (fsv k).1)) ++
  ((List.range 64).map (fun k => (1547 + k, ow k)) ++
  (List.range 64).map (fun k => (1612 + k, prodO al (ow k))))

theorem keys_Xs (fsv : Nat → { v : Value // v.bytes = 4 }) (ow : Nat → Value) (al : Value) :
    ∀ r ∈ (valuesXs fsv ow al).map Prod.fst,
      (1415 ≤ r ∧ r < 1499) ∨ (1547 ≤ r ∧ r < 1611) ∨ (1612 ≤ r ∧ r < 1676) := by
  intro r hr
  simp only [valuesXs, List.map_append, List.map_map, List.mem_append, List.mem_map,
    List.mem_range, Function.comp_apply] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact Or.inl (colReg_range k hk)
  · omega
  · omega

/-- The registers of the S tile and the P store: the guard of the store and the warp's offset
(`%r45`, from the recorded lane bits), then `valuesXt`. -/
def valuesX (_L : Launch) (_g : Nat) (d : D) : List (Nat × Value) :=
  [ (172, .pred true), (506, b32 (r45 d.stg.bw)), (168, .pred d.stg.kp), (507, d.stg.al),
    (1522, d.stg.mn), (1531, d.stg.rs), (1544, d.stg.m2),
    (1520, ownV fun k => (d.stg.fsv k).1), (1529, d.stg.sw), (1536, d.stg.cm1),
    (1538, d.stg.cm2), (1540, d.stg.cm3), (1534, d.stg.cm4), (1542, d.stg.ld) ] ++
    (valuesXt d ++ valuesXs d.stg.fsv d.stg.ow d.stg.al)

/-- The scalar registers that change with the iteration: the loop's tests, the next block's key
and number, the parity of the stage, the loop counter and the Tensor Memory and barrier addresses
that depend on the stage. The only other registers that change with the iteration are the bias
pointers (`valuesR`). -/
def valuesI (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let T := g % L.block
  let e := d.e
  let sb := L.sharedBase
  [ (91, .pred (decide (e.r26 = d.i))),
    (92, .pred (actB e T d.i)),
    (93, .pred (decide (e.nbias ≤ d.n + e.splits))),
    (94, .pred (decide (d.i + 1 < e.r25 ∧ e.r25 < 2 ^ 31))),
    (95, .pred (decide (d.i + 1 < e.r25 ∧ e.r25 < 2 ^ 31) &&
      decide (e.nbias ≤ d.n + e.splits))),
    (502, b32 ((d.n + e.splits) % 2 ^ 32)),
    (503, b32 ((e.splits * 128 + d.n * 128) % 2 ^ 32)),
    (504, b32 (d.i % 2)), (505, b32 ((sb + d.i % 2 * 8) % 2 ^ 32)),
    (874, b32 ((sb + d.i % 2 * 8 + 213280) % 2 ^ 32)), (875, b32 (d.i / 2 % 2)),
    (940, b32 d.i), (941, b32 (d.i % 2 * 8)),
    (943, b32 ((d.i % 2 * 128 + e.tm) % 2 ^ 32)),
    (1676, b32 ((d.i % 2 * 128 + e.tm + r45 d.stg.bw) % 2 ^ 32)),
    (1709, b32 ((sb + d.i % 2 * 8 + 213296) % 2 ^ 32)),
    (1912, b32 (key d.n)), (1913, b32 d.n), (1993, b64 (d.i + 1)), (2446, b64 d.i),
    (169, .pred (decide (d.i = 0))), (1532, b32 ((d.i + 1) % 2)),
    (179, .pred (pe0 e T d.n)), (180, .pred (pe1 e T d.n)) ]

/-- The registers of the region at state `d` of thread `g`, nested to the right. -/
def values (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  valuesI L g d ++ (valuesS L g d ++ (valuesP L g d ++ (valuesQ L g d ++ (valuesR L g d ++
    (valuesW d ++ valuesX L g d)))))

/-- The value of register `r` at state `d`: the table's. -/
def valueOf (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values L g d).lookup r).getD (b32 0)

/-- The registers live at `pc`, with their values at state `d`. -/
def factsAt (L : Launch) (g : Nat) (pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g d)

abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) := factsAt L g d.site.pc d

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
