-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Flow.Code
public import Kernels.RmsNorm.Flow.Sites
public import Kernels.RmsNorm.Proof.Math
public import Lemmas.Flow.Code
public import Lemmas.Flow.Facts
public import Lemmas.Flow.Widen
public import Lemmas.Flow.FloatOutcome
public import Kernels.RmsNorm.Assumptions
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-! # A thread of `rmsnorm` as abstract states

Every thread first shuffles its warp index (a value it never uses), then, while its CTA has a
row `c + 152 i` left, runs one iteration per row. It loads its sixteen inputs of the row (two
16-byte vectors of eight halves), converts them to single precision and stages them in its own
32 bytes of shared memory per tile, sums their squares, and reduces the sum over its warp in
five butterfly rounds of shuffles. Lane 0 stores its warp's sum; after a CTA barrier the eight
lanes 0..7 of warp 0 load the eight warp sums, warp 0 reduces them in five more rounds, and
thread 0 stores the CTA's total. After a second barrier every thread loads the total, computes
`1 / sqrt(total / 4096 + eps)`, loads its sixteen weights, reloads its staged inputs, and
stores its sixteen outputs; a third barrier ends the row.

An abstract state is the next event (`site`, and for a vector access the element `sub` and the
values `acc` read so far) with the row iteration `i` and the raw values the thread has read in the
row: the words of its inputs (`xa`, `xb`), the vector loads not yet consumed (`raw`, `rs0`,
`rs1`), the values received in the two butterflies (`ra`, `rb`), warp 0's loaded warp sum (`u`)
and the total (`tt`). The registers hold the outcomes of the code on these values (`values`):
each floating instruction's outcome under the kernel's assumptions (`floatE`, `approxE`,
`widenE`), which is the Core rule's value where an assumption declines a NaN or infinite operand.
The machine stops (`none`) exactly where a load does not rebuild or a local instruction's outcome
faults; on real inputs the outcomes are the floats of the exact real computation. -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The event sites of a thread. -/
inductive Site where
  /-- The shuffle of the warp index. -/
  | shfl0
  /-- The input loads of the two tiles and the stores of the converted inputs. -/
  | ldxa | stxa0 | stxa1 | ldxb | stxb0 | stxb1
  /-- Round `k` of the warp's butterfly. -/
  | bfa (k : Nat)
  /-- Lane 0's store of its warp's sum. -/
  | stws
  /-- The first barrier. -/
  | bar0
  /-- Lanes 0..7 of warp 0: the load of a warp sum. -/
  | ldws
  /-- Round `k` of warp 0's butterfly over the warp sums. -/
  | bfb (k : Nat)
  /-- Thread 0's store of the total. -/
  | stts
  /-- The second barrier. -/
  | bar1
  /-- The load of the total. -/
  | ldts
  /-- Tile 0: the weights, the reloaded inputs, the outputs. -/
  | ldwa | ldsa0 | ldsa1 | stoa
  /-- Tile 1: the weights, the reloaded inputs, the outputs. -/
  | ldwb | ldsb0 | ldsb1 | stob
  /-- The third barrier, ending the row. -/
  | bar2
  | exit
  deriving DecidableEq

def Site.pc : Site → Nat
  | .shfl0 => Flow.shfl_0 | .ldxa => Flow.load_0 | .stxa0 => Flow.store_0
  | .stxa1 => Flow.store_1 | .ldxb => Flow.load_1 | .stxb0 => Flow.store_2
  | .stxb1 => Flow.store_3
  | .bfa 0 => Flow.shfl_1 | .bfa 1 => Flow.shfl_2 | .bfa 2 => Flow.shfl_3
  | .bfa 3 => Flow.shfl_4 | .bfa _ => Flow.shfl_5
  | .stws => Flow.store_4 | .bar0 => Flow.bar_0 | .ldws => Flow.load_2
  | .bfb 0 => Flow.shfl_6 | .bfb 1 => Flow.shfl_7 | .bfb 2 => Flow.shfl_8
  | .bfb 3 => Flow.shfl_9 | .bfb _ => Flow.shfl_10
  | .stts => Flow.store_5 | .bar1 => Flow.bar_1 | .ldts => Flow.load_3
  | .ldwa => Flow.load_4 | .ldsa0 => Flow.load_5 | .ldsa1 => Flow.load_6
  | .stoa => Flow.store_6 | .ldwb => Flow.load_7 | .ldsb0 => Flow.load_8
  | .ldsb1 => Flow.load_9 | .stob => Flow.store_7 | .bar2 => Flow.bar_2 | .exit => Flow.exit_0

/-- The sites of four-element vector accesses. -/
def Site.vec : Site → Bool
  | .ldxa | .stxa0 | .stxa1 | .ldxb | .stxb0 | .stxb1 | .ldwa | .ldsa0 | .ldsa1 | .stoa
  | .ldwb | .ldsb0 | .ldsb1 | .stob => true
  | _ => false

/-- The sites of four-element vector loads. -/
def Site.vload : Site → Bool
  | .ldxa | .ldxb | .ldwa | .ldsa0 | .ldsa1 | .ldwb | .ldsb0 | .ldsb1 => true
  | _ => false

/-- The sites inside a row iteration. -/
def Site.inRow : Site → Bool
  | .shfl0 | .exit => false
  | _ => true

structure D where
  site : Site
  /-- The element of a vector access. -/
  sub : Nat := 0
  /-- The values a vector load has read so far. -/
  acc : List Value := []
  /-- The row iteration. -/
  i : Nat := 0
  /-- Raw values of a vector load not yet consumed: the inputs or the weights. -/
  raw : List Value := []
  /-- The raw values of the two reloads of the staged inputs. -/
  rs0 : List Value := []
  rs1 : List Value := []
  /-- The words of the inputs of the two tiles. -/
  xa : List Value := []
  xb : List Value := []
  /-- The values received in the warp's butterfly. -/
  ra : Nat → Value := fun _ => b32 0
  /-- Warp 0's loaded warp sum (`0` for lanes 8..31). -/
  u : Value := b32 0
  /-- The values received in warp 0's butterfly. -/
  rb : Nat → Value := fun _ => b32 0
  /-- The loaded total. -/
  tt : Value := b32 0

/-! ### The outcomes of the code -/

/-- `add.ftz.f32 d, a, b`, whose value is the outcome of the ideal sum. -/
def addV (x y : Value) : Value := okVal (b32 0) (floatE (addI true) [x, y])

/-- `fma.rn.ftz.f32 d, x, x, z`: the square of `x` added to `z`. -/
def fmaV (x z : Value) : Value := okVal (b32 0) (floatE (fmaI .rn true) [x, x, z])

/-- `mul.rz.ftz.f32x2 d, w, c`: the pair of products. -/
def mulV (w c : Value) : Value := okVal (.pair (b32 0) (b32 0)) (floatE (mul2I .rz true) [w, c])

/-- Half `k` of four words: the low half of word `k / 2` for even `k`, else its high half. -/
def halfOf (ws : List Value) (k : Nat) : Value :=
  if k % 2 = 0 then (splitValue 32 (ws.getD (k / 2) (b32 0))).1
  else (splitValue 32 (ws.getD (k / 2) (b32 0))).2

/-- Half `k` of four words widened to single precision (`cvt.f32.f16`). -/
def xw (ws : List Value) (k : Nat) : Value := okVal (b32 0) (widenE (halfOf ws k))

/-- The `0f00000000` operand of the first fused multiply-add. -/
abbrev z0 : Value := b32 0

/-- The chain of fused multiply-adds of the squares of the first `n` widened halves of `ws` onto
`z`. -/
def fmaRun (ws : List Value) : Nat → Value → Value
  | 0, z => z
  | n + 1, z => fmaV (xw ws n) (fmaRun ws n z)

/-- The sum of squares of the thread's sixteen inputs, as computed. -/
def ssqV (d : D) : Value := fmaRun d.xb 8 (fmaRun d.xa 8 z0)

/-- `q` after adding the first `k` received values `r 0, ..., r (k-1)`. -/
def bsumV (q : Value) (r : Nat → Value) : Nat → Value
  | 0 => q
  | k + 1 => addV (bsumV q r k) (r k)

/-- The `f32` constant `0f45800000` (`4096`), moved to a register. -/
abbrev c4096w : Value := b32 1166016512

/-- The `f32` constant `0f358637BD` (`eps`). -/
abbrev epsw : Value := b32 897988541

/-- `div.approx.ftz.f32` of a total by `4096`. -/
def divV (T : Value) : Value := okVal (b32 0) (approxE (divI true) [T, c4096w])

/-- The scale factor of a total: `rsqrt.approx.ftz.f32` of the mean plus `eps`. -/
def rrV (T : Value) : Value := okVal (b32 0) (approxE (rsqrtI true) [addV (divV T) epsw])

/-- The pair of scale factors (`mov.b64 d, {r, r}`). -/
def cpair (T : Value) : Value := joinValue (rrV T) (rrV T)

/-- Pair `j` of the reloaded inputs (`mov.b64 d, {a, b}`): the first two from `r0`, the last two
from `r1`. -/
def pw (r0 r1 : List Value) (j : Nat) : Value :=
  match j with
  | 0 => joinValue (r0.getD 0 (b32 0)) (r0.getD 1 (b32 0))
  | 1 => joinValue (r0.getD 2 (b32 0)) (r0.getD 3 (b32 0))
  | 2 => joinValue (r1.getD 0 (b32 0)) (r1.getD 1 (b32 0))
  | _ => joinValue (r1.getD 2 (b32 0)) (r1.getD 3 (b32 0))

/-- Pair `j` of the reloaded inputs times the scale factors, and its two lanes. -/
def mm1 (r0 r1 : List Value) (c : Value) (j : Nat) : Value := mulV (pw r0 r1 j) c
def ml1 (r0 r1 : List Value) (c : Value) (j : Nat) : Value := (splitValue 64 (mm1 r0 r1 c j)).1
def mh1 (r0 r1 : List Value) (c : Value) (j : Nat) : Value := (splitValue 64 (mm1 r0 r1 c j)).2

/-- Those lanes times the pair `j` of widened weights `w`, and its two lanes. -/
def mm2 (w r0 r1 : List Value) (c : Value) (j : Nat) : Value :=
  mulV (joinValue (ml1 r0 r1 c j) (mh1 r0 r1 c j)) (joinValue (xw w (2 * j)) (xw w (2 * j + 1)))
def ml2 (w r0 r1 : List Value) (c : Value) (j : Nat) : Value := (splitValue 64 (mm2 w r0 r1 c j)).1
def mh2 (w r0 r1 : List Value) (c : Value) (j : Nat) : Value := (splitValue 64 (mm2 w r0 r1 c j)).2

/-- Output pair `j` of a tile: the two products converted to halves (`cvt.rn.f16x2.f32`). -/
def outV (w r0 r1 : List Value) (c : Value) (j : Nat) : Value :=
  cvtPairV (mh2 w r0 r1 c j) (ml2 w r0 r1 c j)

/-- The `f32` literal `0f45800000` as a real (`4096`). -/
def c4096 : ℝ := (((f32Value 1166016512).getD 0 : ℚ) : ℝ)

/-- The scale factor `1 / sqrt(total / 4096 + eps)` of a total. -/
def rms (tt : ℝ) : ℝ := 1 / Real.sqrt (tt / c4096 + eps)

/-! ### Widths of the outcomes -/

theorem addV_bytes (x y : Value) : (addV x y).bytes = 4 := okVal_bytes (floatE_add_four _ _)
theorem fmaV_bytes (x z : Value) : (fmaV x z).bytes = 4 := okVal_bytes (floatE_fma_four _ _ _)
theorem xw_bytes (ws : List Value) (k : Nat) : (xw ws k).bytes = 4 := okVal_bytes (widenE_four _)
theorem divV_bytes (T : Value) : (divV T).bytes = 4 := okVal_bytes (approxE_four rfl _)
theorem rrV_bytes (T : Value) : (rrV T).bytes = 4 := okVal_bytes (approxE_four rfl _)

theorem fmaRun_bytes (ws : List Value) {z : Value} (hz : z.bytes = 4) :
    ∀ n, (fmaRun ws n z).bytes = 4
  | 0 => hz
  | _ + 1 => fmaV_bytes _ _

theorem ssqV_bytes (d : D) : (ssqV d).bytes = 4 := fmaRun_bytes _ (fmaRun_bytes _ rfl 8) 8

theorem bsumV_bytes {q : Value} (hq : q.bytes = 4) (r : Nat → Value) :
    ∀ k, (bsumV q r k).bytes = 4
  | 0 => hq
  | _ + 1 => addV_bytes _ _

theorem mulV_pair (w c : Value) :
    ∃ a b, mulV w c = .pair a b ∧ a.bytes = 4 ∧ b.bytes = 4 := okVal_pair (floatE_mul2_pair4 _ _ _)

theorem outV_bytes (w r0 r1 : List Value) (c : Value) (j : Nat) : (outV w r0 r1 c j).bytes = 4 :=
  cvtPairV_bytes _ _

theorem mulV_lanes (w c : Value) : (splitValue 64 (mulV w c)).1.bytes = 4 ∧
    (splitValue 64 (mulV w c)).2.bytes = 4 := by
  obtain ⟨a, b, h, ha, hb⟩ := mulV_pair w c
  rw [h]; exact ⟨ha, hb⟩

/-- A packed product unpacks into its two lanes. -/
theorem unpackE_mulV (w c : Value) :
    (unpackE 64 (mulV w c)).toBool = true := by
  obtain ⟨a, b, h, ha, hb⟩ := mulV_pair w c
  rw [h, unpackE_pair ha hb]; rfl

theorem ml1_bytes (r0 r1 : List Value) (c : Value) (j : Nat) : (ml1 r0 r1 c j).bytes = 4 :=
  (mulV_lanes _ _).1
theorem mh1_bytes (r0 r1 : List Value) (c : Value) (j : Nat) : (mh1 r0 r1 c j).bytes = 4 :=
  (mulV_lanes _ _).2
theorem ml2_bytes (w r0 r1 : List Value) (c : Value) (j : Nat) : (ml2 w r0 r1 c j).bytes = 4 :=
  (mulV_lanes _ _).1
theorem mh2_bytes (w r0 r1 : List Value) (c : Value) (j : Nat) : (mh2 w r0 r1 c j).bytes = 4 :=
  (mulV_lanes _ _).2

/-! ### Register values -/

/-- The row of iteration `i`. -/
abbrev row (g i : Nat) : Nat := g / 256 + 152 * i

/-- The byte offset of the thread's tile-0 elements in a row-major `Bt × 4096` half array. -/
abbrev off (g i : Nat) : Nat := 2 * (4096 * row g i + 8 * (g % 256))

/-- The registers of an abstract state, by id. -/
def values (P : Params) (g : Nat) (d : D) : List (Nat × Value) :=
  let tid := g % 256
  let r := row g d.i
  let o := off g d.i
  let rw (k : Nat) := d.raw.getD k (b32 0)
  let r0 (k : Nat) := d.rs0.getD k (b32 0)
  let r1 (k : Nat) := d.rs1.getD k (b32 0)
  let c := cpair d.tt
  let w := d.raw
  [(283, b64 P.I), (284, b64 P.O), (285, b64 P.W), (45, b32 P.Bt),
   (42, b32 tid), (43, b32 (tid / 32)), (44, b32 (tid % 32)),
   (280, b32 r), (279, b32 (4096 * r + 8 * tid)),
   (2, .pred (decide (P.Bt ≤ g / 256))),
   (290, b64 (P.W + 16 * tid)), (313, b64 (P.W + 16 * tid + 4096)),
   (125, b32 (P.S + 4 * (tid / 32) + 16384)),
   (161, b32 (P.S + 32 * tid)), (166, b32 (P.S + 32 * tid + 16)),
   (219, b32 (P.S + 32 * tid + 8192)), (224, b32 (P.S + 32 * tid + 8208)),
   (3, .pred (decide (tid % 32 ≠ 0))),
   (287, b64 (P.I + o)), (289, b64 o), (288, b64 (P.I + o + 4096)),
   (53, d.xa.getD 0 (b32 0)), (54, d.xa.getD 1 (b32 0)), (55, d.xa.getD 2 (b32 0)),
   (56, d.xa.getD 3 (b32 0)),
   (9, halfOf d.xa 0), (10, halfOf d.xa 1), (11, halfOf d.xa 2), (12, halfOf d.xa 3),
   (13, halfOf d.xa 4), (14, halfOf d.xa 5), (15, halfOf d.xa 6), (16, halfOf d.xa 7),
   (57, xw d.xa 0), (58, xw d.xa 1), (59, xw d.xa 2), (60, xw d.xa 3),
   (61, xw d.xa 4), (62, xw d.xa 5), (63, xw d.xa 6), (64, xw d.xa 7),
   (65, xw d.xa 0), (66, xw d.xa 1), (67, xw d.xa 2), (68, xw d.xa 3),
   (69, xw d.xa 4), (70, xw d.xa 5), (71, xw d.xa 6), (72, xw d.xa 7),
   (110, fmaRun d.xa 1 z0), (111, fmaRun d.xa 2 z0), (112, fmaRun d.xa 3 z0),
   (113, fmaRun d.xa 4 z0), (114, fmaRun d.xa 5 z0), (115, fmaRun d.xa 6 z0),
   (116, fmaRun d.xa 7 z0), (117, fmaRun d.xa 8 z0),
   (73, d.xb.getD 0 (b32 0)), (74, d.xb.getD 1 (b32 0)), (75, d.xb.getD 2 (b32 0)),
   (76, d.xb.getD 3 (b32 0)),
   (17, halfOf d.xb 0), (18, halfOf d.xb 1), (19, halfOf d.xb 2), (20, halfOf d.xb 3),
   (21, halfOf d.xb 4), (22, halfOf d.xb 5), (23, halfOf d.xb 6), (24, halfOf d.xb 7),
   (77, xw d.xb 0), (78, xw d.xb 1), (79, xw d.xb 2), (80, xw d.xb 3),
   (81, xw d.xb 4), (82, xw d.xb 5), (83, xw d.xb 6), (84, xw d.xb 7),
   (85, xw d.xb 0), (86, xw d.xb 1), (87, xw d.xb 2), (88, xw d.xb 3),
   (89, xw d.xb 4), (90, xw d.xb 5), (91, xw d.xb 6), (92, xw d.xb 7),
   (118, fmaRun d.xb 1 (fmaRun d.xa 8 z0)), (119, fmaRun d.xb 2 (fmaRun d.xa 8 z0)),
   (120, fmaRun d.xb 3 (fmaRun d.xa 8 z0)), (121, fmaRun d.xb 4 (fmaRun d.xa 8 z0)),
   (122, fmaRun d.xb 5 (fmaRun d.xa 8 z0)), (123, fmaRun d.xb 6 (fmaRun d.xa 8 z0)),
   (124, fmaRun d.xb 7 (fmaRun d.xa 8 z0)),
   (94, ssqV d), (95, b32 16), (96, b32 31), (97, b32 4294967295),
   (99, bsumV (ssqV d) d.ra 1), (100, b32 8), (102, bsumV (ssqV d) d.ra 2), (103, b32 4),
   (105, bsumV (ssqV d) d.ra 3), (106, b32 2), (108, bsumV (ssqV d) d.ra 4), (109, b32 1),
   (126, bsumV (ssqV d) d.ra 5),
   (4, .pred (decide (31 < tid))), (127, b32 0), (128, b32 256),
   (5, .pred (decide (8 ≤ tid))),
   (281, d.u), (130, b32 (P.S + 4 * (tid % 32) + 16384)),
   (6, .pred (decide (tid % 32 ≠ 0))),
   (135, b32 16), (136, b32 31), (137, b32 4294967295),
   (139, bsumV d.u d.rb 1), (140, b32 8), (142, bsumV d.u d.rb 2), (143, b32 4),
   (145, bsumV d.u d.rb 3), (146, b32 2), (148, bsumV d.u d.rb 4), (149, b32 1),
   (151, bsumV d.u d.rb 5), (150, b32 (P.S + 16384)),
   (153, b32 0), (154, b32 256), (156, b32 (P.S + 16384)),
   (295, c),
   (167, rw 0), (170, rw 1), (173, rw 2), (176, rw 3),
   (157, r0 0), (158, r0 1), (159, r0 2), (160, r0 3),
   (162, r1 0), (163, r1 1), (164, r1 2), (165, r1 3),
   (25, halfOf w 0), (26, halfOf w 1), (27, halfOf w 2), (28, halfOf w 3),
   (29, halfOf w 4), (30, halfOf w 5), (31, halfOf w 6), (32, halfOf w 7),
   (168, xw w 0), (169, xw w 1), (171, xw w 2), (172, xw w 3),
   (174, xw w 4), (175, xw w 5), (177, xw w 6), (178, xw w 7),
   (292, pw d.rs0 d.rs1 0), (291, mm1 d.rs0 d.rs1 c 0),
   (180, ml1 d.rs0 d.rs1 c 0), (182, mh1 d.rs0 d.rs1 c 0),
   (179, ml1 d.rs0 d.rs1 c 0), (181, mh1 d.rs0 d.rs1 c 0),
   (294, pw d.rs0 d.rs1 1), (293, mm1 d.rs0 d.rs1 c 1),
   (184, ml1 d.rs0 d.rs1 c 1), (186, mh1 d.rs0 d.rs1 c 1),
   (183, ml1 d.rs0 d.rs1 c 1), (185, mh1 d.rs0 d.rs1 c 1),
   (297, pw d.rs0 d.rs1 2), (296, mm1 d.rs0 d.rs1 c 2),
   (188, ml1 d.rs0 d.rs1 c 2), (190, mh1 d.rs0 d.rs1 c 2),
   (187, ml1 d.rs0 d.rs1 c 2), (189, mh1 d.rs0 d.rs1 c 2),
   (299, pw d.rs0 d.rs1 3), (298, mm1 d.rs0 d.rs1 c 3),
   (192, ml1 d.rs0 d.rs1 c 3), (194, mh1 d.rs0 d.rs1 c 3),
   (191, ml1 d.rs0 d.rs1 c 3), (193, mh1 d.rs0 d.rs1 c 3),
   (301, joinValue (ml1 d.rs0 d.rs1 c 0) (mh1 d.rs0 d.rs1 c 0)),
   (302, joinValue (xw w 0) (xw w 1)), (300, mm2 w d.rs0 d.rs1 c 0),
   (195, ml2 w d.rs0 d.rs1 c 0), (196, mh2 w d.rs0 d.rs1 c 0),
   (204, ml2 w d.rs0 d.rs1 c 0), (203, mh2 w d.rs0 d.rs1 c 0),
   (304, joinValue (ml1 d.rs0 d.rs1 c 1) (mh1 d.rs0 d.rs1 c 1)),
   (305, joinValue (xw w 2) (xw w 3)), (303, mm2 w d.rs0 d.rs1 c 1),
   (197, ml2 w d.rs0 d.rs1 c 1), (198, mh2 w d.rs0 d.rs1 c 1),
   (206, ml2 w d.rs0 d.rs1 c 1), (205, mh2 w d.rs0 d.rs1 c 1),
   (307, joinValue (ml1 d.rs0 d.rs1 c 2) (mh1 d.rs0 d.rs1 c 2)),
   (308, joinValue (xw w 4) (xw w 5)), (306, mm2 w d.rs0 d.rs1 c 2),
   (199, ml2 w d.rs0 d.rs1 c 2), (200, mh2 w d.rs0 d.rs1 c 2),
   (208, ml2 w d.rs0 d.rs1 c 2), (207, mh2 w d.rs0 d.rs1 c 2),
   (310, joinValue (ml1 d.rs0 d.rs1 c 3) (mh1 d.rs0 d.rs1 c 3)),
   (311, joinValue (xw w 6) (xw w 7)), (309, mm2 w d.rs0 d.rs1 c 3),
   (201, ml2 w d.rs0 d.rs1 c 3), (202, mh2 w d.rs0 d.rs1 c 3),
   (210, ml2 w d.rs0 d.rs1 c 3), (209, mh2 w d.rs0 d.rs1 c 3),
   (211, outV w d.rs0 d.rs1 c 0), (212, outV w d.rs0 d.rs1 c 1),
   (213, outV w d.rs0 d.rs1 c 2), (214, outV w d.rs0 d.rs1 c 3), (312, b64 (P.O + o)),
   (225, rw 0), (228, rw 1), (231, rw 2), (234, rw 3),
   (215, r0 0), (216, r0 1), (217, r0 2), (218, r0 3),
   (220, r1 0), (221, r1 1), (222, r1 2), (223, r1 3),
   (33, halfOf w 0), (34, halfOf w 1), (35, halfOf w 2), (36, halfOf w 3),
   (37, halfOf w 4), (38, halfOf w 5), (39, halfOf w 6), (40, halfOf w 7),
   (226, xw w 0), (227, xw w 1), (229, xw w 2), (230, xw w 3),
   (232, xw w 4), (233, xw w 5), (235, xw w 6), (236, xw w 7),
   (315, pw d.rs0 d.rs1 0), (314, mm1 d.rs0 d.rs1 c 0),
   (238, ml1 d.rs0 d.rs1 c 0), (240, mh1 d.rs0 d.rs1 c 0),
   (237, ml1 d.rs0 d.rs1 c 0), (239, mh1 d.rs0 d.rs1 c 0),
   (317, pw d.rs0 d.rs1 1), (316, mm1 d.rs0 d.rs1 c 1),
   (242, ml1 d.rs0 d.rs1 c 1), (244, mh1 d.rs0 d.rs1 c 1),
   (241, ml1 d.rs0 d.rs1 c 1), (243, mh1 d.rs0 d.rs1 c 1),
   (319, pw d.rs0 d.rs1 2), (318, mm1 d.rs0 d.rs1 c 2),
   (246, ml1 d.rs0 d.rs1 c 2), (248, mh1 d.rs0 d.rs1 c 2),
   (245, ml1 d.rs0 d.rs1 c 2), (247, mh1 d.rs0 d.rs1 c 2),
   (321, pw d.rs0 d.rs1 3), (320, mm1 d.rs0 d.rs1 c 3),
   (250, ml1 d.rs0 d.rs1 c 3), (252, mh1 d.rs0 d.rs1 c 3),
   (249, ml1 d.rs0 d.rs1 c 3), (251, mh1 d.rs0 d.rs1 c 3),
   (323, joinValue (ml1 d.rs0 d.rs1 c 0) (mh1 d.rs0 d.rs1 c 0)),
   (324, joinValue (xw w 0) (xw w 1)), (322, mm2 w d.rs0 d.rs1 c 0),
   (253, ml2 w d.rs0 d.rs1 c 0), (254, mh2 w d.rs0 d.rs1 c 0),
   (262, ml2 w d.rs0 d.rs1 c 0), (261, mh2 w d.rs0 d.rs1 c 0),
   (326, joinValue (ml1 d.rs0 d.rs1 c 1) (mh1 d.rs0 d.rs1 c 1)),
   (327, joinValue (xw w 2) (xw w 3)), (325, mm2 w d.rs0 d.rs1 c 1),
   (255, ml2 w d.rs0 d.rs1 c 1), (256, mh2 w d.rs0 d.rs1 c 1),
   (264, ml2 w d.rs0 d.rs1 c 1), (263, mh2 w d.rs0 d.rs1 c 1),
   (329, joinValue (ml1 d.rs0 d.rs1 c 2) (mh1 d.rs0 d.rs1 c 2)),
   (330, joinValue (xw w 4) (xw w 5)), (328, mm2 w d.rs0 d.rs1 c 2),
   (257, ml2 w d.rs0 d.rs1 c 2), (258, mh2 w d.rs0 d.rs1 c 2),
   (266, ml2 w d.rs0 d.rs1 c 2), (265, mh2 w d.rs0 d.rs1 c 2),
   (332, joinValue (ml1 d.rs0 d.rs1 c 3) (mh1 d.rs0 d.rs1 c 3)),
   (333, joinValue (xw w 6) (xw w 7)), (331, mm2 w d.rs0 d.rs1 c 3),
   (259, ml2 w d.rs0 d.rs1 c 3), (260, mh2 w d.rs0 d.rs1 c 3),
   (268, ml2 w d.rs0 d.rs1 c 3), (267, mh2 w d.rs0 d.rs1 c 3),
   (269, outV w d.rs0 d.rs1 c 0), (270, outV w d.rs0 d.rs1 c 1),
   (271, outV w d.rs0 d.rs1 c 2), (272, outV w d.rs0 d.rs1 c 3),
   (334, b64 (P.O + o + 4096)),
   (273, b32 1), (7, .pred (decide (r < P.Bt)))]

def valueOf (P : Params) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values P g d).lookup r).getD (b32 0)

def factsAt (P : Params) (g pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf P g d)

abbrev facts (P : Params) (g : Nat) (d : D) : List (Nat × Value) :=
  factsAt P g d.site.pc d

/-! ### Transitions -/

/-- An element of a vector load: the element's bytes rebuild to a value, kept in `acc`; after the
last element `k` continues with the four values, or stops. Bytes that do not rebuild fault. -/
def loadNext (d : D) (e : Event) (k : List Value → Option D) : Option (Option D) :=
  match e.kind with
  | .rd _ bs => match rebuild 3 bs with
    | .ok v =>
      if d.sub + 1 < 4 then some (some { d with sub := d.sub + 1, acc := d.acc ++ [v] })
      else (k (d.acc ++ [v])).map some
    | .error _ => none
  | _ => none

/-- An element of a vector store; after the last element the thread continues at `d'`. -/
def storeNext (d d' : D) : Option (Option D) :=
  if d.sub + 1 < 4 then some (some { d with sub := d.sub + 1 }) else some (some d')

/-- The words `ws` of a tile unpack into halves that widen, and the fused multiply-adds of the
squares onto `z` do not fault: the input loads' code (`unpackE`, `widenE`, `floatE`). -/
def xOk (ws : List Value) (z : Value) : Bool :=
    (unpackE 32 (ws.getD 0 (b32 0))).toBool && (widenE (halfOf ws 0)).toBool &&
      (widenE (halfOf ws 1)).toBool &&
    (unpackE 32 (ws.getD 1 (b32 0))).toBool && (widenE (halfOf ws 2)).toBool &&
      (widenE (halfOf ws 3)).toBool &&
    (unpackE 32 (ws.getD 2 (b32 0))).toBool && (widenE (halfOf ws 4)).toBool &&
      (widenE (halfOf ws 5)).toBool &&
    (unpackE 32 (ws.getD 3 (b32 0))).toBool && (widenE (halfOf ws 6)).toBool &&
      (widenE (halfOf ws 7)).toBool &&
    (floatE (fmaI .rn true) [xw ws 0, xw ws 0, fmaRun ws 0 z]).toBool &&
    (floatE (fmaI .rn true) [xw ws 1, xw ws 1, fmaRun ws 1 z]).toBool &&
    (floatE (fmaI .rn true) [xw ws 2, xw ws 2, fmaRun ws 2 z]).toBool &&
    (floatE (fmaI .rn true) [xw ws 3, xw ws 3, fmaRun ws 3 z]).toBool &&
    (floatE (fmaI .rn true) [xw ws 4, xw ws 4, fmaRun ws 4 z]).toBool &&
    (floatE (fmaI .rn true) [xw ws 5, xw ws 5, fmaRun ws 5 z]).toBool &&
    (floatE (fmaI .rn true) [xw ws 6, xw ws 6, fmaRun ws 6 z]).toBool &&
    (floatE (fmaI .rn true) [xw ws 7, xw ws 7, fmaRun ws 7 z]).toBool

/-- The weight words `w` unpack into halves that widen. -/
def tileW (w : List Value) : Bool :=
    (unpackE 32 (w.getD 0 (b32 0))).toBool && (widenE (halfOf w 0)).toBool &&
      (widenE (halfOf w 1)).toBool &&
    (unpackE 32 (w.getD 1 (b32 0))).toBool && (widenE (halfOf w 2)).toBool &&
      (widenE (halfOf w 3)).toBool &&
    (unpackE 32 (w.getD 2 (b32 0))).toBool && (widenE (halfOf w 4)).toBool &&
      (widenE (halfOf w 5)).toBool &&
    (unpackE 32 (w.getD 3 (b32 0))).toBool && (widenE (halfOf w 6)).toBool &&
      (widenE (halfOf w 7)).toBool

/-- The reloaded pairs `r0`, `r1` pack and multiply with the pair `c` of scale factors. -/
def tileP (r0 r1 : List Value) (c : Value) : Bool :=
    (packE (r0.getD 0 (b32 0)) (r0.getD 1 (b32 0))).toBool &&
    (floatE (mul2I .rz true) [pw r0 r1 0, c]).toBool &&
    (packE (r0.getD 2 (b32 0)) (r0.getD 3 (b32 0))).toBool &&
    (floatE (mul2I .rz true) [pw r0 r1 1, c]).toBool &&
    (packE (r1.getD 0 (b32 0)) (r1.getD 1 (b32 0))).toBool &&
    (floatE (mul2I .rz true) [pw r0 r1 2, c]).toBool &&
    (packE (r1.getD 2 (b32 0)) (r1.getD 3 (b32 0))).toBool &&
    (floatE (mul2I .rz true) [pw r0 r1 3, c]).toBool

/-- The products multiply with the pairs of widened weights. -/
def tileQ (w r0 r1 : List Value) (c : Value) : Bool :=
    (floatE (mul2I .rz true) [joinValue (ml1 r0 r1 c 0) (mh1 r0 r1 c 0),
      joinValue (xw w 0) (xw w 1)]).toBool &&
    (floatE (mul2I .rz true) [joinValue (ml1 r0 r1 c 1) (mh1 r0 r1 c 1),
      joinValue (xw w 2) (xw w 3)]).toBool &&
    (floatE (mul2I .rz true) [joinValue (ml1 r0 r1 c 2) (mh1 r0 r1 c 2),
      joinValue (xw w 4) (xw w 5)]).toBool &&
    (floatE (mul2I .rz true) [joinValue (ml1 r0 r1 c 3) (mh1 r0 r1 c 3),
      joinValue (xw w 6) (xw w 7)]).toBool

/-- The results convert to pairs of halves. -/
def tileC (w r0 r1 : List Value) (c : Value) : Bool :=
    (cvtPairE (mh2 w r0 r1 c 0) (ml2 w r0 r1 c 0)).toBool &&
    (cvtPairE (mh2 w r0 r1 c 1) (ml2 w r0 r1 c 1)).toBool &&
    (cvtPairE (mh2 w r0 r1 c 2) (ml2 w r0 r1 c 2)).toBool &&
    (cvtPairE (mh2 w r0 r1 c 3) (ml2 w r0 r1 c 3)).toBool

/-- The weight words `w` widen, the reloaded pairs `r0`, `r1` pack and multiply with the pair `c`
of scale factors, the products multiply with the weights, and the results convert to halves. -/
def tileOk (w r0 r1 : List Value) (c : Value) : Bool :=
  tileW w && tileP r0 r1 c && tileQ w r0 r1 c && tileC w r0 r1 c

/-- The total `T` divides by `4096`, adds `eps` and has an inverse square root. -/
def ttOk (T : Value) : Bool :=
  (approxE (divI true) [T, c4096w]).toBool && (floatE (addI true) [divV T, epsw]).toBool &&
    (approxE (rsqrtI true) [addV (divV T) epsw]).toBool

/-- The successor after a received butterfly value `y` in round `k`. -/
def bfaNext (g : Nat) (d : D) (k : Nat) (y : Value) : D :=
  let d' := { d with ra := Function.update d.ra k y }
  if k + 1 < 5 then { d' with site := .bfa (k + 1) }
  else if g % 256 % 32 = 0 then { d' with site := .stws } else { d' with site := .bar0 }

/-- The successor after warp 0's received value `y` in round `k`. -/
def bfbNext (g : Nat) (d : D) (k : Nat) (y : Value) : D :=
  let d' := { d with rb := Function.update d.rb k y }
  if k + 1 < 5 then { d' with site := .bfb (k + 1) }
  else if g % 256 = 0 then { d' with site := .stts } else { d' with site := .bar1 }

/-- The output stores of tile 0 after its second reload `vs`. -/
def tileA (d : D) (vs : List Value) : D := { d with site := .stoa, sub := 0, acc := [], rs1 := vs }

/-- The output stores of tile 1 after its second reload `vs`. -/
def tileB (d : D) (vs : List Value) : D := { d with site := .stob, sub := 0, acc := [], rs1 := vs }

def next (P : Params) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .shfl0 =>
    if g / 256 < P.Bt then some (some { d with site := .ldxa, i := 0 })
    else some (some { d with site := .exit })
  | .ldxa => loadNext d e fun vs =>
      if xOk vs z0 then some { d with site := .stxa0, sub := 0, acc := [], xa := vs } else none
  | .stxa0 => storeNext d { d with site := .stxa1, sub := 0 }
  | .stxa1 => storeNext d { d with site := .ldxb, sub := 0 }
  | .ldxb => loadNext d e fun vs =>
      if xOk vs (fmaRun d.xa 8 z0) then
        some { d with site := .stxb0, sub := 0, acc := [], xb := vs }
      else none
  | .stxb0 => storeNext d { d with site := .stxb1, sub := 0 }
  | .stxb1 => storeNext d { d with site := .bfa 0, sub := 0 }
  | .bfa k =>
    match e.kind with
    | .shfl _ _ _ _ recv _ =>
      if (floatE (addI true) [bsumV (ssqV d) d.ra k, recv]).toBool then
        some (some (bfaNext g d k recv))
      else none
    | _ => none
  | .stws => some (some { d with site := .bar0 })
  | .bar0 =>
    if 31 < g % 256 then some (some { d with site := .bar1 })
    else if g % 256 < 8 then some (some { d with site := .ldws })
    else some (some { d with site := .bfb 0, u := b32 0 })
  | .ldws =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => if v.bytes = 4 then some (some { d with site := .bfb 0, u := v }) else none
      | .error _ => none
    | _ => none
  | .bfb k =>
    match e.kind with
    | .shfl _ _ _ _ recv _ =>
      if (floatE (addI true) [bsumV d.u d.rb k, recv]).toBool then
        some (some (bfbNext g d k recv))
      else none
    | _ => none
  | .stts => some (some { d with site := .bar1 })
  | .bar1 => some (some { d with site := .ldts })
  | .ldts =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => if ttOk v then some (some { d with site := .ldwa, tt := v, raw := [] }) else none
      | .error _ => none
    | _ => none
  | .ldwa => loadNext d e fun vs => some { d with site := .ldsa0, sub := 0, acc := [], raw := vs }
  | .ldsa0 => loadNext d e fun vs => some { d with site := .ldsa1, sub := 0, acc := [], rs0 := vs }
  | .ldsa1 => loadNext d e fun vs =>
      if tileOk d.raw d.rs0 vs (cpair d.tt) then some (tileA d vs) else none
  | .stoa => storeNext d { d with site := .ldwb, sub := 0, raw := [] }
  | .ldwb => loadNext d e fun vs => some { d with site := .ldsb0, sub := 0, acc := [], raw := vs }
  | .ldsb0 => loadNext d e fun vs => some { d with site := .ldsb1, sub := 0, acc := [], rs0 := vs }
  | .ldsb1 => loadNext d e fun vs =>
      if tileOk d.raw d.rs0 vs (cpair d.tt) then some (tileB d vs) else none
  | .stob => storeNext d { d with site := .bar2, sub := 0 }
  | .bar2 =>
    if row g (d.i + 1) < P.Bt then some (some { d with site := .ldxa, i := d.i + 1 })
    else some (some { d with site := .exit, i := d.i + 1 })
  | .exit => none

/-! ### The invariant -/

structure Inv (P : Params) (g : Nat) (d : D) : Prop where
  /-- A vector access is at one of its four elements, any other site at none. -/
  sub : (d.site.vec = true → d.sub < 4) ∧ (d.site.vec = false → d.sub = 0)
  /-- A vector load has read the elements before `sub`; no other site holds read values. -/
  acc : d.acc.length = if d.site.vload then d.sub else 0
  /-- A site of a row iteration is in a row of the batch; the exit is past the last row. -/
  row : d.site.inRow = true → row g d.i < P.Bt
  exit : d.site = .exit → P.Bt ≤ g / 256 + 152 * d.i
  /-- The butterfly rounds. -/
  bfa : ∀ k, d.site = .bfa k → k < 5
  bfb : ∀ k, d.site = .bfb k → k < 5 ∧ g % 256 < 32
  /-- The threads of warp 0's reduction. -/
  ldws : d.site = .ldws → g % 256 < 8
  stts : d.site = .stts → g % 256 = 0
  stws : d.site = .stws → g % 256 % 32 = 0
  /-- Warp 0's loaded value is an operand of the shuffle. -/
  u : d.site = .bfb 0 → d.u.bytes = 4
  /-- The raw values of the vector loads before the conversions. -/
  raw : (d.site = .ldsa0 ∨ d.site = .ldsb0 → d.raw.length = 4) ∧
    (d.site = .ldsa1 ∨ d.site = .ldsb1 → d.raw.length = 4 ∧ d.rs0.length = 4)

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

/-- Thread `g` as a site machine. -/
def code (P : Params) (L : Launch) (g : Nat) : Flow.Code kernel Prod L g where
  D := D
  init := { site := .shfl0 }
  pc := fun d => d.site.pc
  facts := facts P g
  sub := D.sub
  acc := D.acc
  inv := Inv P g
  next := next P g

/-- The kernel's ideal assumption reads each of its floating forms as exact arithmetic. -/
theorem ideal_add : Assumption.IdealFor Prod (.add .f32) := by
  unfold Assumptions.idealArith; exact Assumption.idealFor_head (by decide)

theorem ideal_mul2 : Assumption.IdealFor Prod .mulF32x2 := by
  unfold Assumptions.idealArith; exact Assumption.idealFor_head (by decide)

theorem ideal_widen : Assumption.IdealFor Prod .cvtF32F16 := by
  unfold Assumptions.idealArith; exact Assumption.idealFor_head (by decide)

theorem ideal_cvt : Assumption.IdealFor Prod .cvtRnF16x2F32 := by
  unfold Assumptions.idealArith; exact Assumption.idealFor_head (by decide)

/-- No assumption of the kernel has a local rule for an operation that is neither a floating nor
an approximate form: the Core rule applies. -/
theorem localRule_none {op : Op} (hf : Assumption.FloatForm.ofOp op = none)
    (ha : Assumption.ApproxForm.ofOp op = none) (L : Launch) (g : Nat) (t : TState) :
    ∀ a ∈ Prod, a.localRule L g t op = none := by
  intro a ha'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
  rcases ha' with rfl | rfl
  · exact Assumption.idealReal_localRule_none fun f hf' => by rw [hf] at hf'; cases hf'
  · exact Assumption.approxExact_localRule_none fun f ha' => by rw [ha] at ha'; cases ha'

/-- No assumption of the kernel has a local rule for a branch: the Core rule applies. -/
theorem localRule_bra (L : Launch) (g : Nat) (t : TState) (target : Nat) (uni : Bool) :
    ∀ a ∈ Prod, a.localRule L g t (.bra target uni) = none :=
  localRule_none (by simp [Assumption.FloatForm.ofOp]) (by simp [Assumption.ApproxForm.ofOp])
    L g t

/-- No assumption of the kernel names the unpack of a word into two halves. -/
theorem noUnpack : Flow.NoUnpack Prod := fun lo hi src L g t =>
  localRule_none (op := .move ⟨.unpack, .int .b 32, [some lo, some hi], [.reg src]⟩)
    (by simp [Assumption.FloatForm.ofOp]) (by simp [Assumption.ApproxForm.ofOp]) L g t

/-- No assumption of the kernel names the pack of two words into one. -/
theorem noPack : Flow.NoPack Prod := fun d a b L g t =>
  localRule_none (op := .move ⟨.pack, .int .b 64, [some d], [.reg a, .reg b]⟩)
    (by simp [Assumption.FloatForm.ofOp]) (by simp [Assumption.ApproxForm.ofOp]) L g t

/-- The kernel's ideal assumption leaves a floating instruction it declines (a NaN or infinite
operand) to the Core rule: the approximate-as-exact assumption names no floating form. -/
theorem decline {f : Assumption.FloatForm} : Assumption.DeclineCore Prod f := by
  unfold Assumptions.idealArith
  refine Assumption.declineCore_head (fun a ha L g t op hf => ?_)
  simp only [List.mem_singleton] at ha
  subst ha
  exact Assumption.approxExact_localRule_none fun f' hf' => by
    rw [approxForm_none_of_float hf] at hf'; cases hf'

theorem ideal_fma : Assumption.IdealFor Prod (.fma .f32) := by
  unfold Assumptions.idealArith; exact Assumption.idealFor_head (by decide)

/-- The kernel's approximate-as-exact assumption reads `div.approx` and `rsqrt.approx` as exact
functions and leaves their infinite or NaN operands to the Core rule. -/
theorem approx {f : Assumption.ApproxForm} (hf : f ∈ [.div .f32, .rsqrt .f32]) :
    ApproxFor Prod f ∧ ApproxDecline Prod f :=
  approx_of_rules (by hooks_off) fun L g t op hop => by
    simp only [List.findSome?_cons, List.findSome?_nil, Assumptions.idealArith,
      Assumptions.exactApprox]
    rw [Assumption.idealReal_localRule_none fun f' hf' => by
      rw [floatForm_none_of_approx hop] at hf'; cases hf']
    simp only [Assumption.approxExact_localRule_of hop hf]
    cases Assumption.execApproxExact t op <;> rfl

/-- No assumption of the kernel names a move. -/
theorem coreMoves : CoreMoves Prod := fun m L g t =>
  localRule_none (op := .move m) (by simp [Assumption.FloatForm.ofOp])
    (by simp [Assumption.ApproxForm.ofOp]) L g t

end
end PTX.Kernels.RmsNorm.Proof
