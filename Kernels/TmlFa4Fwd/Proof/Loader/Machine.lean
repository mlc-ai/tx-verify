-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.SchedWords

@[expose] public section

/-! # The loader warps as a site machine

Warps 14 and 15 run from their `setmaxnreg` (pc 179) to the `ret` (pc 9205). A lane picks its
CTA's tile by the persistent scheduler's first pass, exactly as the output and MMA warps (`word`
… `tiles`, the same arithmetic on other registers, recorded in an `Epilogue.D`), reads the
request's offsets and used-K length (`q0`, `q1`, `uk`) and loads the tile's K/V blocks from the
paged cache into the three-slot ring, from the last block to the first.

Every block is loaded the same way, in one of three periods (`Per`): the first block (`prime`),
the next blocks while the Bias still has columns (`warm`, at most nine rounds, with the Bias
loads of warp 14) and the remaining blocks (`steady`). A period's block is: two rounds of the
page-table loop (`pgLd` reads the page index when the row is inside the used length, `pgSt` and
`rwSt` save the page and the row in local memory), then for the K half and the V half
(`v = false, true`) of the block: the wait for an empty ring slot (`slot`), two rounds of the
pointer loop (`ptP`, `ptR` read the page and row back, `ptS` saves the row's address), and the
packet: per half of the rows a two-word local load of a row address (`lw`, sub-steps 0 and 1),
and per row the shuffle of the address's two words from its lane in the group of eight (`xl`,
`xh`) and two 16-byte asynchronous copies (`cp`); then the commit and the arrival on the slot's
full barrier (`commit`, `arrive`). Warp 14 also loads Q and the Bias by TMA in seven groups
(`tw`: the wait for the empty stage, `te`: three elections, `ta`: the elected lane's
expect-tx arrival, `tc`: its two tensor copies): four in the first block, two per warm round,
one after the warm rounds. After the last block the scheduler's second pass finds no further
tile; the lane waits until the consumers emptied all three slots (`dw`), warp 14 waits for the
second Q stage and arrives on its full barrier (`dq`, `de`, `da`), and the lane returns
(`exit`).

The machine follows every value an event returns: a load or shuffle of a 32-bit word records
the word, and a value of another kind stops the machine (`some none`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 add32 addi sub32 mul32 mad32 min32 shrs shru
  andi scmp scmpi sel addrU addrS xor32 not32 shl popc sdiv divOk fdiv Scan laneW ctaW paramW
  batchOf skipFirst reqOf skipLoop tlOf prefixD headsW lanePreds partials loopRegs chosen
  loopOf tilesOf)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ori ceil128 sbW sbi w32 neg32)

noncomputable section

/-! ### Arithmetic of the code that the other roles do not use -/

abbrev or32 (x y : BitVec 64) : BitVec 64 := r32 x ||| r32 y
abbrev max32 (x y : BitVec 64) : BitVec 64 :=
  if PTX.compare .gt .s 32 (r32 x) (r32 y) then r32 x else r32 y

/-- The warp index as the loader's code reads it. -/
abbrev warpW (w : Nat) : BitVec 64 := BitVec.ofNat 64 w

/-- Whether the warp is not warp 14 (`%p121`): warp 14 also loads Q and the Bias. -/
abbrev not14 (w : Nat) : Bool := scmpi .ne .b (warpW w) 14

/-- The next ring slot after `s`, and the parity after it. -/
abbrev nslot (s : BitVec 64) : BitVec 64 := sel (scmpi .eq .b (addi s 1) 3) (i32 0) (addi s 1)
abbrev npar (s q : BitVec 64) : BitVec 64 :=
  xor32 q (sel (scmpi .eq .b (addi s 1) 3) (i32 1) (i32 0))

/-! ### Sites -/

/-- The period of a block: the first block, the warm rounds with Bias loads, the rest. -/
inductive Per where
  | prime | warm | steady
  deriving DecidableEq

/-- The packet of a period's K (`v = false`) or V half. -/
def pk : Per → Bool → Nat
  | .prime, false => 0 | .prime, true => 1
  | .warm, false => 2 | .warm, true => 3
  | .steady, false => 4 | .steady, true => 5

inductive Site where
  | setmax
  | word (k : Scan)
  | down (k : Scan)
  | up (k : Scan) (j : Fin 5)
  | total (k : Scan)
  | vote (late : Bool)
  | pre (late : Bool)
  | tiles (late : Bool)
  | q0 | q1 | uk
  /-- Round `it` of a period's page-table loop: the page index, the page store, the row store. -/
  | pgLd (per : Per) (it : Fin 2)
  | pgSt (per : Per) (it : Fin 2)
  | rwSt (per : Per) (it : Fin 2)
  /-- The wait for an empty slot before half `v` of a period's block. -/
  | slot (per : Per) (v : Bool)
  /-- Round `it` of the pointer loop: the page and row loads, the address store. -/
  | ptP (per : Per) (v : Bool) (it : Fin 2)
  | ptR (per : Per) (v : Bool) (it : Fin 2)
  | ptS (per : Per) (v : Bool) (it : Fin 2)
  /-- The packet: the address load of half `h` of the rows, per row `i` the two shuffles and
  the two copies, the commit and the arrival. -/
  | lw (per : Per) (v : Bool) (h : Fin 2)
  | xl (per : Per) (v : Bool) (i : Fin 16)
  | xh (per : Per) (v : Bool) (i : Fin 16)
  | cp (per : Per) (v : Bool) (i : Fin 16) (c : Fin 2)
  | commit (per : Per) (v : Bool)
  | arrive (per : Per) (v : Bool)
  /-- TMA group `t` of warp 14: the wait, the three elections, the arrival, the two copies. -/
  | tw (t : Fin 7)
  | te (t : Fin 7) (e : Fin 3)
  | ta (t : Fin 7)
  | tc (t : Fin 7) (c : Fin 2)
  /-- The drain: the three slot waits, warp 14's Q wait, election and arrival, the return. -/
  | dw (k : Fin 3)
  | dq | de | da
  | exit
  deriving DecidableEq

/-- The program counters of the packets' address loads, first shuffles and first copies. -/
def lwPc (k : Nat) (h : Fin 2) : Nat :=
  ([[543, 609], [804, 854], [1003, 1072], [1238, 1292], [1469, 1537], [1632, 1685]].getD k [])
    |>.getD h.val 0
def xlPc (k : Nat) (i : Fin 16) : Nat :=
  ([[544, 553, 561, 569, 577, 585, 593, 601, 610, 618, 626, 634, 642, 650, 658, 666],
    [805, 812, 818, 824, 830, 836, 842, 848, 855, 861, 867, 873, 879, 885, 891, 897],
    [1004, 1015, 1024, 1032, 1040, 1048, 1056, 1064, 1073, 1081, 1089, 1097, 1105, 1113, 1121,
      1129],
    [1239, 1249, 1256, 1262, 1268, 1274, 1280, 1286, 1293, 1299, 1305, 1311, 1317, 1323, 1329,
      1335],
    [1470, 1480, 1489, 1497, 1505, 1513, 1521, 1529, 1538, 1546, 1554, 1562, 1570, 1578, 1586,
      1594],
    [1633, 1642, 1649, 1655, 1661, 1667, 1673, 1679, 1686, 1692, 1698, 1704, 1710, 1716, 1722,
      1728]].getD k []).getD i.val 0
def cpPc (k : Nat) (i : Fin 16) : Nat :=
  ([[550, 558, 566, 574, 582, 590, 598, 606, 615, 623, 631, 639, 647, 655, 663, 671],
    [810, 816, 822, 828, 834, 840, 846, 852, 859, 865, 871, 877, 883, 889, 895, 901],
    [1012, 1021, 1029, 1037, 1045, 1053, 1061, 1069, 1078, 1086, 1094, 1102, 1110, 1118, 1126,
      1134],
    [1247, 1254, 1260, 1266, 1272, 1278, 1284, 1290, 1297, 1303, 1309, 1315, 1321, 1327, 1333,
      1339],
    [1477, 1486, 1494, 1502, 1510, 1518, 1526, 1534, 1543, 1551, 1559, 1567, 1575, 1583, 1591,
      1599],
    [1640, 1647, 1653, 1659, 1665, 1671, 1677, 1683, 1690, 1696, 1702, 1708, 1714, 1720, 1726,
      1732]].getD k []).getD i.val 0

/-- The program counters of a TMA group: the wait, the elections, the arrival, the copies. -/
def twPc (t : Fin 7) : Nat := [679, 704, 730, 756, 1146, 1175, 1361].getD t.val 0
def tePc (t : Fin 7) (e : Fin 3) : Nat :=
  ([[682, 687, 694], [707, 712, 720], [733, 738, 746], [759, 765, 772], [1149, 1154, 1164],
    [1178, 1183, 1192], [1364, 1370, 1377]].getD t.val []).getD e.val 0
def taPc (t : Fin 7) : Nat := [686, 711, 737, 763, 1153, 1182, 1368].getD t.val 0
def tcPc (t : Fin 7) (c : Fin 2) : Nat :=
  ([[693, 700], [719, 727], [745, 753], [771, 779], [1163, 1173], [1191, 1200],
    [1376, 1383]].getD t.val []).getD c.val 0

def Site.pc : Site → Nat
  | .setmax => 179
  | .word k => match k with | .first => 186 | .loop => 245 | .second => 1750 | .loop2 => 1805
  | .down k => match k with | .first => 187 | .loop => 247 | .second => 1751 | .loop2 => 1807
  | .up k j => match k with
    | .first => 206 + 4 * j.val | .loop => 268 + 3 * j.val
    | .second => 1771 + 3 * j.val | .loop2 => 1828 + 3 * j.val
  | .total k => match k with | .first => 226 | .loop => 283 | .second => 1786 | .loop2 => 1843
  | .vote l => if l then 1855 else 297
  | .pre l => if l then 1860 else 304
  | .tiles l => if l then 1861 else 308
  | .q0 => 381
  | .q1 => 382
  | .uk => 385
  | .pgLd per _ => match per with | .prime => 503 | .warm => 946 | .steady => 1416
  | .pgSt per _ => match per with | .prime => 506 | .warm => 949 | .steady => 1419
  | .rwSt per _ => match per with | .prime => 511 | .warm => 953 | .steady => 1423
  | .slot per v => [517, 782, 960, 1206, 1430, 1611].getD (pk per v) 0
  | .ptP per v _ => [525, 790, 968, 1214, 1438, 1619].getD (pk per v) 0
  | .ptR per v _ => [527, 792, 970, 1216, 1440, 1621].getD (pk per v) 0
  | .ptS per v _ => [534, 799, 977, 1223, 1447, 1628].getD (pk per v) 0
  | .lw per v h => lwPc (pk per v) h
  | .xl per v i => xlPc (pk per v) i
  | .xh per v i => xlPc (pk per v) i + 1
  | .cp per v i c => cpPc (pk per v) i + c.val
  | .commit per v => [673, 903, 1136, 1341, 1601, 1734].getD (pk per v) 0
  | .arrive per v => [674, 904, 1137, 1342, 1602, 1735].getD (pk per v) 0
  | .tw t => twPc t
  | .te t e => tePc t e
  | .ta t => taPc t
  | .tc t c => tcPc t c
  | .dw k => [1866, 1877, 1888].getD k.val 0
  | .dq => 1893
  | .de => 1896
  | .da => 1900
  | .exit => 9205

/-! ### States -/

/-- The chosen request's coordinates as the loader computes them: the Q row offset `%r6108` and
the head `%r6109`, and the operands of its two divisions. -/
structure Coords where
  row : BitVec 64
  head : BitVec 64
  n1 : BitVec 64
  d1 : BitVec 64
  n2 : BitVec 64
  d2 : BitVec 64

/-- The setup's words: the head as the K/V offset's factor (`%r751`), the K/V head bases
(`%rd12`, `%rd13`), the page-table row of the request (`%rd11`), the blocks (`%r28`), the
blocks the Bias leaves out (`%r29`). -/
structure Setup where
  r741 : BitVec 64
  r748 : BitVec 64
  p109 : Bool
  r751 : BitVec 64
  rd9 : BitVec 64
  rd11 : BitVec 64
  rd12 : BitVec 64
  rd13 : BitVec 64
  r755 : BitVec 64
  p112 : Bool
  r758 : BitVec 64
  r760 : BitVec 64
  r761 : BitVec 64
  r765 : BitVec 64
  p115 : Bool
  r28 : BitVec 64
  r769 : BitVec 64
  r773 : BitVec 64
  p118 : Bool
  r29 : BitVec 64
  p119 : Bool
  r31 : BitVec 64
  r32 : BitVec 64
  r778 : BitVec 64
  r35 : BitVec 64

/-- The values a state records. -/
structure V where
  /-- The scheduler's scan: the words its events returned and its loop state (its `site` is
  not read), and the request's two offsets (`c0`, `c1`). -/
  sc : Epilogue.D := { site := .start }
  /-- The request's used-K length. -/
  ukw : BitVec 64 := 0
  /-- The page index of the page-table round (zero for a row past the used length). -/
  pw : BitVec 64 := 0
  /-- The page and row a pointer round read back. -/
  lp : BitVec 64 := 0
  lr : BitVec 64 := 0
  /-- The two words of the row address a packet's half loaded. -/
  l0 : BitVec 64 := 0
  l1 : BitVec 64 := 0
  /-- The two words of the current row's address that the shuffles returned. -/
  x0 : BitVec 64 := 0
  x1 : BitVec 64 := 0
  /-- The round of the warm (`%r6114`) or steady (`%r6121`) loop, the ring slot (`%r6119`) and
  its parity (`%r6120`), the parities of the two Bias stages (`%r6117`, `%r6118`) and of the
  second Q stage at the drain (`%r6132`). -/
  rnd : BitVec 64 := 0
  slot : BitVec 64 := 0
  par : BitVec 64 := 0
  bq0 : BitVec 64 := 0
  bq1 : BitVec 64 := 0
  qp : BitVec 64 := 0
  /-- The rows of a warm or steady block that its packets load (`%r937`, `%r1095`), recorded at
  the code's `selp` on whether the block starts before the first row. -/
  len : BitVec 64 := 0
  /-- The later blocks' first block less one (`%r56`, the tile's blocks less two), recorded at
  the end of the first block: the warm and steady rows are offsets from it. -/
  r56 : BitVec 64 := 0
  /-- The chosen request's coordinates (recorded after the scan) and the tile's setup words
  (recorded after the used-K read): functions of the recorded words, kept as fields so that the
  later sites' terms are small. -/
  co : Coords := ⟨0, 0, 0, 0, 0, 0⟩
  su : Setup := ⟨0, 0, false, 0, 0, 0, 0, 0, 0, false, 0, 0, 0, 0, false, 0, 0, 0, false, 0, false,
    0, 0, 0, 0⟩

structure D where
  site : Site
  v : V
  /-- The sub-step: 1 between the two elements of an address load. -/
  k : Fin 2 := 0

/-- A state at sub-step 0. -/
abbrev D.mk' (s : Site) (v : V) : D := ⟨s, v, 0⟩

/-- A conditional successor (both branches at sub-step 0). -/
abbrev D.ite (c : Bool) (a b : D) : D := if c = true then a else b

/-- A conditional successor of the later blocks (a page-table round, the ends of the blocks and
rounds), whose sub-step a proof reads off without deciding `c`. -/
abbrev D.iteS (c : Bool) (a b : D) : D :=
  ⟨if c = true then a.site else b.site, if c = true then a.v else b.v, 0⟩

/-! ### Register values -/

def coords (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : Coords :=
  let heads := headsW p
  let k := paramW 800
  let r19 := sub32 c.cur (mul32 c.tot heads)
  let r696 := sub32 (ctaW L g) (add32 r19 c.pv)
  let r697 := shl c.nt 8
  let r705 := sel (scmp .gt .s (shrs r697 3) k) (sel (scmp .gt .s (shrs r697 4) k)
    (sel (scmp .gt .s (shrs r697 5) k) (sel (scmp .gt .s (shrs r697 6) k) (i32 1) (i32 2))
      (i32 4)) (i32 8)) (i32 16)
  let r706 := min32 r705 heads
  let r707 := mul32 r706 c.nt
  let r712 := fdiv r696 r707
  let r714 := sub32 r696 (mul32 r712 r707)
  let r715 := mul32 r712 r706
  let r718 := sel (scmp .gt .s (add32 r715 r706) heads) (sub32 heads r715) r706
  let r723 := fdiv r714 r718
  ⟨add32 c.nt (not32 r723), sub32 (add32 r714 r715) (mul32 r723 r718), r696, r707, r714, r718⟩

/-- The registers of the launch the warp keeps throughout (`w` is the warp index). -/
def valuesStart (p : Params) (L : Launch) (g w : Nat) : List (Nat × Value) :=
  [(1061, b32 (g % L.block)), (1062, b32 w), (1072, .bits 32 (ctaW L g)), (1663, b32 16),
   (2535, b32 L.sharedBase),
   (7170, b32 p.batch), (7289, .ptr 64 false (.param (param 11)) 0),
   (7290, .ptr 64 false (.param (param 10)) 0), (7291, .ptr 64 false (.param (param 9)) 0),
   (7292, b64 (L.localBase + 0)), (7293, b64 (L.localBase + 32)),
   (7294, b64 (L.localBase + 64)), (7295, b64 (L.localBase + 96)),
   (7492, b64 p.kLayout.base), (7493, b64 p.kLayout.rowStride),
   (7494, b64 p.kLayout.headStride), (7495, b64 p.kLayout.pageStride),
   (7496, b64 p.vLayout.base), (7497, b64 p.vLayout.rowStride),
   (7498, b64 p.vLayout.headStride), (7499, b64 p.vLayout.pageStride),
   (7502, b64 p.cuQBase), (7503, b64 p.usedKBase), (7504, b64 p.pageTableBase),
   (7505, b64 p.pageTableStride), (7506, b64 p.cuQBase)]

/-- The registers of the scheduler that keep one value wherever they are live: the lane, the
skip predicate of the first pass, the heads of each pass. -/
def valuesRole (p : Params) (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(1073, .bits 32 (laneW L g)), (64, .pred (skipFirst p L g)), (7136, .bits 32 (headsW p)),
   (7137, .bits 32 (headsW p))]

/-- The registers of a scan round. -/
def valuesScan (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : Scan → List (Nat × Value)
  | .first =>
    [(7511, addrU p.cuQBase (laneW L g)), (7159, .bits 32 c.w), (7162, .bits 32 c.tl)] ++
      partials L g c 1716 3 7163
  | .loop =>
    loopRegs p L g false c 1075 7160 7165 7513 ++
    [(76, .pred (scmpi .eq .b (laneW L g) 31)), (7161, .bits 32 c.w), (7162, .bits 32 c.tl)] ++
      lanePreds L g 82 ++ partials L g c 1737 3 7163
  | .second =>
    [(7858, addrU p.cuQBase (laneW L g)), (7184, .bits 32 c.w), (7187, .bits 32 c.tl),
     (7145, .bits 32 (paramW p.batch))] ++ lanePreds L g 235 ++ partials L g c 2248 3 7188
  | .loop2 =>
    loopRegs p L g true c 1173 7185 7190 7860 ++
    [(243, .pred (scmpi .eq .b (laneW L g) 31)), (7186, .bits 32 c.w), (7187, .bits 32 c.tl),
     (7145, .bits 32 (paramW p.batch))] ++ lanePreds L g 249 ++ partials L g c 2269 3 7188

/-- The registers of the choice of a request, in the first pass. -/
def valuesSelect (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : List (Nat × Value) :=
  let r19 := sub32 c.cur (mul32 c.tot (headsW p))
  [(89, .pred (scmp .le .s (mad32 (prefixD L g c) (headsW p) r19) (ctaW L g))),
   (1079, .bits 32 r19), (7165, .bits 32 c.gx), (7162, .bits 32 c.tl),
   (7163, .bits 32 (prefixD L g c)), (1080, .bits 32 (popc c.bal)),
   (1752, .bits 32 (addi (popc c.bal) (-1))), (7170, .bits 32 (chosen c)), (7167, .bits 32 c.pv),
   (7144, .bits 32 (paramW p.batch)), (7154, .bits 32 (paramW 800))]

/-- The registers of the second pass's ballot. -/
def valuesSelect2 (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : List (Nat × Value) :=
  [(256, .pred (scmp .le .s (mad32 (prefixD L g c) (headsW p)
      (sub32 c.cur (mul32 c.tot (headsW p)))) (ctaW L g))),
   (7187, .bits 32 c.tl), (7188, .bits 32 (prefixD L g c)), (1177, .bits 32 (popc c.bal)),
   (2285, .bits 32 (addi (popc c.bal) (-1)))]

/-- The swizzled shared address of a row's 16 bytes (`x ^ ((x >> 3) & 112)`). -/
abbrev swz (x : BitVec 64) : BitVec 64 := xor32 (andi (shru x 3) 112) x

/-- The lane's shared base of the K/V rows (`%r731`). -/
abbrev rowBase (L : Launch) (g : Nat) : BitVec 64 :=
  add32 (sbW L) (andi (shl (BitVec.ofNat 64 (g % L.block)) 4) 1008)

/-- The 64-bit index of the chosen request (`mul.wide.s32 … 4`). -/
abbrev wideS (i : BitVec 64) : Value :=
  .bits 64 (truncBits (2 * 32) (BitVec.ofInt 64 (toSigned 32 (r32 i) * toSigned 32 (i32 4))))

/-- The registers of the request's reads. -/
def valuesReq (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  let c := v.sc
  let co := v.co
  [(7168, .bits 32 co.row), (7169, .bits 32 co.head), (7170, .bits 32 (chosen c)),
   (7514, wideS (chosen c)), (7515, addrS p.cuQBase (chosen c)),
   (7516, addrS p.usedKBase (chosen c)), (1799, .bits 32 c.c0),
   (1085, .bits 32 (sub32 c.c0 c.c1)), (7296, b64 16), (1798, b32 16), (103, .pred false),
   (7297, MemExt.same.extendBits 64 (cvtIntBits false .s 64 .s 32 (r32 (chosen c)))),
   (1081, .bits 32 (andi (shru (BitVec.ofNat 64 (g % L.block)) 3) 7)),
   (1082, .bits 32 (andi (shl (BitVec.ofNat 64 (g % L.block)) 3) 56)),
   (1083, .bits 32 (swz (addi (rowBase L g) 68608))),
   (1084, .bits 32 (swz (addi (rowBase L g) 69632)))]

/-- The empty barrier of ring slot `s` (`sb + 56 + 8 s`). -/
abbrev emptyAt (L : Launch) (s : BitVec 64) : BitVec 64 := addi (add32 (sbW L) (shl s 3)) 56

/-- The registers of the drain's polls `k`. -/
def valuesDrain (L : Launch) (w : Nat) (v : V) : Fin 3 → List (Nat × Value)
  | 0 => [(258, .pred (not14 w)), (2288, .bits 32 (emptyAt L v.slot)), (7179, .bits 32 v.slot),
      (7180, .bits 32 v.par), (7192, .bits 32 v.qp)]
  | 1 => [(258, .pred (not14 w)), (2289, .bits 32 (emptyAt L (nslot v.slot))),
      (2290, .bits 32 (npar v.slot v.par)), (2296, .bits 32 (nslot v.slot)),
      (7192, .bits 32 v.qp)]
  | 2 => [(258, .pred (not14 w)),
      (2291, .bits 32 (emptyAt L (nslot (nslot v.slot)))),
      (2292, .bits 32 (npar (nslot v.slot) (npar v.slot v.par))), (7192, .bits 32 v.qp)]

/-! ### 64-bit arithmetic, as the integer rules compute it -/

abbrev r64 (x : BitVec 64) : BitVec 64 := truncBits 64 x
abbrev mul64 (x y : BitVec 64) : BitVec 64 := truncBits 64 (r64 x * r64 y)
abbrev add64 (x y : BitVec 64) : BitVec 64 := truncBits 64 (r64 x + r64 y)
abbrev shl64 (x : BitVec 64) (n : Int) : BitVec 64 :=
  if (i32 n).toNat ≥ 64 then 0 else truncBits 64 (r64 x <<< (i32 n).toNat)
/-- `cvt.s64.s32` and `cvt.u64.u32` of a 32-bit word (Core writes the unsigned case as
`truncBits`). -/
abbrev sext (x : BitVec 64) : BitVec 64 := truncBits 64 (cvtIntBits false .s 64 .s 32 (r32 x))
abbrev zext (x : BitVec 64) : BitVec 64 := truncBits 64 (r32 x)
/-- `mul.hi.s32` by an immediate. -/
abbrev mulhi (x : BitVec 64) (n : Int) : BitVec 64 :=
  truncBits 32 (BitVec.ofInt 64 ((if (some IType.s == some IType.s) = true then
    toSigned 32 (r32 x) * toSigned 32 (i32 n) else ↑(r32 x).toNat * ↑(i32 n).toNat) / 2 ^ 32))
/-- `shr.u32` by a register. -/
abbrev shrur (x y : BitVec 64) : BitVec 64 :=
  if (r32 y).toNat ≥ 32 then 0 else r32 x >>> (r32 y).toNat
/-- `mul.wide` of kind `k` by an immediate. -/
abbrev mulWide (k : IType) (x : BitVec 64) (n : Int) : BitVec 64 :=
  if (some k == some IType.s) = true then
    truncBits (2 * 32) (BitVec.ofInt 64 (toSigned 32 (r32 x) * toSigned 32 (i32 n)))
  else BitVec.ofNat 64 ((r32 x).toNat * (i32 n).toNat)
abbrev wide4 (x : BitVec 64) : BitVec 64 := mulWide .s x 4
abbrev wideU4 (x : BitVec 64) : BitVec 64 := mulWide .u x 4

/-! ### The tile's setup and the page-table loop -/

/-- `x + 127` divided by 128, by the code's signed shift and floor correction, in its three
steps (`%r755`, the correction's predicate, the result). -/
abbrev cdivS (x : BitVec 64) : BitVec 64 := shrs (add32 x (shru (shrs x 31) 25)) 7
abbrev cdivP (x : BitVec 64) : Bool :=
  scmpi .gt .s x (-1) && scmp .ne .b x (andi (add32 x (shru (shrs x 31) 25)) (-128))

def setup (p : Params) (L : Launch) (g : Nat) (v : V) : Setup :=
  let c := v.sc
  let co := v.co
  let tid := BitVec.ofNat 64 (g % L.block)
  let r741 := shl co.row 8
  let r748 := add32 (mulhi co.head 715827883) (shru (mulhi co.head 715827883) 31)
  let p109 := scmpi .lt .s co.head 0 && scmp .ne .b co.head (mul32 r748 (i32 6))
  let r751 := add32 r748 (sel p109 (i32 (-1)) (i32 0))
  let rd9 := sext (chosen c)
  let rd235 := sext r751
  let r755 := cdivS v.ukw
  let p112 := cdivP v.ukw
  let r758 := add32 r755 (sel p112 (i32 1) (i32 0))
  let r760 := add32 (add32 r741 v.ukw) (sub32 c.c0 c.c1)
  let r761 := addi r760 256
  let r765 := cdivS r761
  let p115 := cdivP r761
  let r28 := min32 r758 (add32 r765 (sel p115 (i32 1) (i32 0)))
  let r769 := addi r760 128
  let r773 := cdivS r769
  let p118 := cdivP r769
  let r29 := sub32 (min32 r758 (add32 r773 (sel p118 (i32 1) (i32 0)))) r28
  let p119 := scmpi .gt .s r28 0
  let r31 := addi r28 (-1)
  let r32 := shl r31 7
  let r778 := sel p119 r32 (i32 0)
  { r741, r748, p109, r751, rd9
    rd11 := add64 (BitVec.ofNat 64 p.pageTableBase)
      (shl64 (mul64 (BitVec.ofNat 64 p.pageTableStride) rd9) 2)
    rd12 := add64 (BitVec.ofNat 64 p.kLayout.base)
      (shl64 (mul64 (BitVec.ofNat 64 p.kLayout.headStride) rd235) 1)
    rd13 := add64 (BitVec.ofNat 64 p.vLayout.base)
      (shl64 (mul64 (BitVec.ofNat 64 p.vLayout.headStride) rd235) 1)
    r755, p112, r758, r760, r761, r765, p115, r28, r769, r773, p118, r29, p119, r31, r32, r778
    r35 := or32 (add32 (andi (shru tid 3) 7) (andi (shl tid 3) 56)) r778 }

/-- The setup's registers, kept from the request's reads to the second pass (the temporaries at
the setup's `selp`s included). -/
def valuesSetup (_p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  let c := v.sc
  let su := v.su
  [(1801, .bits 32 su.r741), (1087, .bits 32 (add32 c.c0 su.r741)), (1086, .bits 32 v.ukw),
   (1085, .bits 32 (sub32 c.c0 c.c1)), (7168, .bits 32 v.co.row),
   (7169, .bits 32 v.co.head), (7170, .bits 32 (chosen c)),
   (108, .pred true), (1044, .bits 16 (BitVec.ofNat 64 3)), (7520, b64 1), (7296, b64 16),
   (1808, .bits 32 su.r748), (111, .pred su.p109), (7299, .bits 64 su.rd11),
   (7300, .bits 64 su.rd12), (7301, .bits 64 su.rd13), (1815, .bits 32 su.r755),
   (114, .pred su.p112), (1818, .bits 32 su.r758), (1820, .bits 32 su.r760),
   (1825, .bits 32 su.r765), (117, .pred su.p115), (1088, .bits 32 su.r28),
   (1833, .bits 32 su.r773), (120, .pred su.p118), (1089, .bits 32 su.r29),
   (1090, .bits 32 (max32 su.r29 (i32 0))), (121, .pred su.p119), (1091, .bits 32 su.r31),
   (1092, .bits 32 su.r32), (1838, .bits 32 su.r778), (1093, .bits 32 (i32 1)),
   (1094, .bits 32 (i32 3)), (1095, .bits 32 su.r35), (7302, b64 1), (9534, b64 0),
   (1059, .bits 16 (BitVec.ofNat 64 4)), (7297, .bits 64 su.rd9),
   (1081, .bits 32 (andi (shru (BitVec.ofNat 64 (g % L.block)) 3) 7)),
   (1082, .bits 32 (andi (shl (BitVec.ofNat 64 (g % L.block)) 3) 56)),
   (1083, .bits 32 (swz (addi (rowBase L g) 68608))),
   (1084, .bits 32 (swz (addi (rowBase L g) 69632)))]

/-- The tile's number of K/V blocks (`%r28`). -/
abbrev blocks (_p : Params) (_L : Launch) (_g : Nat) (v : V) : BitVec 64 := v.su.r28

/-- The first row of a lane's page round `it` in a period: the block's first row plus the lane's
row in the block (`%r36`, `%r60`, `%r89`). -/
def row0 (_p : Params) (L : Launch) (g : Nat) (v : V) (per : Per) (it : Fin 2) : BitVec 64 :=
  let tid := BitVec.ofNat 64 (g % L.block)
  let su := v.su
  match per with
  | .prime => add32 su.r35 (shl (i32 it.val) 6)
  | .warm =>
    add32 (add32 (or32 (andi (shru tid 3) 7) (andi (shl tid 3) 56))
      (shl (sub32 v.r56 v.rnd) 7)) (shl (i32 it.val) 6)
  | .steady =>
    add32 (or32 (or32 (andi (shru tid 3) 7) (andi (shl tid 3) 56))
      (shl (sub32 v.r56 v.rnd) 7)) (shl (i32 it.val) 6)

/-- The page-table index of a row (`row / 16`, by the code's multiply-high division). -/
abbrev hiWord (x : BitVec 64) : BitVec 64 :=
  truncBits 32 (BitVec.ofNat 64 (x.toNat / 4294967296))
def pgIdx (r36 : BitVec 64) : BitVec 64 :=
  let hi := hiWord (mul64 (BitVec.ofNat 64 1) (zext r36))
  shrur (add32 (shrur (sub32 r36 hi) (i32 1)) hi) (i32 3)

/-- The registers of the prime page loop's round `it`. -/
def valuesPgPrime (p : Params) (L : Launch) (g : Nat) (v : V) (it : Fin 2) :
    List (Nat × Value) :=
  let r36 := row0 p L g v .prime it
  let r37 := pgIdx r36
  [(7172, .bits 32 (i32 it.val)), (4, .pred (it.val = 0)), (1096, .bits 32 r36),
   (1097, .bits 32 r37), (122, .pred (scmp .ge .s r36 v.ukw)),
   (7531, .bits 64 (add64 v.su.rd11 (wide4 r37))), (7173, .bits 32 v.pw),
   (7532, .bits 64 (wideU4 (i32 it.val))),
   (7533, .bits 64 (add64 (BitVec.ofNat 64 (L.localBase + 96)) (wideU4 (i32 it.val)))),
   (7534, .bits 64 (add64 (BitVec.ofNat 64 (L.localBase + 64)) (wideU4 (i32 it.val)))),
   (1847, .bits 32 (sub32 r36 (mul32 r37 (i32 16))))]

/-! ### The packets -/

/-- The registers of a packet: the two address loads' words, per row the two received words,
their 64-bit join, the row's global address, the copy size and its predicate (of the K packet
for a V packet, which reuses them), and the row offset. -/
structure PkRegs where
  ld : List Nat
  lo : List Nat
  hi : List Nat
  mv : List Nat
  ad : List Nat
  sz : List Nat
  pr : List Nat
  off : Nat

def pkRegs : Nat → PkRegs
  | 0 => ⟨[1853, 1854, 1871, 1872],
   [1855, 1857, 1859, 1861, 1863, 1865, 1867, 1869, 1873, 1875, 1877, 1879, 1881, 1883, 1885, 1887],
   [1856, 1858, 1860, 1862, 1864, 1866, 1868, 1870, 1874, 1876, 1878, 1880, 1882, 1884, 1886, 1888],
   [7546, 7549, 7551, 7553, 7555, 7557, 7559, 7561, 7563, 7565, 7567, 7569, 7571, 7573, 7575, 7577],
   [7548, 7550, 7552, 7554, 7556, 7558, 7560, 7562, 7564, 7566, 7568, 7570, 7572, 7574, 7576, 7578],
   [1098, 1099, 1100, 1101, 1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113],
   [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139], 7547⟩
  | 1 => ⟨[1927, 1928, 1945, 1946],
   [1929, 1931, 1933, 1935, 1937, 1939, 1941, 1943, 1947, 1949, 1951, 1953, 1955, 1957, 1959, 1961],
   [1930, 1932, 1934, 1936, 1938, 1940, 1942, 1944, 1948, 1950, 1952, 1954, 1956, 1958, 1960, 1962],
   [7610, 7613, 7615, 7617, 7619, 7621, 7623, 7625, 7627, 7629, 7631, 7633, 7635, 7637, 7639, 7641],
   [7612, 7614, 7616, 7618, 7620, 7622, 7624, 7626, 7628, 7630, 7632, 7634, 7636, 7638, 7640, 7642],
   [1098, 1099, 1100, 1101, 1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113],
   [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139], 7611⟩
  | 2 => ⟨[1998, 1999, 2019, 2020],
   [2000, 2004, 2007, 2009, 2011, 2013, 2015, 2017, 2021, 2023, 2025, 2027, 2029, 2031, 2033, 2035],
   [2001, 2005, 2008, 2010, 2012, 2014, 2016, 2018, 2022, 2024, 2026, 2028, 2030, 2032, 2034, 2036],
   [7665, 7668, 7670, 7672, 7674, 7676, 7678, 7680, 7682, 7684, 7686, 7688, 7690, 7692, 7694, 7696],
   [7667, 7669, 7671, 7673, 7675, 7677, 7679, 7681, 7683, 7685, 7687, 7689, 7691, 7693, 7695, 7697],
   [1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135, 1136, 1137, 1138],
   [169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184], 7666⟩
  | 3 => ⟨[2077, 2078, 2098, 2099],
   [2079, 2083, 2086, 2088, 2090, 2092, 2094, 2096, 2100, 2102, 2104, 2106, 2108, 2110, 2112, 2114],
   [2080, 2084, 2087, 2089, 2091, 2093, 2095, 2097, 2101, 2103, 2105, 2107, 2109, 2111, 2113, 2115],
   [7719, 7723, 7725, 7727, 7729, 7731, 7733, 7735, 7737, 7739, 7741, 7743, 7745, 7747, 7749, 7751],
   [7722, 7724, 7726, 7728, 7730, 7732, 7734, 7736, 7738, 7740, 7742, 7744, 7746, 7748, 7750, 7752],
   [1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135, 1136, 1137, 1138],
   [169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184], 7721⟩
  | 4 => ⟨[2156, 2157, 2177, 2178],
   [2158, 2162, 2165, 2167, 2169, 2171, 2173, 2175, 2179, 2181, 2183, 2185, 2187, 2189, 2191, 2193],
   [2159, 2163, 2166, 2168, 2170, 2172, 2174, 2176, 2180, 2182, 2184, 2186, 2188, 2190, 2192, 2194],
   [7780, 7783, 7785, 7787, 7789, 7791, 7793, 7795, 7797, 7799, 7801, 7803, 7805, 7807, 7809, 7811],
   [7782, 7784, 7786, 7788, 7790, 7792, 7794, 7796, 7798, 7800, 7802, 7804, 7806, 7808, 7810, 7812],
   [1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169],
   [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227], 7781⟩
  | 5 => ⟨[2198, 2199, 2219, 2220],
   [2200, 2204, 2207, 2209, 2211, 2213, 2215, 2217, 2221, 2223, 2225, 2227, 2229, 2231, 2233, 2235],
   [2201, 2205, 2208, 2210, 2212, 2214, 2216, 2218, 2222, 2224, 2226, 2228, 2230, 2232, 2234, 2236],
   [7824, 7827, 7829, 7831, 7833, 7835, 7837, 7839, 7841, 7843, 7845, 7847, 7849, 7851, 7853, 7855],
   [7826, 7828, 7830, 7832, 7834, 7836, 7838, 7840, 7842, 7844, 7846, 7848, 7850, 7852, 7854, 7856],
   [1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169],
   [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227], 7825⟩

  | _ => ⟨[], [], [], [], [], [], [], 0⟩

/-- `mul.wide.u32 … 2`: the byte offset of a lane's 8 columns. -/
abbrev wideU2 (x : BitVec 64) : BitVec 64 := mulWide .u x 2

/-- The registers of a packet's rows, for every row (the rows not current are dead): the
address words of the current half, the current row's received words, join and address, every
row's copy size from the packet's length `len`, and the row offset `off`. -/
def valuesRows (R : PkRegs) (v : V) (len off : BitVec 64) : List (Nat × Value) :=
  let pair := v.x0 ||| v.x1 <<< 32
  [(R.ld.getD 0 0, .bits 32 v.l0), (R.ld.getD 1 0, .bits 32 v.l1), (R.ld.getD 2 0, .bits 32 v.l0),
   (R.ld.getD 3 0, .bits 32 v.l1), (R.off, .bits 64 off)] ++
  (List.range 16).flatMap fun i =>
    [(R.lo.getD i 0, .bits 32 v.x0), (R.hi.getD i 0, .bits 32 v.x1), (R.mv.getD i 0, .bits 64 pair),
     (R.ad.getD i 0, .bits 64 (add64 pair off)),
     (R.sz.getD i 0, .bits 32 (sel (scmpi .gt .s len (8 * i)) (i32 16) (i32 0))),
     (R.pr.getD i 0, .pred (scmpi .gt .s len (8 * i)))]

/-- The first block's length of rows inside the used length, for the copy sizes (`%r792`). -/
abbrev lenPrime (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
  sel v.su.p119 (sub32 v.ukw (add32 (andi (shru (BitVec.ofNat 64 (g % L.block)) 3) 7) v.su.r32))
    (i32 0)

/-- The ring slot and parity, live from the first block to the drain. -/
def valuesRing (v : V) : List (Nat × Value) :=
  [(7179, .bits 32 v.slot), (7180, .bits 32 v.par)]

/-! ### The later blocks, the pointer loops and the TMA groups -/

/-- A 64-bit immediate as `mov.b64` writes it, a local address, and the sign extension of a
32-bit word that `ld.local.s32` writes into a 64-bit register. -/
abbrev m64 (n : Int) : BitVec 64 := truncBits 64 (BitVec.ofInt 64 n)
abbrev lb (L : Launch) (o : Nat) : BitVec 64 := BitVec.ofNat 64 (L.localBase + o)
abbrev sx32 (y : BitVec 64) : BitVec 64 := truncBits 64 (BitVec.ofInt 64 (toSigned 32 y))
/-- `mad.lo.s64` and `and.b64` by an immediate. -/
abbrev mad64 (x y z : BitVec 64) : BitVec 64 := truncBits 64 (r64 x * r64 y + r64 z)
abbrev and64 (x : BitVec 64) (n : Int) : BitVec 64 := r64 x &&& m64 n

/-- The lane's index as a word. -/
abbrev tidW (L : Launch) (g : Nat) : BitVec 64 := BitVec.ofNat 64 (g % L.block)

/-- The address of the request's page-table row (`%rd11`, recomputed by the later blocks). -/
abbrev ptRow (p : Params) (v : V) : BitVec 64 :=
  add64 (BitVec.ofNat 64 p.pageTableBase)
    (shl64 (mul64 (BitVec.ofNat 64 p.pageTableStride) (sext (chosen v.sc))) 2)

/-- The steady loop's first round (`%r6121`): the warm rounds done. -/
abbrev warmRounds (v : V) : BitVec 64 :=
  min32 (max32 v.su.r31 (i32 0)) (i32 9)

/-- The registers of the pointer loop of packet `k`: the round counter, its predicate, the
round's offsets into the page and row arrays and their addresses, the page and row read back,
the row's address and its slot address. -/
structure PtRegs where
  it : Nat
  pr : Nat
  a : Nat
  b : Nat
  pg : Nat
  c : Nat
  rw : Nat
  ad : Nat
  u : Nat

def ptRegs : Nat → PtRegs
  | 0 => ⟨9535, 5, 7535, 7536, 7537, 7538, 7539, 7543, 7545⟩
  | 1 => ⟨9536, 6, 7599, 7600, 7601, 7602, 7603, 7607, 7609⟩
  | 2 => ⟨9537, 9, 7654, 7655, 7656, 7657, 7658, 7662, 7664⟩
  | 3 => ⟨9538, 10, 7708, 7709, 7710, 7711, 7712, 7716, 7718⟩
  | 4 => ⟨9539, 12, 7769, 7770, 7771, 7772, 7773, 7777, 7779⟩
  | 5 => ⟨9540, 13, 7813, 7814, 7815, 7816, 7817, 7821, 7823⟩
  | _ => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The registers of round `it` of packet `k`'s pointer loop: a K packet (`k` even) addresses
the K cache from `%rd12`, a V packet the V cache from `%rd13`; the warm and steady K packets save
the addresses at the second local array. -/
def valuesPt (p : Params) (L : Launch) (v : V) (k : Nat) (it : Fin 2) : List (Nat × Value) :=
  let R := ptRegs k
  let itv := m64 it.val
  let a := shl64 itv 2
  let lay := if k % 2 = 0 then p.kLayout else p.vLayout
  let base := if k % 2 = 0 then v.su.rd12 else v.su.rd13
  let dst := if k = 2 ∨ k = 4 then lb L 32 else lb L 0
  [(R.it, .bits 64 itv), (R.pr, .pred (it.val = 0)), (R.a, .bits 64 a),
   (R.b, .bits 64 (add64 (lb L 96) a)), (R.pg, .bits 64 (sx32 v.lp)),
   (R.c, .bits 64 (add64 (lb L 64) a)), (R.rw, .bits 64 (sx32 v.lr)),
   (R.ad, .bits 64 (add64 base (shl64 (mad64 (BitVec.ofNat 64 lay.rowStride) (sx32 v.lr)
      (mul64 (BitVec.ofNat 64 lay.pageStride) (sx32 v.lp))) 1))),
   (R.u, .bits 64 (add64 dst (shl64 itv 3)))]

/-- The swizzled row bases of the later packets: the two shared addresses of a lane's rows from
the column offset `c` (`%r928`/`%r932` and their steady and V copies). -/
abbrev rowsAt (L : Launch) (g : Nat) (c : BitVec 64) : BitVec 64 :=
  add32 (sbW L) (or32 (andi (shl (tidW L g) 4) 896) (shl c 1))

/-- The registers the warm rounds keep (`w` is the warp): the round, the Bias parities, the
ring, the round's first block (`%r56`), the Bias's sign (`%r57`), whether warp 14 loads the last
Bias block (`%p5`), the warp test and the lane's column offset (`%r59`). -/
def valuesWarm (L : Launch) (g w : Nat) (v : V) : List (Nat × Value) :=
  let su := v.su
  [(7174, .bits 32 v.rnd), (7177, .bits 32 v.bq0), (7178, .bits 32 v.bq1),
   (7179, .bits 32 v.slot), (7180, .bits 32 v.par), (1116, .bits 32 v.r56),
   (1117, .bits 32 (shru su.r29 31)), (7, .pred (scmpi .gt .s su.r28 10 && scmpi .lt .s su.r29 0)),
   (123, .pred (not14 w)), (1119, .bits 32 (andi (shl (tidW L g) 3) 56))]

/-- The registers of round `it` of a warm block's page-table loop. -/
def valuesPgWarm (p : Params) (L : Launch) (g : Nat) (v : V) (it : Fin 2) :
    List (Nat × Value) :=
  let r60 := row0 p L g v .warm it
  let r61 := pgIdx r60
  [(8, .pred (it.val = 0)), (7175, .bits 32 (i32 it.val)),
   (1118, .bits 32 (shl (sub32 v.r56 v.rnd) 7)), (1120, .bits 32 r60),
   (1121, .bits 32 r61), (7650, .bits 64 (add64 (ptRow p v) (wide4 r61))),
   (7176, .bits 32 v.pw), (7651, .bits 64 (wideU4 (i32 it.val))),
   (7652, .bits 64 (add64 (lb L 96) (wideU4 (i32 it.val)))),
   (7653, .bits 64 (add64 (lb L 64) (wideU4 (i32 it.val)))),
   (1975, .bits 32 (sub32 r60 (mul32 r61 (BitVec.ofNat 64 16))))]

/-- A warm block's first row less the lane's row (`%r933`), and the rows its packets load when
that is not negative (`%r936`). -/
abbrev startWarm (v : V) : BitVec 64 := sub32 v.r56 v.rnd
abbrev lenWarm (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
  sub32 v.ukw (or32 (andi (shru (tidW L g) 3) 7) (shl (startWarm v) 7))

/-- The registers of a warm block's K packet: the slot's barriers' base (`%r62`), the two row
bases, the length, and the two destination registers of the rows. -/
def valuesWarmK (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  let r924 := rowsAt L g (andi (shl (tidW L g) 3) 56)
  let r928 := swz (addi r924 69632)
  let r932 := swz (addi r924 68608)
  let r942 := shl v.slot 15
  valuesRows (pkRegs 2) v v.len (wideU2 (andi (shl (tidW L g) 3) 56)) ++
  [(1122, .bits 32 (add32 (sbW L) (shl v.slot 3))), (1988, .bits 32 r928),
   (1992, .bits 32 r932), (1997, .bits 32 v.len), (2002, .bits 32 r942),
   (2003, .bits 32 (add32 r932 r942)), (2006, .bits 32 (add32 r928 r942))]

/-- The registers of a warm block's V packet: the next slot and parity (`%r79`, `%r1004`), its
barriers' base, the K packet's sizes, the row bases and destinations. -/
def valuesWarmV (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  let s := nslot v.slot
  let r1006 := shl (tidW L g) 4
  let r1008 := add32 (sbW L) (andi r1006 1008)
  let r1012 := swz (addi r1008 69632)
  let r1016 := swz (addi r1008 68608)
  let r1021 := shl s 15
  valuesRows (pkRegs 3) v v.len (and64 (zext r1006) 112) ++
  [(1139, .bits 32 s), (1141, .bits 32 (add32 (sbW L) (shl s 3))),
   (2063, .bits 32 (addi (add32 (sbW L) (shl s 3)) 56)), (2064, .bits 32 (npar v.slot v.par)),
   (2066, .bits 32 r1006), (2072, .bits 32 r1012), (2076, .bits 32 r1016),
   (2081, .bits 32 r1021), (2082, .bits 32 (add32 r1016 r1021)),
   (2085, .bits 32 (add32 r1012 r1021))]

/-- The registers the steady rounds keep: the round, the ring, the round's first block and its
row offset (`%r84`, `%r85`), the lane's row and column offsets (`%r86`, `%r87`, `%r1070`), the
page-table row, the column offset in bytes, and the row bases (`%r92`, `%r93`). -/
def valuesSteady (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  let su := v.su
  let r84 := sub32 v.r56 v.rnd
  let r86 := andi (shru (tidW L g) 3) 7
  let r87 := andi (shl (tidW L g) 3) 56
  let r1086 := rowsAt L g r87
  [(7181, .bits 32 v.rnd), (7179, .bits 32 v.slot), (7180, .bits 32 v.par),
   (1116, .bits 32 v.r56), (1117, .bits 32 (shru su.r29 31)),
   (1144, .bits 32 r84), (1145, .bits 32 (shl r84 7)), (1146, .bits 32 r86),
   (1147, .bits 32 r87), (2130, .bits 32 (or32 r86 r87)), (7763, .bits 64 (ptRow p v)),
   (7781, .bits 64 (wideU2 r87)), (1152, .bits 32 (swz (addi r1086 69632))),
   (1153, .bits 32 (swz (addi r1086 68608)))]

/-- The registers of round `it` of a steady block's page-table loop. -/
def valuesPgSteady (p : Params) (L : Launch) (g : Nat) (v : V) (it : Fin 2) :
    List (Nat × Value) :=
  let r84 := sub32 v.r56 v.rnd
  let r1070 := or32 (andi (shru (tidW L g) 3) 7) (andi (shl (tidW L g) 3) 56)
  let r89 := row0 p L g v .steady it
  let r90 := pgIdx r89
  [(11, .pred (it.val = 0)), (7182, .bits 32 (i32 it.val)),
   (1148, .bits 32 (or32 r1070 (shl r84 7))), (1149, .bits 32 r89), (1150, .bits 32 r90),
   (7765, .bits 64 (add64 (ptRow p v) (wide4 r90))), (7183, .bits 32 v.pw),
   (7766, .bits 64 (wideU4 (i32 it.val))),
   (7767, .bits 64 (add64 (lb L 96) (wideU4 (i32 it.val)))),
   (7768, .bits 64 (add64 (lb L 64) (wideU4 (i32 it.val)))),
   (2137, .bits 32 (sub32 r89 (mul32 r90 (BitVec.ofNat 64 16))))]

/-- The same for a steady block (`%r84`, `%r1094`). -/
abbrev lenSteady (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
  sub32 v.ukw (add32 (andi (shru (tidW L g) 3) 7) (shl (startWarm v) 7))

/-- The registers of a steady block's K packet. -/
def valuesSteadyK (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  let r87 := andi (shl (tidW L g) 3) 56
  let r1086 := rowsAt L g r87
  let r1100 := shl v.slot 15
  valuesRows (pkRegs 4) v v.len (wideU2 r87) ++
  [(1151, .bits 32 (add32 (sbW L) (shl v.slot 3))), (2155, .bits 32 v.len),
   (2160, .bits 32 r1100), (2161, .bits 32 (add32 (swz (addi r1086 68608)) r1100)),
   (2164, .bits 32 (add32 (swz (addi r1086 69632)) r1100))]

/-- The registers of a steady block's V packet. -/
def valuesSteadyV (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  let r87 := andi (shl (tidW L g) 3) 56
  let r1086 := rowsAt L g r87
  let s := nslot v.slot
  let r1142 := shl s 15
  valuesRows (pkRegs 5) v v.len (wideU2 r87) ++
  [(1170, .bits 32 s), (1171, .bits 32 (add32 (sbW L) (shl s 3))),
   (2140, .bits 32 (addi (add32 (sbW L) (shl s 3)) 56)), (2141, .bits 32 (npar v.slot v.par)),
   (2202, .bits 32 r1142), (2203, .bits 32 (add32 (swz (addi r1086 68608)) r1142)),
   (2206, .bits 32 (add32 (swz (addi r1086 69632)) r1142))]

/-- A tensor map's generic address (`cvta.param` of parameter `i`) and a zero cache hint. -/
abbrev tmap (i : Nat) : Value := .ptr 64 true (.param (param i)) 0

/-- The registers of TMA group `t`: its barrier addresses, the expected bytes, the copies'
coordinates, tensor maps and cache hints. -/
def valuesTma (L : Launch) (v : V) : Fin 7 → List (Nat × Value)
  | 0 => [(1889, .bits 32 (addi (sbW L) 16)), (1890, .bits 32 (i32 1)),
      (1892, .bits 32 (i32 32768)), (7580, tmap 9), (7581, .bits 64 (m64 0)),
      (1894, .bits 32 (i32 0)), (7582, tmap 9), (7583, .bits 64 (m64 0)),
      (1896, .bits 32 (i32 64))]
  | 1 => [(1114, .bits 32 (addi (sbW L) 320)), (1897, .bits 32 (addi (sbW L) 336)),
      (1898, .bits 32 (i32 1)), (1900, .bits 32 (i32 32768)),
      (1903, .bits 32 (sub32 (i32 1152) (shl (max32 v.su.r29 (i32 0)) 7))),
      (7585, tmap 11), (7586, .bits 64 (m64 0)),
      (1906, .bits 32 (sub32 (i32 1216) (shl (max32 v.su.r29 (i32 0)) 7))),
      (7587, tmap 11), (7588, .bits 64 (m64 0))]
  | 2 => [(1907, .bits 32 (addi (sbW L) 24)), (1908, .bits 32 (i32 1)),
      (1910, .bits 32 (i32 32768)), (7590, tmap 9),
      (1912, .bits 32 (addi (add32 v.sc.c0 v.su.r741) 128)), (7591, .bits 64 (m64 0)),
      (1913, .bits 32 (i32 0)), (7592, tmap 9),
      (1915, .bits 32 (addi (add32 v.sc.c0 v.su.r741) 128)), (7593, .bits 64 (m64 0)),
      (1916, .bits 32 (i32 64))]
  | 3 => [(1917, .bits 32 (addi (sbW L) 344)), (1918, .bits 32 (i32 1)),
      (1920, .bits 32 (i32 32768)), (1115, .bits 32 (addi (add32 v.sc.c0 v.su.r741) 128)),
      (7595, tmap 11), (7596, .bits 64 (m64 0)), (1922, .bits 32 (i32 1152)),
      (7597, tmap 11), (7598, .bits 64 (m64 0)), (1924, .bits 32 (i32 1216))]
  | 4 =>
    let r984 := sub32 (shru v.su.r29 31) (add32 (max32 v.su.r29 (i32 0)) v.rnd)
    [(1140, .bits 32 (addi (sbW L) 320)), (2039, .bits 32 (addi (sbW L) 336)),
      (2041, .bits 32 (i32 32768)), (2046, .bits 32 (addi (shl r984 7) 1024)),
      (7699, tmap 11), (7700, .bits 64 (m64 0)), (2051, .bits 32 (addi (shl r984 7) 1088)),
      (7701, tmap 11), (7702, .bits 64 (m64 0))]
  | 5 => [(2052, .bits 32 (addi (sbW L) 344)), (2054, .bits 32 (i32 32768)),
      (2057, .bits 32 (sub32 (i32 1024) (shl v.rnd 7))),
      (2058, .bits 32 (addi (add32 v.sc.c0 v.su.r741) 128)), (7704, tmap 11),
      (7705, .bits 64 (m64 0)), (2061, .bits 32 (sub32 (i32 1088) (shl v.rnd 7))),
      (2062, .bits 32 (addi (add32 v.sc.c0 v.su.r741) 128)), (7706, tmap 11),
      (7707, .bits 64 (m64 0))]
  | 6 =>
    let r83 := shl (warmRounds v) 7
    [(1142, .bits 32 (addi (sbW L) 320)), (2121, .bits 32 (addi (sbW L) 336)),
      (2123, .bits 32 (i32 32768)), (1143, .bits 32 r83),
      (2125, .bits 32 (sub32 (i32 1152) r83)), (7754, tmap 11), (7755, .bits 64 (m64 0)),
      (2127, .bits 32 (sub32 (i32 1216) r83)), (7756, tmap 11), (7757, .bits 64 (m64 0)),
      (7181, .bits 32 (warmRounds v)), (7177, .bits 32 v.bq0),
      (1116, .bits 32 v.r56), (1117, .bits 32 (shru v.su.r29 31)),
      (7179, .bits 32 v.slot), (7180, .bits 32 v.par)]

/-- The registers of the first block's packets (`half`: the V packet, which also keeps warp 14's
first Bias parity `%r6117` and whether the Bias ends inside the tile, `%p162`). -/
def valuesPrime (L : Launch) (g w : Nat) (v : V) (half : Bool) : List (Nat × Value) :=
  let off := wideU2 (andi (shl (BitVec.ofNat 64 (g % L.block)) 3) 56)
  valuesRows (pkRegs (if half then 1 else 0)) v (lenPrime L g v) off ++
    [(1852, .bits 32 (lenPrime L g v)), (123, .pred (not14 w))] ++
    (if half then [(7177, .bits 32 v.bq0), (164, .pred (scmpi .lt .s v.su.r29 0))] else [])

/-- The registers at state `d`. -/
def values (p : Params) (L : Launch) (g w : Nat) (d : D) : List (Nat × Value) :=
  let v := d.v
  match d.site with
  | .setmax => []
  | .word k | .down k | .up k _ | .total k => valuesScan p L g v.sc k ++ valuesRing v
  | .vote false | .pre false | .tiles false => valuesSelect p L g v.sc
  | .vote true | .pre true | .tiles true =>
    valuesSelect2 p L g v.sc ++ valuesRing v ++ [(7192, .bits 32 v.qp)]
  | .q0 | .q1 | .uk => valuesReq p L g v
  | .pgLd .prime it | .pgSt .prime it | .rwSt .prime it =>
    valuesPgPrime p L g v it ++ valuesSetup p L g v
  | .slot .prime false =>
    [(1848, .bits 32 (addi (sbW L) 56)), (1849, .bits 32 (i32 1))] ++ valuesSetup p L g v
  | .slot .prime true =>
    [(1925, .bits 32 (addi (sbW L) 64)), (1926, .bits 32 (i32 1))] ++
      valuesPrime L g w v true ++ valuesSetup p L g v
  | .ptP .prime h it | .ptR .prime h it | .ptS .prime h it =>
    valuesPt p L v (pk .prime h) it ++ valuesPrime L g w v h ++ valuesSetup p L g v
  | .lw .prime h _ | .xl .prime h _ | .xh .prime h _ | .cp .prime h _ _ | .commit .prime h
  | .arrive .prime h => valuesPrime L g w v h ++ valuesSetup p L g v
  | .tw t | .te t _ | .ta t | .tc t _ =>
    if t.val < 4 then
      valuesTma L v t ++ valuesPrime L g w v false ++ [(7177, .bits 32 v.bq0)] ++
        valuesSetup p L g v
    else if t.val < 6 then
      valuesTma L v t ++ [(1139, .bits 32 (nslot v.slot)), (2064, .bits 32 (npar v.slot v.par))] ++
        valuesRows (pkRegs 2) v v.len 0 ++ valuesWarm L g w v ++ valuesSetup p L g v
    else valuesTma L v t ++ valuesSetup p L g v
  | .pgLd .warm it | .pgSt .warm it | .rwSt .warm it =>
    valuesPgWarm p L g v it ++ valuesWarm L g w v ++ valuesSetup p L g v
  | .slot .warm false =>
    [(1122, .bits 32 (add32 (sbW L) (shl v.slot 3))),
     (1976, .bits 32 (addi (add32 (sbW L) (shl v.slot 3)) 56))] ++
      valuesWarm L g w v ++ valuesSetup p L g v
  | .ptP .warm false it | .ptR .warm false it | .ptS .warm false it =>
    valuesPt p L v 2 it ++ [(1122, .bits 32 (add32 (sbW L) (shl v.slot 3)))] ++
      valuesWarm L g w v ++ valuesSetup p L g v
  | .lw .warm false _ | .xl .warm false _ | .xh .warm false _ | .cp .warm false _ _
  | .commit .warm false | .arrive .warm false =>
    valuesWarmK L g v ++ valuesWarm L g w v ++ valuesSetup p L g v
  | .slot .warm true | .lw .warm true _ | .xl .warm true _ | .xh .warm true _
  | .cp .warm true _ _ | .commit .warm true | .arrive .warm true =>
    valuesWarmV L g v ++ valuesWarm L g w v ++ valuesSetup p L g v
  | .ptP .warm true it | .ptR .warm true it | .ptS .warm true it =>
    valuesPt p L v 3 it ++ valuesWarmV L g v ++ valuesWarm L g w v ++ valuesSetup p L g v
  | .pgLd .steady it | .pgSt .steady it | .rwSt .steady it =>
    valuesPgSteady p L g v it ++ valuesSteady p L g v ++ valuesSetup p L g v
  | .slot .steady false =>
    [(1151, .bits 32 (add32 (sbW L) (shl v.slot 3))),
     (2138, .bits 32 (addi (add32 (sbW L) (shl v.slot 3)) 56))] ++
      valuesSteady p L g v ++ valuesSetup p L g v
  | .ptP .steady false it | .ptR .steady false it | .ptS .steady false it =>
    valuesPt p L v 4 it ++ [(1151, .bits 32 (add32 (sbW L) (shl v.slot 3)))] ++
      valuesSteady p L g v ++ valuesSetup p L g v
  | .lw .steady false _ | .xl .steady false _ | .xh .steady false _ | .cp .steady false _ _
  | .commit .steady false | .arrive .steady false =>
    valuesSteadyK L g v ++ valuesSteady p L g v ++ valuesSetup p L g v
  | .slot .steady true | .lw .steady true _ | .xl .steady true _ | .xh .steady true _
  | .cp .steady true _ _ | .commit .steady true | .arrive .steady true =>
    valuesSteadyV L g v ++ valuesSteady p L g v ++ valuesSetup p L g v
  | .ptP .steady true it | .ptR .steady true it | .ptS .steady true it =>
    valuesPt p L v 5 it ++ valuesSteadyV L g v ++ valuesSteady p L g v ++ valuesSetup p L g v
  | .dw k => valuesDrain L w v k
  | .dq => [(2305, .bits 32 (addi (sbW L) 24)), (7192, .bits 32 v.qp)]
  | .da => [(2307, .bits 32 (i32 32768))]
  | .de | .exit => []

/-- The value of register `r` at state `d`; `ent` gives the startup registers the warp never
reads. -/
def valueOf (p : Params) (L : Launch) (g w : Nat) (ent : Nat → Value) (d : D) (r : Nat) : Value :=
  ((values p L g w d).lookup r).getD (((valuesRole p L g).lookup r).getD
    (((valuesStart p L g w).lookup r).getD (ent r)))

abbrev facts (p : Params) (L : Launch) (g w : Nat) (ent : Nat → Value) (d : D) :
    List (Nat × Value) :=
  Flow.factsFrom (Flow.live d.site.pc) (valueOf p L g w ent d)

/-! ### Transitions -/

/-- Follow a 32-bit word. -/
def word32 (v : Value) (f : BitVec 64 → D) : Option (Option D) :=
  match v with
  | .bits 32 x => some (some (f x))
  | _ => some none

/-- A state at site `s` with the scan state changed by `f`. -/
abbrev scAt (d : D) (s : Site) (f : Epilogue.D → Epilogue.D) : D :=
  D.mk' s { d.v with sc := f d.v.sc }

/-- The drain from the first pass without a tile: slot 0, parity 1, Q parity 1. -/
abbrev drain0 (v : V) : V := { v with slot := i32 0, par := i32 1, qp := i32 1 }

/-- The end of the scan of pass `late`, with the last group's capped first request `gx` and the
tiles `cur` through it: past the batch, no tile (the drain); else the ballot. -/
def scanExit (p : Params) (late : Bool) (d : D) (gx cur : BitVec 64) : D :=
  let v := if late then { d.v with qp := i32 0 } else d.v
  D.ite (scmp .ge .s gx (batchOf p late))
    (D.mk' (.dw 0) (if late then v else drain0 v))
    (D.mk' (.vote late) { v with sc := { v.sc with gx := gx, cur := cur } })

/-- The loop head of pass `late` with group start `grp` and tiles `acc` before it. -/
def loopHead (p : Params) (L : Launch) (g : Nat) (late : Bool) (d : D) (grp acc : BitVec 64) :
    D :=
  D.ite (scmp .ge .s (addi grp 31) (batchOf p late))
    (scanExit p late d (min32 (addi grp 31) (batchOf p late)) (addi (ctaW L g) 1))
    (D.ite (scmp .gt .s (reqOf L g grp) (batchOf p late))
      (scAt d (.down (loopOf late)) fun c => { c with grp := grp, acc := acc, w := i32 0 })
      (scAt d (.word (loopOf late)) fun c => { c with grp := grp, acc := acc }))

/-- After lane 31's prefix sum `x` of a round of scan `k`. -/
def afterTotal (p : Params) (L : Launch) (g : Nat) (k : Scan) (d : D) (x : BitVec 64) : D :=
  let d := scAt d d.site fun c => { c with tot := x }
  match k with
  | .first | .second =>
    D.ite (scmp .gt .s (mul32 x (headsW p)) (ctaW L g))
      (scanExit p k.late d (i32 0) (mul32 x (headsW p)))
      (loopHead p L g k.late d (i32 0) (mul32 x (headsW p)))
  | .loop | .loop2 =>
    D.ite (scmp .le .s (mad32 x (headsW p) d.v.sc.acc) (ctaW L g))
      (loopHead p L g k.late d (min32 (addi d.v.sc.grp 31) (batchOf p k.late))
        (mad32 x (headsW p) d.v.sc.acc))
      (scanExit p k.late d (min32 (addi d.v.sc.grp 31) (batchOf p k.late))
        (mad32 x (headsW p) d.v.sc.acc))

/-- After the chosen request's tile count `x`: the coordinates, then the request's reads if the
request exists, else the drain. A division without a rule faults the thread. -/
def afterTiles (p : Params) (L : Launch) (g : Nat) (d : D) (x : BitVec 64) : Option D :=
  let d := scAt d d.site fun c => { c with nt := x }
  let co := coords p L g d.v.sc
  let v := drain0 { d.v with co := co }
  if divOk co.n1 co.d1 then
    if divOk co.n2 co.d2 then
      some (D.ite (scmp .lt .s (chosen d.v.sc) (paramW p.batch)) (D.mk' .q0 v) (D.mk' (.dw 0) v))
    else none
  else none

/-- The start of a scheduler pass: lanes past the batch skip their read. -/
def passStart (p : Params) (L : Launch) (g : Nat) (late : Bool) (d : D) : D :=
  let k : Scan := if late then .second else .first
  D.ite (scmp .gt .s (laneW L g) (if late then paramW p.batch else BitVec.ofNat 64 p.batch))
    (scAt d (.down k) fun c => { c with w := i32 0 }) (D.mk' (.word k) d.v)

/-- The state's values with the tile's setup recorded. -/
abbrev withSetup (p : Params) (L : Launch) (g : Nat) (v : V) : V := { v with su := setup p L g v }

/-- The conditions of the warm and steady blocks' successors, as opaque constants: whether the
row is past the used length (`%p165`, `%p208`), and whether a block starts before the lane's
first row (`%p166`, `%p209`). Their terms add the 32-bit pattern of `-2` to a recorded word,
and evaluating them (which `site_norm` does at a conditional successor) recurses through that
literal; as constants they stay closed until a proof unfolds them (`geW_eq`, `ltZ_eq`; the
role's `sym_decide` rule decides the code's branch with them). -/
@[irreducible] def geW (x y : BitVec 64) : Bool := scmp .ge .s x y
@[irreducible] def ltZ (x : BitVec 64) : Bool := scmpi .lt .s x 0

theorem geW_eq (x y : BitVec 64) : geW x y = scmp .ge .s x y := by
  delta geW; exact Eq.refl _
theorem ltZ_eq (x : BitVec 64) : ltZ x = scmpi .lt .s x 0 := by
  delta ltZ; exact Eq.refl _

/-- The condition of round `it`'s page load. -/
def rowCond (p : Params) (L : Launch) (g : Nat) (v : V) (per : Per) (it : Fin 2) : Bool :=
  if per = .prime then scmp .ge .s (row0 p L g v per it) v.ukw
  else geW (row0 p L g v per it) v.ukw

/-- Round `it` of a period's page loop: the page index is read when the row is inside the used
length, else it is zero. -/
def pgEnter (p : Params) (L : Launch) (g : Nat) (d : D) (per : Per) (it : Fin 2) : D :=
  D.iteS (rowCond p L g d.v per it)
    (D.mk' (.pgSt per it) { d.v with pw := i32 0 }) (D.mk' (.pgLd per it) d.v)

/-- The steady loop, or the second pass when no block is left. -/
def afterTail (p : Params) (L : Launch) (g : Nat) (d : D) : D :=
  let v := { d.v with rnd := warmRounds d.v }
  D.iteS (scmp .ge .s (warmRounds d.v) d.v.su.r31)
    (passStart p L g true (D.mk' d.site v)) (pgEnter p L g (D.mk' d.site v) .steady 0)

/-- After the warm rounds: warp 14 loads the last Bias block when the tile has more than ten
blocks and the Bias ends inside it (`%p5`), then the steady loop. -/
def afterWarm (p : Params) (L : Launch) (g w : Nat) (d : D) : D :=
  let r28 := blocks p L g d.v
  let r29 := d.v.su.r29
  D.iteS (not14 w || !(scmpi .gt .s r28 10 && scmpi .lt .s r29 0)) (afterTail p L g d)
    (D.mk' (.tw 6) d.v)

/-- The end of the first block: the warm rounds when the tile has two blocks or more. -/
def afterPrime (p : Params) (L : Launch) (g w : Nat) (d : D) : D :=
  let v := { d.v with slot := i32 2, par := i32 1, r56 := addi (blocks p L g d.v) (-2) }
  D.iteS (scmpi .lt .s (blocks p L g d.v) 2) (afterWarm p L g w (D.mk' d.site v))
    (pgEnter p L g (D.mk' d.site { v with rnd := i32 0, bq1 := d.v.bq0 }) .warm 0)

/-- The slot and parity after a round's V half, and the next round. -/
abbrev roundV (v : V) : V :=
  { v with
    slot := nslot (nslot v.slot)
    par := npar (nslot v.slot) (npar v.slot v.par)
    rnd := addi v.rnd 1 }

/-- The end of a warm round's V half: another warm round or the end of the warm loop. -/
def warmEnd (p : Params) (L : Launch) (g w : Nat) (d : D) : D :=
  D.iteS (scmp .ne .b (addi d.v.rnd 1) (warmRounds d.v))
    (pgEnter p L g (D.mk' d.site (roundV d.v)) .warm 0)
    (afterWarm p L g w (D.mk' d.site (roundV d.v)))

/-- The end of a steady round's V half: another round or the scheduler's second pass. -/
def steadyEnd (p : Params) (L : Launch) (g : Nat) (d : D) : D :=
  D.iteS (scmp .lt .s (addi d.v.rnd 1) d.v.su.r31)
    (pgEnter p L g (D.mk' d.site (roundV d.v)) .steady 0)
    (passStart p L g true (D.mk' d.site (roundV d.v)))

/-- The site after a packet's arrival. -/
def afterArrive (p : Params) (L : Launch) (g w : Nat) (d : D) : Per → Bool → D
  | .prime, false =>
    D.ite (not14 w) (D.mk' (.slot .prime true) { d.v with bq0 := i32 1 })
      (D.mk' (.tw 0) { d.v with bq0 := i32 1 })
  | .prime, true => afterPrime p L g w d
  | .warm, false => D.ite (not14 w) (D.mk' (.slot .warm true) d.v) (D.mk' (.tw 4) d.v)
  | .warm, true => warmEnd p L g w d
  | .steady, false => D.mk' (.slot .steady true) d.v
  | .steady, true => steadyEnd p L g d

/-- The site after TMA group `t`. -/
def groupEnd (p : Params) (L : Launch) (g : Nat) (d : D) : Fin 7 → D
  | 0 => D.mk' (.tw 1) d.v
  | 1 => D.mk' (.tw 2) d.v
  | 2 => D.mk' (.tw 3) d.v
  | 3 => D.mk' (.slot .prime true) d.v
  | 4 => D.mk' (.tw 5) d.v
  | 5 => D.mk' (.slot .warm true) { d.v with bq0 := xori d.v.bq0 1, bq1 := xori d.v.bq1 1 }
  | 6 => afterTail p L g d
where xori (x : BitVec 64) (n : Int) : BitVec 64 := r32 x ^^^ i32 n

/-- The site after election `e` of TMA group `t` on a lane it did not elect (or after the
elected lane's arrival or copy before it). -/
def teNext (p : Params) (L : Launch) (g : Nat) (d : D) (t : Fin 7) : Fin 3 → D
  | 0 => D.mk' (.te t 1) d.v
  | 1 => D.mk' (.te t 2) d.v
  | 2 => groupEnd p L g (if t.val = 3 then { d with v := { d.v with bq0 := i32 0 } } else d) t

/-- The site after election `e` of TMA group `t` on the lane it elected. -/
def teElected (d : D) (t : Fin 7) : Fin 3 → D
  | 0 => D.mk' (.ta t) d.v
  | 1 => D.mk' (.tc t 0) d.v
  | 2 => D.mk' (.tc t 1) (if t.val = 3 then { d.v with bq0 := i32 0 } else d.v)

/-- The site after the drain's successful poll `k`. -/
def dwNext (w : Nat) (d : D) : Fin 3 → D
  | 0 => D.mk' (.dw 1) d.v
  | 1 => D.mk' (.dw 2) d.v
  | 2 => D.ite (not14 w) (D.mk' .exit d.v) (D.mk' .dq d.v)

/-- The start of a packet after its pointer loop: a warm or steady block's K packet records the
rows it loads, zero when the block starts before the lane's first row (the code's `selp`). -/
def pkStart (L : Launch) (g : Nat) (d : D) (per : Per) (b : Bool) : D :=
  if per = .prime then D.mk' (.lw per b 0) d.v
  else if b = true then D.mk' (.lw per b 0) d.v
  else D.mk' (.lw per b 0) { d.v with
    len := sel (scmpi .lt .s (startWarm d.v) 0) (i32 0)
      (if per = .warm then lenWarm L g d.v else lenSteady L g d.v) }

/-- The successor after event `e`. -/
def succ (p : Params) (L : Launch) (g w : Nat) (d : D) (e : Event) : Option (Option D) :=
  let go (s : Site) : Option (Option D) := some (some (D.mk' s d.v))
  match d.site with
  | .setmax => some (some (passStart p L g false d))
  | .word k =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => word32 v fun x => scAt d (.down k) fun c => { c with w := x }
      | .error _ => none
    | _ => none
  | .down k =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v fun x =>
      scAt d (.up k 0) fun c => { c with dn := x, tl := tlOf p L g k c x }
    | _ => none
  | .up k j =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v fun x =>
      match j with
      | 0 => scAt d (.up k 1) fun c => { c with u1 := x }
      | 1 => scAt d (.up k 2) fun c => { c with u2 := x }
      | 2 => scAt d (.up k 3) fun c => { c with u4 := x }
      | 3 => scAt d (.up k 4) fun c => { c with u8 := x }
      | 4 => scAt d (.total k) fun c => { c with u16 := x }
    | _ => none
  | .total k =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v (afterTotal p L g k d)
    | _ => none
  | .vote late =>
    match e.kind with
    | .vote _ _ b =>
      let d := scAt d d.site fun c => { c with bal := BitVec.ofNat 64 b.toNat }
      some (some (D.ite (scmpi .eq .b d.v.sc.bal 0)
        (scAt d (.tiles late) fun c => { c with pv := i32 0 }) (D.mk' (.pre late) d.v)))
    | _ => none
  | .pre late =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v fun x =>
      if late then scAt d (.tiles true) fun c => c
      else scAt d (.tiles false) fun c => { c with pv := mul32 x (headsW p) }
    | _ => none
  | .tiles late =>
    match e.kind with
    | .shfl _ _ _ _ v _ =>
      match v with
      | .bits 32 x =>
        if late then some (some (scAt d (.dw 0) fun c => c))
        else (afterTiles p L g d x).map some
      | _ => some none
    | _ => none
  | .q0 =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => word32 v fun x => scAt d .q1 fun c => { c with c0 := x }
      | .error _ => none
    | _ => none
  | .q1 =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => word32 v fun x => scAt d .uk fun c => { c with c1 := x }
      | .error _ => none
    | _ => none
  | .uk =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => word32 v fun x =>
        pgEnter p L g (D.mk' .uk (withSetup p L g { d.v with ukw := x })) .prime 0
      | .error _ => none
    | _ => none
  | .pgLd per it =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => word32 v fun x => D.mk' (.pgSt per it) { d.v with pw := x }
      | .error _ => none
    | _ => none
  | .pgSt per it => go (.rwSt per it)
  | .rwSt per it =>
    if it.val = 0 then some (some (pgEnter p L g d per 1)) else go (.slot per false)
  | .slot per v =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then D.mk' (.ptP per v 0) d.v else d))
    | _ => none
  | .ptP per v it =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok x => word32 x fun y => D.mk' (.ptR per v it) { d.v with lp := y }
      | .error _ => none
    | _ => none
  | .ptR per v it =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok x => word32 x fun y => D.mk' (.ptS per v it) { d.v with lr := y }
      | .error _ => none
    | _ => none
  | .ptS per v it => if it.val = 0 then go (.ptP per v 1) else some (some (pkStart L g d per v))
  | .lw per v h =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok x => word32 x fun y =>
        if d.k.val = 0 then ⟨.lw per v h, { d.v with l0 := y }, 1⟩
        else D.mk' (.xl per v ⟨8 * h.val, by omega⟩) { d.v with l1 := y }
      | .error _ => none
    | _ => none
  | .xl per v i =>
    match e.kind with
    | .shfl _ _ _ _ x _ => word32 x fun y => D.mk' (.xh per v i) { d.v with x0 := y }
    | _ => none
  | .xh per v i =>
    match e.kind with
    | .shfl _ _ _ _ x _ => word32 x fun y => D.mk' (.cp per v i 0) { d.v with x1 := y }
    | _ => none
  | .cp per v i c =>
    if c.val = 0 then go (.cp per v i 1)
    else if i.val = 7 then go (.lw per v 1)
    else if i.val = 15 then go (.commit per v) else go (.xl per v (i + 1))
  | .commit per v => go (.arrive per v)
  | .arrive per v => some (some (afterArrive p L g w d per v))
  | .tw t =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then D.mk' (.te t 0) d.v else d))
    | _ => none
  | .te t i =>
    match e.kind with
    | .elect _ _ ld =>
      some (some (if laneOf L g = ld then teElected d t i else teNext p L g d t i))
    | _ => none
  | .ta t => go (.te t 1)
  | .tc t c => if c.val = 0 then go (.te t 2) else some (some (groupEnd p L g d t))
  | .dw k =>
    match e.kind with
    | .wait _ _ ok _ _ =>
      some (some (if ok then dwNext w d k else d))
    | _ => none
  | .dq =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then D.mk' .de d.v else d))
    | _ => none
  | .de =>
    match e.kind with
    | .elect _ _ ld => some (some (if laneOf L g = ld then D.mk' .da d.v else D.mk' .exit d.v))
    | _ => none
  | .da => go .exit
  | .exit => none

/-- The midway sub-steps a state may have: the second element of an address load. -/
def Site.midOk : Site → Fin 2 → Prop
  | .lw _ _ _, _ => True
  | _, _ => False

/-- The accumulator of a sub-step: the first word of an address load at sub-step 1. -/
def accOf : Fin 2 → BitVec 64 → List Value
  | ⟨0, _⟩, _ => []
  | ⟨_ + 1, _⟩, l0 => [.bits 32 l0]

/-- The loader warps as a code machine (`w` is the lane's warp, 14 or 15). -/
@[reducible] def code (p : Params) (L : Launch) (g w : Nat) (ent : Nat → Value) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := D.mk' .setmax {}
  pc := (·.site.pc)
  facts := facts p L g w ent
  sub := (·.k.val)
  acc := fun d => accOf d.k d.v.l0
  inv := fun d => d.k = 0 ∨ d.site.midOk d.k
  next := succ p L g w

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
