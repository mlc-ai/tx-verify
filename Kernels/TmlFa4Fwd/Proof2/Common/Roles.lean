-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Startup.Machine
public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Shape
public import Kernels.TmlFa4Fwd.Proof2.Mma.Startup
public import Kernels.TmlFa4Fwd.Proof2.Mma.Ledger
public import Kernels.TmlFa4Fwd.Proof2.Correction.Ledger
public import Kernels.TmlFa4Fwd.Proof2.Loader.Handoff
public import Kernels.TmlFa4Fwd.Proof2.Loader.Ledger
public import Kernels.TmlFa4Fwd.Proof2.SmWarp.Code
public import Lemmas.Flow.Glue
public import Lemmas.Flow.Counted
public import Lemmas.Flow.Polls
public import Lemmas.Kernel.CodeCheck
public import Tactics.KernelRfl

@[expose] public section

/-! # The roles of tml-fa4 and the thread machine glued from them

Every thread runs the startup (`Proof2/Startup`) and then the role its warp index selects. This
file declares the roles against the code and glues their fragments into one machine per thread
(`thread`), so the layers above use one frame, `Frame.stateAt thread`, for every thread.

**Roles as data.** Each fragment has a region of the code (half-open intervals) and the pcs where
control may leave it (`Decl`). `closed` checks, by evaluation of the decoded program, that every
instruction of a region other than its exits continues inside it, and `sites` lists the region's
event instructions, which are the machine's sites (`Startup.site_mem`). A role region contains the
dispatch tests that follow its code (the compiled dispatch is a sequence of `if`s, so a finished
role walks the remaining tests to the common return at pc 9205); the first instructions of the
roles those tests could reach are its declared exits, which the role's own facts on the warp index
exclude.

**Glue and ledger.** The role index is `Role`: a migrated role is its own constructor, a role
not yet migrated is `stub r`, whose fragment stops at its first event (`stop`). The startup's exit
`enter r` enters role `r` when the startup's recorded words are the reference ones the role's
first state relies on (`Gate`: the shared base and the warp index), else the stub of `r`. That
the gate holds on every thread is the startup's reference invariant, so no followed thread
reaches a stub of a migrated role; the startup itself follows every value (plan rule M1). The
thread machine counts the events of each class `Cls` (`Code.counted`); a role's reference
invariant states closed forms of the counts.

**Interface for other lanes.** A lane migrating role `r` adds a constructor to `Role`, its case
to `frag` and `exit` (with its gate), and a hand-off lemma `handoff_r` in `Common/Sound.lean`:
a concrete state of the startup's state `enter r` whose words pass the gate is a concrete state
of the role's first state. Nothing else in this file or in the startup changes. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2
open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ### Regions and exits -/

/-- A fragment's region of the code and the pcs where control may leave it. -/
structure Decl where
  region : List (Nat × Nat)
  exits : List Nat

def startupDecl : Decl :=
  ⟨[(0, 180), (1901, 1908), (2768, 2770), (3099, 3103), (7742, 7747), (9205, 9206)],
    [179, 1907, 2769, 3102, 7746, 9205]⟩

def loaderDecl : Decl :=
  ⟨[(179, 1908), (2768, 2770), (3099, 3103), (7742, 7747), (9205, 9206)],
    [1907, 2769, 3102, 7746, 9205]⟩

def mmaDecl : Decl :=
  ⟨[(1907, 2768), (3099, 3103), (7742, 7747), (9205, 9206)], [3102, 7746, 9205]⟩

def epilogueDecl : Decl :=
  ⟨[(2769, 3103), (7742, 7747), (9205, 9206)], [3102, 7746, 9205]⟩

def softmaxDecl : Decl := ⟨[(3102, 7747), (9205, 9206)], [7746, 9205]⟩

def correctionDecl : Decl := ⟨[(7746, 9206)], [9205]⟩

/-- Every region is closed up to its exits. -/
theorem closed : [startupDecl, loaderDecl, mmaDecl, epilogueDecl, softmaxDecl,
    correctionDecl].all (fun d => CodeCheck.closedFrom d.region d.exits 0 kernel.code) = true := by
  kernel_rfl

/-- The startup's event instructions: its sites and the first instructions of the roles. -/
def startupSites : List Nat :=
  [25, 34, 35, 46, 50, 51, 56, 60, 61, 62, 66, 67, 68, 73, 77, 78, 79, 80, 84, 85, 90, 94, 95,
    96, 100, 101, 105, 109, 110, 111, 115, 116, 119, 123, 124, 125, 129, 130, 135, 139, 140, 141,
    145, 146, 151, 155, 156, 157, 161, 162, 166, 170, 171, 172, 173, 179, 1907, 2769, 3102, 7746,
    9205]

theorem startup_sites : CodeCheck.sitesFrom startupDecl.region 0 kernel.code = startupSites := by
  kernel_rfl

/-- Every startup site is an event instruction of the region. -/
theorem Startup.site_mem (s : Startup.Site) : s.pc ∈ startupSites := by
  cases s with
  | sh j => fin_cases j <;> decide
  | elect j => fin_cases j <;> decide
  | init n => fin_cases n <;> decide
  | fence => decide
  | bar => decide
  | enter r => cases r <;> decide

/-- The output warp's event instructions: its sites and the two exits of its dispatch tests. -/
def epilogueSites : List Nat :=
  [2769, 2776, 2777, 2796, 2800, 2804, 2808, 2812, 2816, 2835, 2837, 2858, 2861, 2864, 2867, 2870,
    2873, 2887, 2894, 2898, 2953, 2954, 2958, 2963, 2965, 2967, 2969, 2970, 2972, 2976, 2977, 2978,
    2979, 2980, 2981, 2983, 2984, 2985, 2989, 2990, 3009, 3012, 3015, 3018, 3021, 3024, 3043, 3045,
    3066, 3069, 3072, 3075, 3078, 3081, 3092, 3097, 3098, 3102, 7746, 9205]

theorem epilogue_sites :
    CodeCheck.sitesFrom epilogueDecl.region 0 kernel.code = epilogueSites := by
  kernel_rfl

/-- The MMA warp's event instructions: its sites and the three exits of its dispatch tests. -/
def mmaSites : List Nat :=
  [1907, 1909, 1910, 1911, 1916, 1940, 1941, 1960, 1964, 1968, 1972, 1976, 1980, 1999, 2001, 2022,
    2025, 2028, 2031, 2034, 2037, 2050, 2057, 2061, 2112, 2113, 2116, 2141, 2145, 2151, 2152,
    2153, 2197, 2198, 2199, 2200, 2201, 2202, 2203, 2204, 2205, 2208, 2210, 2214, 2215, 2259,
    2260, 2261, 2262, 2263, 2264, 2265, 2266, 2267, 2270, 2271, 2274, 2294, 2297, 2307, 2308,
    2310, 2311, 2319, 2322, 2325, 2328, 2331, 2334, 2335, 2340, 2343, 2352, 2361, 2363, 2407,
    2408, 2409, 2410, 2411, 2412, 2413, 2414, 2415, 2418, 2419, 2423, 2425, 2426, 2434, 2437,
    2440, 2443, 2446, 2449, 2450, 2455, 2458, 2459, 2462, 2464, 2508, 2509, 2510, 2511, 2512,
    2513, 2514, 2515, 2516, 2519, 2520, 2523, 2534, 2537, 2538, 2541, 2545, 2548, 2558, 2559,
    2561, 2562, 2570, 2573, 2576, 2579, 2582, 2585, 2586, 2591, 2594, 2595, 2599, 2601, 2602,
    2610, 2613, 2616, 2619, 2622, 2625, 2626, 2631, 2634, 2635, 2638, 2639, 2642, 2643, 2646,
    2653, 2654, 2673, 2676, 2679, 2682, 2685, 2688, 2707, 2709, 2730, 2733, 2736, 2739, 2742,
    2745, 2756, 2761, 2762, 2763, 2764, 2766, 3102, 7746, 9205]

theorem mma_sites : CodeCheck.sitesFrom mmaDecl.region 0 kernel.code = mmaSites := by
  kernel_rfl

/-- Every site of the MMA warp's machine, and of its allocation prefix, is an event instruction
of its region. -/
theorem Mma.site_mem (s : Mma.Site) : s.pc ∈ mmaSites ∧ ∀ s' : Mma.Start, s'.pc ∈ mmaSites := by
  refine ⟨?_, fun s' => by cases s' <;> decide⟩
  cases s with
  | word k | down k | total k => cases k <;> decide
  | up k j => cases k <;> fin_cases j <;> decide
  | vote l | pre l | tiles l | relinq l | bar2 l | dealloc l | exit l => cases l <;> decide
  | wt k | sh k | eq k | ep k | ce k | cm k => fin_cases k <;> decide
  | qk b j | pv b j => fin_cases b <;> fin_cases j <;> decide
  | mw b l => fin_cases b <;> cases l <;> decide
  | _ => decide

/-- The loader warps' event instructions: their sites (the two rounds of each page-table and
pointer loop share their pcs) and the first instructions of the roles their dispatch tests could
reach. -/
def loaderSites : List Nat :=
  [179, 186, 187, 206, 210, 214, 218, 222, 226, 245, 247, 268, 271, 274, 277, 280, 283, 297, 304,
    308, 381, 382, 385, 503, 506, 511, 517, 525, 527, 534, 543, 544, 545, 550, 551, 553, 554, 558,
    559, 561, 562, 566, 567, 569, 570, 574, 575, 577, 578, 582, 583, 585, 586, 590, 591, 593, 594,
    598, 599, 601, 602, 606, 607, 609, 610, 611, 615, 616, 618, 619, 623, 624, 626, 627, 631, 632,
    634, 635, 639, 640, 642, 643, 647, 648, 650, 651, 655, 656, 658, 659, 663, 664, 666, 667, 671,
    672, 673, 674, 679, 682, 686, 687, 693, 694, 700, 704, 707, 711, 712, 719, 720, 727, 730, 733,
    737, 738, 745, 746, 753, 756, 759, 763, 765, 771, 772, 779, 782, 790, 792, 799, 804, 805, 806,
    810, 811, 812, 813, 816, 817, 818, 819, 822, 823, 824, 825, 828, 829, 830, 831, 834, 835, 836,
    837, 840, 841, 842, 843, 846, 847, 848, 849, 852, 853, 854, 855, 856, 859, 860, 861, 862, 865,
    866, 867, 868, 871, 872, 873, 874, 877, 878, 879, 880, 883, 884, 885, 886, 889, 890, 891, 892,
    895, 896, 897, 898, 901, 902, 903, 904, 946, 949, 953, 960, 968, 970, 977, 1003, 1004, 1005,
    1012, 1013, 1015, 1016, 1021, 1022, 1024, 1025, 1029, 1030, 1032, 1033, 1037, 1038, 1040, 1041,
    1045, 1046, 1048, 1049, 1053, 1054, 1056, 1057, 1061, 1062, 1064, 1065, 1069, 1070, 1072, 1073,
    1074, 1078, 1079, 1081, 1082, 1086, 1087, 1089, 1090, 1094, 1095, 1097, 1098, 1102, 1103, 1105,
    1106, 1110, 1111, 1113, 1114, 1118, 1119, 1121, 1122, 1126, 1127, 1129, 1130, 1134, 1135, 1136,
    1137, 1146, 1149, 1153, 1154, 1163, 1164, 1173, 1175, 1178, 1182, 1183, 1191, 1192, 1200, 1206,
    1214, 1216, 1223, 1238, 1239, 1240, 1247, 1248, 1249, 1250, 1254, 1255, 1256, 1257, 1260, 1261,
    1262, 1263, 1266, 1267, 1268, 1269, 1272, 1273, 1274, 1275, 1278, 1279, 1280, 1281, 1284, 1285,
    1286, 1287, 1290, 1291, 1292, 1293, 1294, 1297, 1298, 1299, 1300, 1303, 1304, 1305, 1306, 1309,
    1310, 1311, 1312, 1315, 1316, 1317, 1318, 1321, 1322, 1323, 1324, 1327, 1328, 1329, 1330, 1333,
    1334, 1335, 1336, 1339, 1340, 1341, 1342, 1361, 1364, 1368, 1370, 1376, 1377, 1383, 1416, 1419,
    1423, 1430, 1438, 1440, 1447, 1469, 1470, 1471, 1477, 1478, 1480, 1481, 1486, 1487, 1489, 1490,
    1494, 1495, 1497, 1498, 1502, 1503, 1505, 1506, 1510, 1511, 1513, 1514, 1518, 1519, 1521, 1522,
    1526, 1527, 1529, 1530, 1534, 1535, 1537, 1538, 1539, 1543, 1544, 1546, 1547, 1551, 1552, 1554,
    1555, 1559, 1560, 1562, 1563, 1567, 1568, 1570, 1571, 1575, 1576, 1578, 1579, 1583, 1584, 1586,
    1587, 1591, 1592, 1594, 1595, 1599, 1600, 1601, 1602, 1611, 1619, 1621, 1628, 1632, 1633, 1634,
    1640, 1641, 1642, 1643, 1647, 1648, 1649, 1650, 1653, 1654, 1655, 1656, 1659, 1660, 1661, 1662,
    1665, 1666, 1667, 1668, 1671, 1672, 1673, 1674, 1677, 1678, 1679, 1680, 1683, 1684, 1685, 1686,
    1687, 1690, 1691, 1692, 1693, 1696, 1697, 1698, 1699, 1702, 1703, 1704, 1705, 1708, 1709, 1710,
    1711, 1714, 1715, 1716, 1717, 1720, 1721, 1722, 1723, 1726, 1727, 1728, 1729, 1732, 1733, 1734,
    1735, 1750, 1751, 1771, 1774, 1777, 1780, 1783, 1786, 1805, 1807, 1828, 1831, 1834, 1837, 1840,
    1843, 1855, 1860, 1861, 1866, 1877, 1888, 1893, 1896, 1900, 1907, 2769, 3102, 7746, 9205]

theorem loader_sites : CodeCheck.sitesFrom loaderDecl.region 0 kernel.code = loaderSites := by
  kernel_rfl

/-- Every site of the loader warps' machine is an event instruction of their region. -/
theorem Loader.site_mem (s : Loader.Site) : s.pc ∈ loaderSites := by
  cases s with
  | word k | down k | total k => cases k <;> decide +kernel
  | up k j => cases k <;> fin_cases j <;> decide +kernel
  | vote l | pre l | tiles l => cases l <;> decide +kernel
  | pgLd per it | pgSt per it | rwSt per it => cases per <;> fin_cases it <;> decide +kernel
  | slot per v | commit per v | arrive per v => cases per <;> cases v <;> decide +kernel
  | ptP per v it | ptR per v it | ptS per v it =>
    cases per <;> cases v <;> fin_cases it <;> decide +kernel
  | lw per v h => cases per <;> cases v <;> fin_cases h <;> decide +kernel
  | xl per v i | xh per v i => cases per <;> cases v <;> fin_cases i <;> decide +kernel
  | cp per v i c => cases per <;> cases v <;> fin_cases i <;> fin_cases c <;> decide +kernel
  | tw t | ta t => fin_cases t <;> decide +kernel
  | te t e => fin_cases t <;> fin_cases e <;> decide +kernel
  | tc t c => fin_cases t <;> fin_cases c <;> decide +kernel
  | dw k => fin_cases k <;> decide +kernel
  | _ => decide +kernel

/-- The correction warps' event instructions: their sites and the common return. -/
def correctionSites : List Nat :=
  [7746, 7747, 7752, 7754, 7761, 7762, 7781, 7785, 7789, 7793, 7797, 7801, 7821, 7823, 7844,
    7847, 7850, 7853, 7856, 7859, 7873, 7880, 7884, 7955, 7956, 7959, 7985, 7987, 7988, 8006,
    8007, 8009, 8012, 8038, 8039, 8064, 8065, 8090, 8091, 8116, 8117, 8142, 8143, 8168, 8169,
    8194, 8195, 8220, 8221, 8223, 8224, 8225, 8226, 8228, 8231, 8257, 8258, 8283, 8284, 8309,
    8310, 8335, 8336, 8361, 8362, 8387, 8388, 8413, 8414, 8439, 8440, 8442, 8443, 8464, 8465,
    8466, 8467, 8468, 8473, 8476, 8480, 8485, 8492, 8496, 8499, 8504, 8511, 8515, 8518, 8523,
    8530, 8534, 8537, 8542, 8549, 8553, 8555, 8560, 8567, 8570, 8572, 8577, 8584, 8587, 8589,
    8594, 8601, 8604, 8606, 8611, 8618, 8621, 8623, 8628, 8635, 8638, 8640, 8645, 8652, 8655,
    8657, 8662, 8669, 8672, 8674, 8679, 8686, 8689, 8691, 8696, 8703, 8706, 8708, 8713, 8720,
    8723, 8725, 8730, 8737, 8740, 8742, 8747, 8754, 8757, 8758, 8759, 8760, 8761, 8762, 8763,
    8764, 8769, 8772, 8776, 8781, 8788, 8792, 8795, 8800, 8807, 8811, 8814, 8819, 8826, 8830,
    8833, 8838, 8845, 8849, 8851, 8856, 8863, 8866, 8868, 8873, 8880, 8883, 8885, 8890, 8897,
    8900, 8902, 8907, 8914, 8917, 8919, 8924, 8931, 8934, 8936, 8941, 8948, 8951, 8953, 8958,
    8965, 8968, 8970, 8975, 8982, 8985, 8987, 8992, 8999, 9002, 9004, 9009, 9016, 9019, 9021,
    9026, 9033, 9036, 9038, 9043, 9050, 9053, 9054, 9055, 9056, 9073, 9082, 9089, 9090, 9110,
    9113, 9116, 9119, 9122, 9125, 9144, 9146, 9167, 9170, 9173, 9176, 9179, 9182, 9194, 9199,
    9200, 9201, 9204, 9205]

theorem correction_sites :
    CodeCheck.sitesFrom correctionDecl.region 0 kernel.code = correctionSites := by
  kernel_rfl

/-- Every site of the correction warps' machine is an event instruction of their region. -/
theorem Correction.site_mem (s : Correction.Site) : s.pc ∈ correctionSites := by
  cases s with
  | word k | down k | total k => cases k <;> decide
  | up k j => cases k <;> fin_cases j <;> decide
  | vote l | pre l | tiles l | wend l | barEnd l | exit l => cases l <;> decide
  | arr k | nb k | rbar k | rscale k | rvote k | rwait k | fbar k | fsum k | fmax k | farr k
    | fence k | lse k => fin_cases k <;> decide
  | rarr st k | fw st k | fdone st k => fin_cases st <;> fin_cases k <;> decide
  | rld st c | rldw st c | rst st c => fin_cases st <;> fin_cases c <;> decide
  | fld st j | fwl st j => fin_cases st <;> fin_cases j <;> decide
  | fst st j h => fin_cases st <;> fin_cases j <;> fin_cases h <;> decide
  | _ => decide

/-! ### The glue -/

/-- A fragment that stops at its first event, at `pc`: a role not yet migrated. -/
@[reducible] def stop (L : Launch) (g pc : Nat) : Flow.Code kernel Assumptions.all L g where
  D := Unit
  init := ()
  pc := fun _ => pc
  facts := fun _ => []
  inv := fun _ => True
  next := fun _ _ => some none

/-- The roles of the glue: the migrated ones, and the stub of every entry. -/
inductive Role where
  | epilogue
  | mma
  | correction
  /-- The loader warps: warp 15 for `true`, warp 14 for `false` (`Loader.wOf`). -/
  | loader (b : Bool)
  | stub (r : Startup.Entry)
  /-- The softmax warps (0 to 7), on the data machine (`SmWarp.codeT`). -/
  | softmax
  deriving DecidableEq

/-- The fragment of each role. -/
@[reducible] def frag (p : Params) (L : Launch) (g : Nat) :
    Role → Flow.Code kernel Assumptions.all L g
  | .mma => Mma.M p L g
  | .epilogue => Epilogue.M p L g
  | .correction => Correction.code p L g
  | .loader b => Loader.F p L g b
  | .stub r => stop L g r.pc
  | .softmax => SmWarp.codeT p L g

/-- The startup's words the roles rely on: the shared base and, per role, the warp index (the
correction warps' first state holds the thread's own warp index, which feeds their named
barriers). -/
def Gate (L : Launch) (g : Nat) : Startup.Entry → Startup.D → Bool
  | .mma, d => d.x1 == BitVec.ofNat 64 L.sharedBase && d.x3 == BitVec.ofNat 64 12
  | .epilogue, d => d.x1 == BitVec.ofNat 64 L.sharedBase && d.x3 == BitVec.ofNat 64 13
  | .correction, d =>
      d.x1 == BitVec.ofNat 64 L.sharedBase && d.x3 == BitVec.ofNat 64 (g % L.block / 32)
  | .loader, d => d.x1 == BitVec.ofNat 64 L.sharedBase &&
      (d.x3 == BitVec.ofNat 64 14 || d.x3 == BitVec.ofNat 64 15)
  | .softmax, d =>
      d.x1 == BitVec.ofNat 64 L.sharedBase && d.x3 == BitVec.ofNat 64 (g % L.block / 32) &&
        decide (g % L.block / 32 < 8)
  | _, _ => false

/-- The role an entry enters when its gate holds; the loader's fragment is chosen by the warp
word the dispatch compared. -/
def roleOf (d : Startup.D) : Startup.Entry → Role
  | .mma => .mma
  | .epilogue => .epilogue
  | .correction => .correction
  | .loader => .loader (d.x3 == BitVec.ofNat 64 15)
  | .softmax => .softmax
  | r => .stub r

/-- The startup's exits: the state `enter r` enters role `r` when its gate holds. -/
def exit (L : Launch) (g : Nat) (d : Startup.D) : Option Role :=
  match d.site with
  | .enter r => some (if Gate L g r d then roleOf d r else .stub r)
  | _ => none

/-- The startup, then the role of the thread's warp. -/
@[reducible] def glued (p : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g :=
  Code.glue (Startup.code p L g) (frag p L g) (exit L g)

/-! ### The ghost ledger -/

deriving instance DecidableEq for Loader.Cnt

/-- The classes of events the thread machine counts: warp shuffles and full-mask ballots (the
instances of the warp collectives), all events (the position in the trace), and the output
warp's tensor stores, bulk-group commits and read waits, arrivals, and per stage the successful
polls of its ready barrier and the arrivals on its free barrier (the library's `okPoll` and
`arrivesOn`, the counts the unit hand-off is stated in), the MMA warp's ledger classes (`Mma.Cnt`),
the correction warps' ledger classes (`Correction.Cnt`), the loader warps' ledger classes
(`Loader.Cnt`), the softmax warps' classes whose counts are closed forms in the places
(`Softmax.Cnt.pointed`, counted on warps 0 to 7 only), and undefined-behaviour events (a
reference invariant may be guarded by none so far). -/
inductive Cls where
  | shfl
  | vote
  | all
  | store
  | commit
  | wait
  | arrive
  | poll (st : Fin 2)
  | freed (st : Fin 2)
  | mma (c : Mma.Cnt)
  | corr (c : Correction.Cnt)
  | load (c : Loader.Cnt)
  | soft (c : Softmax.Cnt)
  | ub
  deriving DecidableEq

/-- The events of each class. -/
def cls (L : Launch) (g : Nat) : Cls → Event → Bool
  | .shfl => Execution.isShfl
  | .vote => isFullVote
  | .all => fun _ => true
  | .store => Epilogue.isStore
  | .commit => Epilogue.isCommit
  | .wait => Epilogue.isWait
  | .arrive => Epilogue.isArrive
  | .poll st => Flow.okPoll (Epilogue.readyLoc L g st)
  | .freed st => Flow.arrivesOn (Epilogue.freeLoc L g st)
  | .mma c => Mma.cls L g c
  | .corr c => Correction.cls L g c
  | .load c => Loader.cls L g c
  | .soft c => fun e => Softmax.cls L g c e && c.pointed && decide (g % L.block / 32 < 8)
  | .ub => fun e => match e.kind with | .ub _ => true | _ => false

/-- **The thread machine**: the glued machine with its ghost ledger. Its state before a thread's
`k`-th event carries the counts of each class among the thread's first `k` events
(`Frame.count_eq`). -/
@[reducible] def thread (p : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g :=
  (glued p L g).counted (cls L g)

end
end PTX.Kernels.TmlFa4Fwd.Proof2
