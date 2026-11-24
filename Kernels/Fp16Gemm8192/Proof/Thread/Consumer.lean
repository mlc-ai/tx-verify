-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Isa.Tmpl
public import Kernels.Fp16Gemm8192.Proof.Thread.Loader
public import Kernels.Fp16Gemm8192.Proof.Support.AssumptionFacts
public import Lemmas.Flow.Footprint

public import Lemmas.Flow.RoundTrip
public import Lemmas.Flow.Cvt
public import Kernels.Fp16Gemm8192.Flow.CvtRuns

@[expose] public section

/-! # The consumer warps as abstract states

Warps 0 to 7 (all lanes) run the epilogue. Each task, a thread polls the CLC response, reads and
queries it, synchronizes its warp group on a named barrier (the group's first thread releases the
response), waits for its accumulator (Tensor Memory columns `256 * (w / 4)`), loads its 256 values,
packs them to half precision, releases the accumulator, and stores the tile in eight slices through
a staging buffer (the group's first thread issues a TMA store of each). It then takes the next task
or drains its stores and leaves; warp 0 also returns Tensor Memory.

An abstract state is the next event with the current and next tile, the CLC and accumulator
parities, the response read, the claimed first CTA and the accumulator values loaded so far.
After a load's wait the code converts the load's values to pairs of halves; a conversion that
faults kills the thread (`next` gives `none`), and every other conversion, of an infinity or a NaN
too, writes its pair (`Flow.cvtPairV`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

inductive Site where
  | setMaxReg
  /-- The CLC response: poll, read, two queries, fence, group barrier, release. -/
  | clcWait | clcLoad | clcStatus | clcFirst | clcFence | clcBar | ack
  /-- The accumulator-full poll, the sixteen loads and their waits, the release. -/
  | accWait
  | load (j : Fin 16) | loadWait (j : Fin 16)
  | accArrive
  /-- Slice `k` of the epilogue: wait for the staging buffer, barrier, four stores,
  barrier, and on the group's first thread the fence, the TMA store and its commit. -/
  | drain (k : Fin 8) | barA (k : Fin 8) | store (k : Fin 8) (i : Fin 4) (el : Fin 4) | barB (k :
    Fin 8)
  | fence (k : Fin 8) | tma (k : Fin 8) | commit (k : Fin 8)
  /-- The exit: drain all stores, the cluster barrier, warp 0's Tensor Memory release. -/
  | finalDrain | exitArrive | exitWait | relinquish | ldBase | dealloc | exit
  deriving DecidableEq

def Site.pc : Site → Nat
  | .setMaxReg => Flow.setMaxReg_1
  | .clcWait => Flow.mbarWait_21 | .clcLoad => Flow.loadAcquire_3 | .clcStatus => Flow.clcQuery_6
  | .clcFirst => Flow.clcQuery_7 | .clcFence => Flow.fenceProxy_4 | .clcBar => Flow.bar_0
  | .ack => Flow.mbarArrive_12
  | .accWait => Flow.mbarWait_22
  | .load j => Flow.tmemLoad.getD j.val 0 | .loadWait j => Flow.tmemWait.getD j.val 0
  | .accArrive => Flow.mbarArrive_13
  | .drain k => Flow.bulkWait.getD k.val 0
  | .barA k => Flow.bar.getD (1 + 2 * k.val) 0 | .barB k => Flow.bar.getD (2 + 2 * k.val) 0
  | .store k i _ => Flow.store.getD (4 * k.val + i.val) 0
  | .fence k => Flow.fenceProxy.getD (5 + k.val) 0
  | .tma k => Flow.tensorCopy.getD (24 + k.val) 0
  | .commit k => Flow.bulkCommit.getD k.val 0
  | .finalDrain => Flow.bulkWait_8 | .exitArrive => Flow.clusterArrive_1
  | .exitWait => Flow.clusterWait_1 | .relinquish => Flow.tmemRelinquish_0
  | .ldBase => Flow.load_0 | .dealloc => Flow.tmemDealloc_0 | .exit => Flow.exit_0

/-- The element of a four-element store the thread is at (the instruction's sub-step). -/
def Site.sub : Site → Nat
  | .store _ _ el => el.val
  | _ => 0

/-- A consumer state: the site, the current tile `(m, n)` and the next one `(m', n')`, the
CLC and accumulator parities, the response read, the claimed first CTA and the
accumulator values loaded so far. -/
structure D where
  site : Site
  m : Nat
  n : Nat
  m' : Nat
  n' : Nat
  cp : Nat
  ap : Nat
  resp : Value
  x : Nat
  /-- Accumulator value `i` of the tile row, as loaded so far. -/
  acc : Nat → Value
  /-- The Tensor Memory base address warp 0 reads back before deallocating. -/
  base : Value

/-- The accumulator registers: register `r` holds value `i` of the tile row's accumulator
(load `i / 16`, position `i % 16`). -/
def dataTable : List (Nat × Nat) :=
  [(161, 0), (160, 1), (163, 2), (162, 3), (165, 4), (164, 5),
   (167, 6), (166, 7), (169, 8), (168, 9), (171, 10), (170, 11),
   (173, 12), (172, 13), (175, 14), (174, 15), (178, 16), (177, 17),
   (180, 18), (179, 19), (182, 20), (181, 21), (184, 22), (183, 23),
   (186, 24), (185, 25), (188, 26), (187, 27), (190, 28), (189, 29),
   (192, 30), (191, 31), (195, 32), (194, 33), (197, 34), (196, 35),
   (199, 36), (198, 37), (201, 38), (200, 39), (203, 40), (202, 41),
   (205, 42), (204, 43), (207, 44), (206, 45), (209, 46), (208, 47),
   (212, 48), (211, 49), (214, 50), (213, 51), (216, 52), (215, 53),
   (218, 54), (217, 55), (220, 56), (219, 57), (222, 58), (221, 59),
   (224, 60), (223, 61), (226, 62), (225, 63), (229, 64), (228, 65),
   (231, 66), (230, 67), (233, 68), (232, 69), (235, 70), (234, 71),
   (237, 72), (236, 73), (239, 74), (238, 75), (241, 76), (240, 77),
   (243, 78), (242, 79), (246, 80), (245, 81), (248, 82), (247, 83),
   (250, 84), (249, 85), (252, 86), (251, 87), (254, 88), (253, 89),
   (256, 90), (255, 91), (258, 92), (257, 93), (260, 94), (259, 95),
   (263, 96), (262, 97), (265, 98), (264, 99), (267, 100), (266, 101),
   (269, 102), (268, 103), (271, 104), (270, 105), (273, 106), (272, 107),
   (275, 108), (274, 109), (277, 110), (276, 111), (280, 112), (279, 113),
   (282, 114), (281, 115), (284, 116), (283, 117), (286, 118), (285, 119),
   (288, 120), (287, 121), (290, 122), (289, 123), (292, 124), (291, 125),
   (294, 126), (293, 127), (297, 128), (296, 129), (299, 130), (298, 131),
   (301, 132), (300, 133), (303, 134), (302, 135), (305, 136), (304, 137),
   (307, 138), (306, 139), (309, 140), (308, 141), (311, 142), (310, 143),
   (314, 144), (313, 145), (316, 146), (315, 147), (318, 148), (317, 149),
   (320, 150), (319, 151), (322, 152), (321, 153), (324, 154), (323, 155),
   (326, 156), (325, 157), (328, 158), (327, 159), (331, 160), (330, 161),
   (333, 162), (332, 163), (335, 164), (334, 165), (337, 166), (336, 167),
   (339, 168), (338, 169), (341, 170), (340, 171), (343, 172), (342, 173),
   (345, 174), (344, 175), (348, 176), (347, 177), (350, 178), (349, 179),
   (352, 180), (351, 181), (354, 182), (353, 183), (356, 184), (355, 185),
   (358, 186), (357, 187), (360, 188), (359, 189), (362, 190), (361, 191),
   (365, 192), (364, 193), (367, 194), (366, 195), (369, 196), (368, 197),
   (371, 198), (370, 199), (373, 200), (372, 201), (375, 202), (374, 203),
   (377, 204), (376, 205), (379, 206), (378, 207), (382, 208), (381, 209),
   (384, 210), (383, 211), (386, 212), (385, 213), (388, 214), (387, 215),
   (390, 216), (389, 217), (392, 218), (391, 219), (394, 220), (393, 221),
   (396, 222), (395, 223), (399, 224), (398, 225), (401, 226), (400, 227),
   (403, 228), (402, 229), (405, 230), (404, 231), (407, 232), (406, 233),
   (409, 234), (408, 235), (411, 236), (410, 237), (413, 238), (412, 239),
   (416, 240), (415, 241), (418, 242), (417, 243), (420, 244), (419, 245),
   (422, 246), (421, 247), (424, 248), (423, 249), (426, 250), (425, 251),
   (428, 252), (427, 253), (430, 254), (429, 255)]

/-- The packed half-precision registers: `(r, a, b)` packs the accumulator values `a` (low
half) and `b` (high half). -/
def packTable : List (Nat × Nat × Nat) :=
  [(436, 1, 0), (437, 3, 2), (438, 5, 4), (439, 7, 6), (440, 9, 8),
   (441, 11, 10), (442, 13, 12), (443, 15, 14), (444, 17, 16), (445, 19, 18),
   (446, 21, 20), (447, 23, 22), (448, 25, 24), (449, 27, 26), (450, 29, 28),
   (451, 31, 30), (458, 33, 32), (459, 35, 34), (460, 37, 36), (461, 39, 38),
   (462, 41, 40), (463, 43, 42), (464, 45, 44), (465, 47, 46), (466, 49, 48),
   (467, 51, 50), (468, 53, 52), (469, 55, 54), (470, 57, 56), (471, 59, 58),
   (472, 61, 60), (473, 63, 62), (481, 65, 64), (482, 67, 66), (483, 69, 68),
   (484, 71, 70), (485, 73, 72), (486, 75, 74), (487, 77, 76), (488, 79, 78),
   (489, 81, 80), (490, 83, 82), (491, 85, 84), (492, 87, 86), (493, 89, 88),
   (494, 91, 90), (495, 93, 92), (496, 95, 94), (504, 97, 96), (505, 99, 98),
   (506, 101, 100), (507, 103, 102), (508, 105, 104), (509, 107, 106), (510, 109, 108),
   (511, 111, 110), (512, 113, 112), (513, 115, 114), (514, 117, 116), (515, 119, 118),
   (516, 121, 120), (517, 123, 122), (518, 125, 124), (519, 127, 126), (527, 129, 128),
   (528, 131, 130), (529, 133, 132), (530, 135, 134), (531, 137, 136), (532, 139, 138),
   (533, 141, 140), (534, 143, 142), (535, 145, 144), (536, 147, 146), (537, 149, 148),
   (538, 151, 150), (539, 153, 152), (540, 155, 154), (541, 157, 156), (542, 159, 158),
   (550, 161, 160), (551, 163, 162), (552, 165, 164), (553, 167, 166), (554, 169, 168),
   (555, 171, 170), (556, 173, 172), (557, 175, 174), (558, 177, 176), (559, 179, 178),
   (560, 181, 180), (561, 183, 182), (562, 185, 184), (563, 187, 186), (564, 189, 188),
   (565, 191, 190), (574, 193, 192), (575, 195, 194), (576, 197, 196), (577, 199, 198),
   (579, 201, 200), (580, 203, 202), (581, 205, 204), (582, 207, 206), (584, 209, 208),
   (585, 211, 210), (586, 213, 212), (587, 215, 214), (589, 217, 216), (590, 219, 218),
   (591, 221, 220), (592, 223, 222), (602, 225, 224), (603, 227, 226), (604, 229, 228),
   (605, 231, 230), (607, 233, 232), (608, 235, 234), (609, 237, 236), (610, 239, 238),
   (612, 241, 240), (613, 243, 242), (614, 245, 244), (615, 247, 246), (617, 249, 248),
   (618, 251, 250), (619, 253, 252), (620, 255, 254)]

/-- The thread's index in the block, warp and cluster rank. -/
abbrev tidOf (L : Launch) (g : Nat) : Nat := g % L.block

/-- The staging offset of the thread's `k`-th sixteen-byte chunk (swizzled). -/
def stage (tid k : Nat) : Nat :=
  1024 * (tid / 32 % 4) + 8192 * (tid / 32 / 4) + 64 * (tid / 2 % 16) + 32 * (tid % 2) +
    8 * ((tid / 2 % 4) ^^^ k)

/-- The consumer thread's register values outside the accumulator. -/
def values (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let tid := tidOf L g
  let w := tid / 32
  let rank := (g / L.block) % 2
  let lead := (w % 4) ||| (tid % 32)
  let sb := L.sharedBase
  [(47, b32 tid), (48, b32 w), (53, b32 lead),
   (145, b32 (w / 4 + 1)), (435, b32 (w / 4 + 10)),
   (157, b32 (sb + 8 * (w / 4) + 72)), (431, b32 (sb + 8 * (w / 4) + 88)),
   (158, b32 10000000),
   (159, b32 (256 * (w / 4) + 0)), (176, b32 (256 * (w / 4) + 16)), (193, b32 (256 * (w / 4) + 32)),
   (210, b32 (256 * (w / 4) + 48)), (227, b32 (256 * (w / 4) + 64)),
     (244, b32 (256 * (w / 4) + 80)),
   (261, b32 (256 * (w / 4) + 96)), (278, b32 (256 * (w / 4) + 112)),
     (295, b32 (256 * (w / 4) + 128)),
   (312, b32 (256 * (w / 4) + 144)), (329, b32 (256 * (w / 4) + 160)),
     (346, b32 (256 * (w / 4) + 176)),
   (363, b32 (256 * (w / 4) + 192)), (380, b32 (256 * (w / 4) + 208)),
     (397, b32 (256 * (w / 4) + 224)),
   (414, b32 (256 * (w / 4) + 240)),
   (573, b32 (sb + 197632 + 2 * stage tid 0)), (578, b32 (sb + 197632 + 2 * stage tid 1)),
   (583, b32 (sb + 197632 + 2 * stage tid 2)), (588, b32 (sb + 197632 + 2 * stage tid 3)),
   (601, b32 (sb + 205824 + 2 * stage tid 0)), (606, b32 (sb + 205824 + 2 * stage tid 1)),
   (611, b32 (sb + 205824 + 2 * stage tid 2)), (616, b32 (sb + 205824 + 2 * stage tid 3)),
   (54, b32 (128 * (w / 4))), (596, b32 (sb + 197632 + 16384 * (w / 4))),
   (624, b32 (sb + 205824 + 16384 * (w / 4))),
   (146, b32 sb), (140, b32 (sb + 104)), (141, b32 10000000), (142, b32 (sb + 144)),
   (969, d.resp), (143, b32 d.x),
   (1028, .pred (decide (d.site = .clcFirst))), (1029, .pred true),
   (1031, .pred true),
   (147, b32 (sb + 128)), (148, b32 0), (150, b32 1),
   (149, .ptr 32 false (.shared (g / L.block) (2 * ((g / L.block) / 2)))
       (BitVec.ofNat 64 (sb + 128))),
   (432, b32 0), (434, b32 1),
   (433, .ptr 32 false (.shared (g / L.block) (2 * ((g / L.block) / 2)))
       (BitVec.ofNat 64 (sb + 8 * (w / 4) + 88))),
   (889, b32 d.cp), (890, b32 d.ap),
   (887, b32 d.m), (888, b32 d.n), (892, b32 d.m'), (891, b32 d.n'),
   (8, .pred (decide (lead ≠ 0))), (11, .pred (decide (lead ≠ 0))), (12, .pred (decide (lead ≠ 0))),
     (13, .pred (decide (lead ≠ 0))), (14, .pred (decide (lead ≠ 0))),
     (15, .pred (decide (lead ≠ 0))), (16, .pred (decide (lead ≠ 0))),
     (17, .pred (decide (lead ≠ 0))), (18, .pred (decide (lead ≠ 0))),
   (19, .pred (decide (d.x ≠ Loader.none32))),
   (453, b32 (256 * d.n + 0)), (454, b32 (512 * d.m + 128 * (w / 4) + 256 * rank)),
   (475, b32 (256 * d.n + 32)), (476, b32 (512 * d.m + 128 * (w / 4) + 256 * rank)),
   (498, b32 (256 * d.n + 64)), (499, b32 (512 * d.m + 128 * (w / 4) + 256 * rank)),
   (521, b32 (256 * d.n + 96)), (522, b32 (512 * d.m + 128 * (w / 4) + 256 * rank)),
   (544, b32 (256 * d.n + 128)), (545, b32 (512 * d.m + 128 * (w / 4) + 256 * rank)),
   (567, b32 (256 * d.n + 160)), (568, b32 (512 * d.m + 128 * (w / 4) + 256 * rank)),
   (594, b32 (256 * d.n + 192)), (595, b32 (512 * d.m + 128 * (w / 4) + 256 * rank)),
   (622, b32 (256 * d.n + 224)), (623, b32 (512 * d.m + 128 * (w / 4) + 256 * rank)),
   (894, .ptr 64 false (.param "gemm_kernel_param_2") 0),
   (907, .ptr 64 true (.param "gemm_kernel_param_2") 0), (908, b64 1364590687093260288),
   (909, .ptr 64 true (.param "gemm_kernel_param_2") 0), (910, b64 1364590687093260288),
   (911, .ptr 64 true (.param "gemm_kernel_param_2") 0), (912, b64 1364590687093260288),
   (913, .ptr 64 true (.param "gemm_kernel_param_2") 0), (914, b64 1364590687093260288),
   (915, .ptr 64 true (.param "gemm_kernel_param_2") 0), (916, b64 1364590687093260288),
   (917, .ptr 64 true (.param "gemm_kernel_param_2") 0), (918, b64 1364590687093260288),
   (919, .ptr 64 true (.param "gemm_kernel_param_2") 0), (920, b64 1364590687093260288),
   (921, .ptr 64 true (.param "gemm_kernel_param_2") 0), (922, b64 1364590687093260288),
   (42, .pred (decide (w ≠ 0))), (873, b32 sb), (875, b32 512), (874, d.base)]

/-- The accumulator registers' values: a table register holds its entry as loaded, a packed
register the pair its conversion makes of its two entries. -/
def accValues (acc : Nat → Value) : List (Nat × Value) :=
  dataTable.map (fun p => (p.1, acc p.2)) ++
    packTable.map (fun p => (p.1, Flow.cvtPairV (acc p.2.1) (acc p.2.2)))

/-- A register's value: accumulator registers hold loaded reals, packed registers hold pairs
of halves, the others are given by `values`. -/
def valueOf (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((accValues d.acc ++ values L g d).lookup r).getD (b32 0)

def factsAt (L : Launch) (g pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g d)

theorem lookup_map_snd {β γ : Type} (l : List (Nat × β)) (f : β → γ) (a : Nat) :
    (l.map fun p => (p.1, f p.2)).lookup a = (l.lookup a).map f := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨b, x⟩ := p; simp only [List.map_cons, List.lookup_cons]
    split <;> simp_all

/-- A register of the accumulator table holds its entry. -/
theorem valueOf_data {L : Launch} {g : Nat} {d : D} {r : Nat} {i : Nat}
    (h : dataTable.lookup r = some i) : valueOf L g d r = d.acc i := by
  simp [valueOf, accValues, List.lookup_append, lookup_map_snd (f := d.acc), h]

/-- A packed register holds the pair its conversion makes of its two entries. -/
theorem valueOf_pack {L : Launch} {g : Nat} {d : D} {r : Nat} {a b : Nat}
    (h0 : dataTable.lookup r = none) (h : packTable.lookup r = some (a, b)) :
    valueOf L g d r = Flow.cvtPairV (d.acc a) (d.acc b) := by
  simp [valueOf, accValues, List.lookup_append, lookup_map_snd (f := d.acc), h0,
    lookup_map_snd (f := fun q : Nat × Nat => Flow.cvtPairV (d.acc q.1) (d.acc q.2)), h]

abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) := factsAt L g d.site.pc d

structure Inv (d : D) : Prop where
  m : d.m < 16
  n : d.n < 32
  m' : d.m' < 16
  n' : d.n' < 32
  cp : d.cp < 2
  ap : d.ap < 2
  x : d.x < 2 ^ 32

/-- The group's first thread (`%r7 = 0`) releases the response and issues the TMA stores. -/
def first (L : Launch) (g : Nat) : Bool := (tidOf L g / 32 % 4) ||| (tidOf L g % 32) = 0

/-- The tile the claimed CTA gives (the current one when nothing is claimed). -/
def nextTile (d : D) : Nat × Nat :=
  if d.x = Loader.none32 then (d.m, d.n) else (Loader.claimM d.x, Loader.claimN d.x)

/-- The accumulator after load `j`: its sixteen values at entries `16 j` to `16 j + 15`, the
other entries unchanged. -/
def loadAcc (acc : Nat → Value) (j : Nat) (vals : List Value) : Nat → Value :=
  fun i => if 16 * j ≤ i ∧ i < 16 * j + 16 then vals.getD (i - 16 * j) (b32 0) else acc i

/-- The conversions after the wait of load `j`, from the generated runs: `(d, a, b)` packs
`a` and `b` into `d`. -/
def cvts (j : Fin 16) : List (Nat × Nat × Nat) :=
  (Flow.cvtRuns.lookup ((Site.loadWait j).pc + 1)).getD []

/-- The conversion `c` does not fault on the accumulator entries its operands hold. -/
def cvtOk (acc : Nat → Value) (c : Nat × Nat × Nat) : Bool :=
  match dataTable.lookup c.2.1, dataTable.lookup c.2.2 with
  | some ia, some ib => (Flow.cvtPairE (acc ia) (acc ib)).toBool
  | _, _ => false

/-- No conversion after the wait of load `j` faults. -/
def chunkOk (acc : Nat → Value) (j : Fin 16) : Bool :=
  (cvts j).all (cvtOk acc)

def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .setMaxReg =>
    let c := g / L.block
    some (some { d with
      site := .clcWait, m := Loader.claimM c, n := Loader.claimN c, cp := 0, ap := 0 })
  | .clcWait => match e.kind with
    | .wait _ _ ok _ _ => some (some { d with site := if ok then .clcLoad else .clcWait })
    | _ => none
  | .clcLoad => match e.kind with
    | .rd _ bs => (Flow.responseOf bs).map fun r =>
      some { d with site := .clcStatus, resp := .clc r }
    | _ => none
  | .clcStatus => match e.kind with
    | .clcQuery _ r =>
      some (some { d with
        site := (if r.firstCta.isSome then .clcFirst else .clcFence), x := Loader.none32 })
    | _ => none
  | .clcFirst => match e.kind with
    | .clcQuery _ r =>
      some (some { d with
        site := .clcFence, x := ((r.firstCta.map fun c => c.1.toNat).getD Loader.none32) })
    | _ => none
  | .clcFence => some (some { d with site := .clcBar })
  | .clcBar =>
    if first L g then some (some { d with site := .ack })
    else some (some { d with site := .accWait, m' := (nextTile d).1, n' := (nextTile d).2 })
  | .ack => some (some { d with site := .accWait, m' := (nextTile d).1, n' := (nextTile d).2 })
  | .accWait => match e.kind with
    | .wait _ _ ok _ _ => some (some { d with site := if ok then .load 0 else .accWait })
    | _ => none
  | .load j => match e.kind with
    | .tc (.ld _ vals _) =>
      some (some { d with site := .loadWait j, acc := loadAcc d.acc j.val vals })
    | _ => none
  | .loadWait j =>
    if chunkOk d.acc j then
      if h : j.val + 1 < 16 then some (some { d with site := .load ⟨j.val + 1, h⟩ })
      else some (some { d with site := .accArrive })
    else none
  | .accArrive => some (some { d with site := .drain 0 })
  | .drain k => some (some { d with site := .barA k })
  | .barA k => some (some { d with site := .store k 0 0 })
  | .store k i el =>
    if h : el.val + 1 < 4 then some (some { d with site := .store k i ⟨el.val + 1, h⟩ })
    else if h : i.val + 1 < 4 then some (some { d with site := .store k ⟨i.val + 1, h⟩ 0 })
    else some (some { d with site := .barB k })
  | .barB k =>
    if first L g then some (some { d with site := .fence k })
    else some (some { d with site := .commit k })
  | .fence k => some (some { d with site := .tma k })
  | .tma k => some (some { d with site := .commit k })
  | .commit k =>
    if h : k.val + 1 < 8 then some (some { d with site := .drain ⟨k.val + 1, h⟩ })
    else if d.x = Loader.none32 then some (some { d with site := .finalDrain })
    else some (some { d with
      site := .clcWait, m := d.m', n := d.n', cp := 1 - d.cp, ap := 1 - d.ap })
  | .finalDrain => some (some { d with site := .exitArrive })
  | .exitArrive => some (some { d with site := .exitWait })
  | .exitWait =>
    if tidOf L g / 32 = 0 then some (some { d with site := .relinquish })
    else some (some { d with site := .exit })
  | .relinquish => some (some { d with site := .ldBase })
  | .ldBase => match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v => some (some { d with site := .dealloc, base := v })
      | .error _ => none
    | _ => none
  | .dealloc => some (some { d with site := .exit })
  | _ => none

/-- The value-table reduction used after evaluating a segment. -/
macro "cons_values" : tactic => `(tactic| simp only [valueOf, PTX.Flow.lookupLit, Option.getD_some,
  Option.getD_none,
  Bool.cond_true, Bool.cond_false])

/-- Evaluate a consumer segment from `h` and close the facts of its end state (as
`Loader.loader_seg`, with the consumer's value table). -/
syntax "cons_seg" term:max term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| cons_seg $h $hpre $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      have hbase := ($hpre).sharedRange
      unfold sharedBytes at hbase
      seg_fp $h using
        try cons_values
        all_goals seg_close [Launch.oneDim_ctaidOf ($hpre).oneDimLaunch.1,
          Launch.oneDim_clusterCtaidOf ($hpre).oneDimLaunch.1,
          Launch.oneDim_rankOfCta ($hpre).oneDimLaunch.1, Dim3.get, ($hpre).cluster, Loader.none32,
          $extra,*]))

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
