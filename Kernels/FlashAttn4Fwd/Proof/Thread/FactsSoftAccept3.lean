-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftShape

@[expose] public section

/-! # The softmax runs accept number words

When the scale word, the words of a state and its reference maximum (and, in a loop trip, its
row sum) are single-precision numbers, the runs the machine's conditions name accept them: the
exponentials (`ExpOk0`, `ExpOk1`), the tests of the row maximum (`max0T`, `max1T`) and the
row sums (`SumOk0`, `SumOk1`). Each is a shape check (`FactsSoftShape`) from the shapes of the
registers the run reads first. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

theorem has_float (x : ℝ) : OTy.f32.Has (.float .f32 x) := ⟨x, rfl⟩

theorem has_scale (hsc : ScaleOk L) : OTy.sbits.Has (scaleV L) :=
  ⟨⟨_, rfl, by simp only [truncBits, BitVec.toNat_ofNat]; omega⟩, _, hsc⟩

theorem has_scale2 (hsc : ScaleOk L) :
    (OTy.pr .sbits .sbits).Has (joinValue (scaleV L) (scaleV L)) := by
  obtain ⟨⟨b, hb, hlt⟩, hx⟩ := has_scale hsc
  obtain ⟨hsp, hby⟩ := join_self_bits hlt
  rw [hb] at hx ⊢
  refine ⟨hby, ?_, ?_⟩ <;> rw [hsp] <;> exact ⟨⟨b, rfl, hlt⟩, hx⟩

theorem has_word {w : Nat → Value} (hw : WordsF32 w) {k : Nat} (hk : k < 128) :
    OTy.f32.Has (w k) := hw k hk

theorem has_words {w : Nat → Value} (hw : WordsF32 w) {j k : Nat} (hj : j < 128) (hk : k < 128) :
    (OTy.pr .f32 .f32).Has (joinValue (w j) (w k)) := by
  obtain ⟨x, hx⟩ := hw j hj
  obtain ⟨y, hy⟩ := hw k hk
  rw [hx, hy]
  exact has_pair_f32 x y

/-- The shapes of the registers the first tile's exponentials read first. -/
def tysX0 : List (Nat × OTy) :=
  [(3901, .sbits), (1682, .f32), (1237, .f32), (1239, .f32), (4109, .pr .sbits .sbits),
   (1243, .f32), (1245, .f32), (1249, .f32), (1251, .f32), (1255, .f32), (1257, .f32),
   (1261, .f32), (1263, .f32), (1267, .f32), (1269, .f32), (1273, .f32), (1275, .f32),
   (1279, .f32), (1281, .f32), (1285, .f32), (1287, .f32), (1291, .f32), (1293, .f32),
   (1297, .f32), (1299, .f32), (1303, .f32), (1305, .f32), (1309, .f32), (1311, .f32),
   (1315, .f32), (1317, .f32), (1321, .f32), (1323, .f32), (1327, .f32), (1328, .f32),
   (1333, .f32), (1335, .f32), (1339, .f32), (1341, .f32), (1345, .f32), (1347, .f32),
   (1351, .f32), (1353, .f32), (1357, .f32), (1359, .f32), (1363, .f32), (1365, .f32),
   (1369, .f32), (1371, .f32), (1375, .f32), (1377, .f32), (1381, .f32), (1383, .f32),
   (1387, .f32), (1389, .f32), (1393, .f32), (1395, .f32), (1399, .f32), (1401, .f32),
   (1405, .f32), (1407, .f32), (1411, .f32), (1413, .f32), (1417, .f32), (1419, .f32),
   (1423, .f32), (1424, .f32), (1429, .f32), (1431, .f32), (1435, .f32), (1437, .f32),
   (1441, .f32), (1443, .f32), (1447, .f32), (1449, .f32), (1453, .f32), (1455, .f32),
   (1459, .f32), (1461, .f32), (1465, .f32), (1467, .f32), (1471, .f32), (1473, .f32),
   (1477, .f32), (1479, .f32), (1483, .f32), (1485, .f32), (1489, .f32), (1491, .f32),
   (1495, .f32), (1497, .f32), (1501, .f32), (1503, .f32), (1507, .f32), (1509, .f32),
   (1513, .f32), (1515, .f32), (1519, .f32), (1520, .f32), (1525, .f32), (1527, .f32),
   (1531, .f32), (1533, .f32), (1537, .f32), (1539, .f32), (1543, .f32), (1545, .f32),
   (1549, .f32), (1551, .f32), (1555, .f32), (1557, .f32), (1561, .f32), (1563, .f32),
   (1567, .f32), (1569, .f32), (1573, .f32), (1575, .f32), (1579, .f32), (1581, .f32),
   (1585, .f32), (1587, .f32), (1591, .f32), (1593, .f32), (1597, .f32), (1599, .f32),
   (1603, .f32), (1605, .f32), (1609, .f32), (1611, .f32), (1615, .f32), (1616, .f32)]

/-- The shapes of the registers a loop tile's exponentials read first. -/
def tysX1 : List (Nat × OTy) :=
  [(3902, .sbits), (2391, .f32), (4488, .pr .f32 .f32), (4487, .pr .f32 .f32),
   (4486, .pr .f32 .f32), (4485, .pr .f32 .f32), (4005, .pr .f32 .f32), (4006, .pr .f32 .f32),
   (4007, .pr .f32 .f32), (4008, .pr .f32 .f32), (4009, .pr .f32 .f32), (4010, .pr .f32 .f32),
   (4011, .pr .f32 .f32), (4012, .pr .f32 .f32), (4013, .pr .f32 .f32), (4014, .pr .f32 .f32),
   (4015, .pr .f32 .f32), (4016, .pr .f32 .f32), (4017, .pr .f32 .f32), (4018, .pr .f32 .f32),
   (4019, .pr .f32 .f32), (4020, .pr .f32 .f32), (4021, .pr .f32 .f32), (4022, .pr .f32 .f32),
   (4023, .pr .f32 .f32), (4024, .pr .f32 .f32), (4025, .pr .f32 .f32), (4026, .pr .f32 .f32),
   (4027, .pr .f32 .f32), (4028, .pr .f32 .f32), (4029, .pr .f32 .f32), (4030, .pr .f32 .f32),
   (4031, .pr .f32 .f32), (4032, .pr .f32 .f32), (4033, .pr .f32 .f32), (4034, .pr .f32 .f32),
   (4035, .pr .f32 .f32), (4036, .pr .f32 .f32), (4037, .pr .f32 .f32), (4038, .pr .f32 .f32),
   (4039, .pr .f32 .f32), (4040, .pr .f32 .f32), (4041, .pr .f32 .f32), (4042, .pr .f32 .f32),
   (4043, .pr .f32 .f32), (4044, .pr .f32 .f32), (4045, .pr .f32 .f32), (4046, .pr .f32 .f32),
   (4047, .pr .f32 .f32), (4048, .pr .f32 .f32), (4049, .pr .f32 .f32), (4050, .pr .f32 .f32),
   (4051, .pr .f32 .f32), (4052, .pr .f32 .f32), (4053, .pr .f32 .f32), (4054, .pr .f32 .f32),
   (4055, .pr .f32 .f32), (4056, .pr .f32 .f32), (4057, .pr .f32 .f32), (4058, .pr .f32 .f32),
   (4059, .pr .f32 .f32), (4060, .pr .f32 .f32), (4061, .pr .f32 .f32), (4062, .pr .f32 .f32),
   (4063, .pr .f32 .f32), (4064, .pr .f32 .f32)]

/-- The shapes of the registers the first tile's row sum reads first. -/
def tysS0 : List (Nat × OTy) :=
  [(408, .f32), (409, .f32), (410, .f32), (411, .f32), (412, .f32), (413, .f32), (414, .f32),
   (415, .f32), (416, .f32), (417, .f32), (418, .f32), (419, .f32), (420, .f32), (421, .f32),
   (422, .f32), (423, .f32), (424, .f32), (425, .f32), (426, .f32), (427, .f32), (428, .f32),
   (429, .f32), (430, .f32), (431, .f32), (432, .f32), (433, .f32), (434, .f32), (435, .f32),
   (436, .f32), (437, .f32), (438, .f32), (439, .f32), (440, .f32), (441, .f32), (442, .f32),
   (443, .f32), (444, .f32), (445, .f32), (1018, .f32), (1021, .f32), (1024, .f32), (1027, .f32),
   (446, .f32), (447, .f32), (448, .f32), (449, .f32), (450, .f32), (451, .f32), (1030, .f32),
   (1033, .f32), (1036, .f32), (1039, .f32), (452, .f32), (453, .f32), (454, .f32), (455, .f32),
   (456, .f32), (457, .f32), (1042, .f32), (1045, .f32), (1048, .f32), (1051, .f32), (458, .f32),
   (459, .f32), (460, .f32), (461, .f32), (462, .f32), (463, .f32), (464, .f32), (465, .f32),
   (1054, .f32), (1057, .f32), (1060, .f32), (1063, .f32), (466, .f32), (467, .f32), (468, .f32),
   (469, .f32), (470, .f32), (471, .f32), (1066, .f32), (1069, .f32), (1072, .f32), (1075, .f32),
   (472, .f32), (473, .f32), (474, .f32), (475, .f32), (476, .f32), (477, .f32), (1078, .f32),
   (1081, .f32), (1084, .f32), (1087, .f32), (478, .f32), (479, .f32), (480, .f32), (481, .f32),
   (482, .f32), (483, .f32), (484, .f32), (485, .f32), (486, .f32), (487, .f32), (488, .f32),
   (489, .f32), (490, .f32), (491, .f32), (492, .f32), (493, .f32), (494, .f32), (495, .f32),
   (496, .f32), (497, .f32), (498, .f32), (499, .f32), (500, .f32), (501, .f32), (502, .f32),
   (503, .f32), (504, .f32), (505, .f32), (506, .f32), (507, .f32), (508, .f32), (509, .f32),
   (510, .f32), (511, .f32)]

/-- The shapes of the registers a loop tile's row sum reads first. -/
def tysS1 : List (Nat × OTy) :=
  [(3933, .f32), (513, .num), (514, .f32), (515, .f32), (516, .f32), (517, .f32), (518, .f32),
   (519, .f32), (520, .f32), (521, .f32), (522, .f32), (523, .f32), (524, .f32), (525, .f32),
   (526, .f32), (527, .f32), (528, .f32), (529, .f32), (530, .f32), (531, .f32), (532, .f32),
   (533, .f32), (534, .f32), (535, .f32), (536, .f32), (537, .f32), (538, .f32), (539, .f32),
   (540, .f32), (541, .f32), (542, .f32), (543, .f32), (544, .f32), (545, .f32), (546, .f32),
   (547, .f32), (548, .f32), (549, .f32), (550, .f32), (551, .f32), (1981, .f32), (1984, .f32),
   (1987, .f32), (1990, .f32), (552, .f32), (553, .f32), (554, .f32), (555, .f32), (556, .f32),
   (557, .f32), (1993, .f32), (1996, .f32), (1999, .f32), (2002, .f32), (558, .f32), (559, .f32),
   (560, .f32), (561, .f32), (562, .f32), (563, .f32), (2005, .f32), (2008, .f32), (2011, .f32),
   (2014, .f32), (564, .f32), (565, .f32), (566, .f32), (567, .f32), (568, .f32), (569, .f32),
   (570, .f32), (571, .f32), (2017, .f32), (2020, .f32), (2023, .f32), (2026, .f32), (572, .f32),
   (573, .f32), (574, .f32), (575, .f32), (576, .f32), (577, .f32), (2029, .f32), (2032, .f32),
   (2035, .f32), (2038, .f32), (578, .f32), (579, .f32), (580, .f32), (581, .f32), (582, .f32),
   (583, .f32), (2041, .f32), (2044, .f32), (2047, .f32), (2050, .f32), (584, .f32), (585, .f32),
   (586, .f32), (587, .f32), (588, .f32), (589, .f32), (590, .f32), (591, .f32), (592, .f32),
   (593, .f32), (594, .f32), (595, .f32), (596, .f32), (597, .f32), (598, .f32), (599, .f32),
   (600, .f32), (601, .f32), (602, .f32), (603, .f32), (604, .f32), (605, .f32), (606, .f32),
   (607, .f32), (608, .f32), (609, .f32), (610, .f32), (611, .f32), (612, .f32), (613, .f32),
   (614, .f32), (615, .f32), (616, .f32), (617, .f32)]

/-- **The first tile's exponentials accept number words.** -/
theorem expOk0_of (hsc : ScaleOk L) {d : D} {x : ℝ} (hm : d.m = .float .f32 x)
    (hw : WordsF32 d.w) : ExpOk0 L g d := by
  rw [expOk0_iff]
  refine chainCond_of_chainTy (T := tyOfO tysX0) (all_tyOfO ?_) (by decide +kernel)
  dsimp only [tysX0]
  repeat' first
    | exact forall_mem_nil'
    | refine forall_mem_cons' (P := fun p : Nat × OTy => p.2.Has (valueOf L g d p.1)) ?_ ?_
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals first
    | exact has_scale hsc
    | exact has_scale2 hsc
    | exact has_word hw (by norm_num)
    | (rw [hm, mSel_read valFloat_float]; exact has_float x)

/-- **A loop tile's exponentials accept number words.** -/
theorem expOk1_of (hsc : ScaleOk L) {d : D} {x : ℝ} (hm : d.m = .float .f32 x)
    (hw : WordsF32 d.w) : ExpOk1 L g d := by
  rw [expOk1_iff]
  refine chainCond_of_chainTy (T := tyOfO tysX1) (all_tyOfO ?_) (by decide +kernel)
  dsimp only [tysX1]
  repeat' first
    | exact forall_mem_nil'
    | refine forall_mem_cons' (P := fun p : Nat × OTy => p.2.Has (valueOf L g d p.1)) ?_ ?_
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals first
    | exact has_scale hsc
    | exact has_words hw (by norm_num) (by norm_num)
    | (rw [mExpV_read hsc hm hw]; exact has_float _)

/-- **The first tile's row sum accepts number probabilities.** -/
theorem sumOk0_of (hsc : ScaleOk L) {d : D} {x : ℝ} (hm : d.m = .float .f32 x)
    (hw : WordsF32 d.w) : SumOk0 L g d := by
  refine oCond_of_oTyRun (T := tyOfO tysS0) (all_tyOfO ?_) (by decide +kernel)
  dsimp only [tysS0]
  repeat' first
    | exact forall_mem_nil'
    | refine forall_mem_cons' (P := fun p : Nat × OTy => p.2.Has (valueOf L g d p.1)) ?_ ?_
  all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
  all_goals (rw [p0V_read hsc hm hw (by norm_num)]; exact has_float _)

/-- **A loop tile's row sum accepts number probabilities, rescale factor and row sum.** -/
theorem sumOk1_of (hsc : ScaleOk L) {d : D} {x y : ℝ} (hm : d.m = .float .f32 x)
    (hl : d.l = .float .f32 y) (hw : WordsF32 d.w) : SumOk1 L g d := by
  refine ⟨oCond_of_oTyRun (T := tyOfO tysS1) (all_tyOfO ?_) (by decide +kernel), ?_⟩
  · dsimp only [tysS1]
    repeat' first
      | exact forall_mem_nil'
      | refine forall_mem_cons' (P := fun p : Nat × OTy => p.2.Has (valueOf L g d p.1)) ?_ ?_
    all_goals simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
    all_goals first
      | (rw [hl]; exact has_float _)
      | exact ⟨_, alphaV_read hsc hm hw⟩
      | (rw [p1V_read hsc hm hw (by norm_num)]; exact has_float _)
  · rw [mNV_read hsc hm hw]
    rfl

/-- **The first tile's test of its row maximum accepts number words.** -/
theorem max0T_ok {d : D} (hw : WordsF32 d.w) :
    oCond (valueEx (valueOf L g d) (exMax0_1860 L d ++ exMax0_1683 L d)) max0T := by
  refine oCond_of_oTyRun (T := tyOfO [(3932, .f32)]) (all_tyOfO ?_) (by decide +kernel)
  refine forall_mem_cons' ?_ forall_mem_nil'
  simp only [valueEx, exMax0_1860, List.cons_append, PTX.Flow.lookupLit, Option.getD_some]
  rw [rmax0V_read (half_read' hw)]
  exact has_float _

/-- **A loop tile's lazy rescale accepts number words and a number reference maximum.** -/
theorem max1T_ok (hsc : ScaleOk L) {d : D} {x : ℝ} (hm : d.m = .float .f32 x)
    (hw : WordsF32 d.w) :
    oCond (valueEx (valueOf L g d) (exMax1_2926 L d ++
      (packVals (valueEx (valueOf L g d) []) (ldPacks true 3) ++ []))) max1T := by
  refine oCond_of_oTyRun (T := tyOfO [(2386, .f32), (3932, .f32), (3902, .sbits)])
    (all_tyOfO ?_) (by decide +kernel)
  refine forall_mem_cons' ?_ (forall_mem_cons' ?_ (forall_mem_cons' ?_ forall_mem_nil'))
  all_goals simp only [valueEx, exMax1_2926, packVals, ldPacks, valueOf, ctrlValues,
    List.cons_append, List.nil_append, List.append_nil,
    PTX.Flow.lookupLit, Option.getD_some]
  · rw [mxV_read (m := d.m) (x := x) (by rw [hm]; exact valFloat_float) (half_read' hw)]
    exact has_float _
  · rw [hm]
    exact has_float _
  · exact has_scale hsc

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
