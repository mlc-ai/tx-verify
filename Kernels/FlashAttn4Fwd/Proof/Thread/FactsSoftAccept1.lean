-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftAcceptBase

@[expose] public section

/-! # The first tile's row maximum accepts single-precision words (run 4)

The last read run of the first tile's row maximum, as `FactsSoftAccept0`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The shapes of the registers `readsMax0_1683` reads first. -/
def tys_1683 : List (Nat × RTy) :=
  [(1015, .bits (BitVec.ofNat 64 4294967295)), (3989, .f32x2), (3990, .f32x2), (3991, .f32x2),
   (3992, .f32x2), (3993, .f32x2), (3994, .f32x2), (3995, .f32x2), (3996, .f32x2),
   (3997, .f32x2), (3998, .f32x2), (3999, .f32x2), (4000, .f32x2), (4001, .f32x2),
   (4002, .f32x2), (4003, .f32x2), (4004, .f32x2), (1237, .f32), (1239, .f32), (1243, .f32),
   (1245, .f32), (1249, .f32), (1251, .f32), (1255, .f32), (1257, .f32), (1261, .f32),
   (1263, .f32), (1267, .f32), (1269, .f32), (1273, .f32), (1275, .f32), (1279, .f32),
   (1281, .f32), (1285, .f32), (1287, .f32), (1291, .f32), (1293, .f32), (1297, .f32),
   (1299, .f32), (1303, .f32), (1305, .f32), (1309, .f32), (1311, .f32), (1315, .f32),
   (1317, .f32), (1321, .f32), (1323, .f32), (1327, .f32), (1328, .f32), (1333, .f32),
   (1335, .f32), (1339, .f32), (1341, .f32), (1345, .f32), (1347, .f32), (1351, .f32),
   (1353, .f32), (1357, .f32), (1359, .f32), (1363, .f32), (1365, .f32), (1369, .f32),
   (1371, .f32), (1375, .f32), (1377, .f32), (1381, .f32), (1383, .f32), (1387, .f32),
   (1389, .f32), (1393, .f32), (1395, .f32), (1399, .f32), (1401, .f32), (1405, .f32),
   (1407, .f32), (1411, .f32), (1413, .f32), (1417, .f32), (1419, .f32), (1423, .f32),
   (1424, .f32), (1429, .f32), (1431, .f32), (1435, .f32), (1437, .f32), (1441, .f32),
   (1443, .f32), (1447, .f32), (1449, .f32), (1453, .f32), (1455, .f32), (1459, .f32),
   (1461, .f32), (1465, .f32), (1467, .f32), (1471, .f32), (1473, .f32), (1477, .f32),
   (1479, .f32), (1483, .f32), (1485, .f32), (1489, .f32), (1491, .f32), (1495, .f32),
   (1497, .f32), (1501, .f32), (1503, .f32), (1507, .f32), (1509, .f32), (1513, .f32),
   (1515, .f32), (1519, .f32), (1520, .f32)]

theorem accept_1683 {L : Launch} {g : Nat} {d : D}
    (hf : ∀ k < 128, RTy.Has .f32 (d.w k)) :
    rCond (valueEx (valueOf L g d) (exMax0_1683 L d)) readsMax0_1683 := by
  refine rCond_of_rTy (T := tyOf tys_1683) (all_tyOf fun p hp => ?_) (by decide +kernel)
  simp only [tys_1683, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [valueEx, valueOf, ctrlValues, PTX.Flow.lookupLit,
    Option.getD_some, exMax0_1683]
  all_goals first
    | exact has_join (hf _ (by norm_num)) (hf _ (by norm_num))
    | exact half_has hf (by norm_num)
    | rfl

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
