-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithBase

@[expose] public section

/-! # The first tile's row maximum: the checkpoint values

The registers live at each checkpoint whose values are not those of the table of the state. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The values at `1334` that are not the table's. -/
def exMax0_1334 (_L : Launch) (d : D) : List (Nat × Value) :=
  [(3989, joinValue (d.w 96) (d.w 97)), (3990, joinValue (d.w 98) (d.w 99)),
   (3991, joinValue (d.w 100) (d.w 101)), (3992, joinValue (d.w 102) (d.w 103)),
   (3993, joinValue (d.w 104) (d.w 105)), (3994, joinValue (d.w 106) (d.w 107)),
   (3995, joinValue (d.w 108) (d.w 109)), (3996, joinValue (d.w 110) (d.w 111)),
   (3997, joinValue (d.w 112) (d.w 113)), (3998, joinValue (d.w 114) (d.w 115)),
   (3999, joinValue (d.w 116) (d.w 117)), (4000, joinValue (d.w 118) (d.w 119)),
   (4001, joinValue (d.w 120) (d.w 121)), (4002, joinValue (d.w 122) (d.w 123)),
   (4003, joinValue (d.w 124) (d.w 125)), (4004, joinValue (d.w 126) (d.w 127))]

/-- The values at `1337` that are not the table's. -/
def exMax0_1337 (_L : Launch) (d : D) : List (Nat × Value) :=
  [(1232, b32 128), (3989, joinValue (d.w 96) (d.w 97)), (3990, joinValue (d.w 98) (d.w 99)),
   (3991, joinValue (d.w 100) (d.w 101)), (3992, joinValue (d.w 102) (d.w 103)),
   (3993, joinValue (d.w 104) (d.w 105)), (3994, joinValue (d.w 106) (d.w 107)),
   (3995, joinValue (d.w 108) (d.w 109)), (3996, joinValue (d.w 110) (d.w 111)),
   (3997, joinValue (d.w 112) (d.w 113)), (3998, joinValue (d.w 114) (d.w 115)),
   (3999, joinValue (d.w 116) (d.w 117)), (4000, joinValue (d.w 118) (d.w 119)),
   (4001, joinValue (d.w 120) (d.w 121)), (4002, joinValue (d.w 122) (d.w 123)),
   (4003, joinValue (d.w 124) (d.w 125)), (4004, joinValue (d.w 126) (d.w 127))]

/-- The values at `1452` that are not the table's. -/
def exMax0_1452 (_L : Launch) (d : D) : List (Nat × Value) :=
  [(1009, b32 4294967295), (1232, b32 128), (1237, half d.w 0), (1239, half d.w 1),
   (1243, half d.w 2), (1245, half d.w 3), (1249, half d.w 4), (1251, half d.w 5),
   (1255, half d.w 6), (1257, half d.w 7), (1261, half d.w 8), (1263, half d.w 9),
   (1267, half d.w 10), (1269, half d.w 11), (1273, half d.w 12), (1275, half d.w 13),
   (1279, half d.w 14), (1281, half d.w 15), (1285, half d.w 16), (1287, half d.w 17),
   (1291, half d.w 18), (1293, half d.w 19), (1297, half d.w 20), (1299, half d.w 21),
   (1303, half d.w 22), (1305, half d.w 23), (1309, half d.w 24), (1311, half d.w 25),
   (1315, half d.w 26), (1317, half d.w 27), (1321, half d.w 28), (1323, half d.w 29),
   (1327, half d.w 30), (1328, half d.w 31), (3989, joinValue (d.w 96) (d.w 97)),
   (3990, joinValue (d.w 98) (d.w 99)), (3991, joinValue (d.w 100) (d.w 101)),
   (3992, joinValue (d.w 102) (d.w 103)), (3993, joinValue (d.w 104) (d.w 105)),
   (3994, joinValue (d.w 106) (d.w 107)), (3995, joinValue (d.w 108) (d.w 109)),
   (3996, joinValue (d.w 110) (d.w 111)), (3997, joinValue (d.w 112) (d.w 113)),
   (3998, joinValue (d.w 114) (d.w 115)), (3999, joinValue (d.w 116) (d.w 117)),
   (4000, joinValue (d.w 118) (d.w 119)), (4001, joinValue (d.w 120) (d.w 121)),
   (4002, joinValue (d.w 122) (d.w 123)), (4003, joinValue (d.w 124) (d.w 125)),
   (4004, joinValue (d.w 126) (d.w 127))]

/-- The values at `1566` that are not the table's. -/
def exMax0_1566 (_L : Launch) (d : D) : List (Nat × Value) :=
  [(1009, b32 4294967295), (1232, b32 128), (1237, half d.w 0), (1239, half d.w 1),
   (1243, half d.w 2), (1245, half d.w 3), (1249, half d.w 4), (1251, half d.w 5),
   (1255, half d.w 6), (1257, half d.w 7), (1261, half d.w 8), (1263, half d.w 9),
   (1267, half d.w 10), (1269, half d.w 11), (1273, half d.w 12), (1275, half d.w 13),
   (1279, half d.w 14), (1281, half d.w 15), (1285, half d.w 16), (1287, half d.w 17),
   (1291, half d.w 18), (1293, half d.w 19), (1297, half d.w 20), (1299, half d.w 21),
   (1303, half d.w 22), (1305, half d.w 23), (1309, half d.w 24), (1311, half d.w 25),
   (1315, half d.w 26), (1317, half d.w 27), (1321, half d.w 28), (1323, half d.w 29),
   (1327, half d.w 30), (1328, half d.w 31), (1333, half d.w 32), (1335, half d.w 33),
   (1339, half d.w 34), (1341, half d.w 35), (1345, half d.w 36), (1347, half d.w 37),
   (1351, half d.w 38), (1353, half d.w 39), (1357, half d.w 40), (1359, half d.w 41),
   (1363, half d.w 42), (1365, half d.w 43), (1369, half d.w 44), (1371, half d.w 45),
   (1375, half d.w 46), (1377, half d.w 47), (1381, half d.w 48), (1383, half d.w 49),
   (1387, half d.w 50), (1389, half d.w 51), (1393, half d.w 52), (1395, half d.w 53),
   (1399, half d.w 54), (1401, half d.w 55), (1405, half d.w 56), (1407, half d.w 57),
   (1411, half d.w 58), (1413, half d.w 59), (1417, half d.w 60), (1419, half d.w 61),
   (1423, half d.w 62), (1424, half d.w 63), (3989, joinValue (d.w 96) (d.w 97)),
   (3990, joinValue (d.w 98) (d.w 99)), (3991, joinValue (d.w 100) (d.w 101)),
   (3992, joinValue (d.w 102) (d.w 103)), (3993, joinValue (d.w 104) (d.w 105)),
   (3994, joinValue (d.w 106) (d.w 107)), (3995, joinValue (d.w 108) (d.w 109)),
   (3996, joinValue (d.w 110) (d.w 111)), (3997, joinValue (d.w 112) (d.w 113)),
   (3998, joinValue (d.w 114) (d.w 115)), (3999, joinValue (d.w 116) (d.w 117)),
   (4000, joinValue (d.w 118) (d.w 119)), (4001, joinValue (d.w 120) (d.w 121)),
   (4002, joinValue (d.w 122) (d.w 123)), (4003, joinValue (d.w 124) (d.w 125)),
   (4004, joinValue (d.w 126) (d.w 127))]

/-- The values at `1680` that are not the table's. -/
def exMax0_1680 (_L : Launch) (d : D) : List (Nat × Value) :=
  [(1009, b32 4294967295), (1232, b32 128), (1237, half d.w 0), (1239, half d.w 1),
   (1243, half d.w 2), (1245, half d.w 3), (1249, half d.w 4), (1251, half d.w 5),
   (1255, half d.w 6), (1257, half d.w 7), (1261, half d.w 8), (1263, half d.w 9),
   (1267, half d.w 10), (1269, half d.w 11), (1273, half d.w 12), (1275, half d.w 13),
   (1279, half d.w 14), (1281, half d.w 15), (1285, half d.w 16), (1287, half d.w 17),
   (1291, half d.w 18), (1293, half d.w 19), (1297, half d.w 20), (1299, half d.w 21),
   (1303, half d.w 22), (1305, half d.w 23), (1309, half d.w 24), (1311, half d.w 25),
   (1315, half d.w 26), (1317, half d.w 27), (1321, half d.w 28), (1323, half d.w 29),
   (1327, half d.w 30), (1328, half d.w 31), (1333, half d.w 32), (1335, half d.w 33),
   (1339, half d.w 34), (1341, half d.w 35), (1345, half d.w 36), (1347, half d.w 37),
   (1351, half d.w 38), (1353, half d.w 39), (1357, half d.w 40), (1359, half d.w 41),
   (1363, half d.w 42), (1365, half d.w 43), (1369, half d.w 44), (1371, half d.w 45),
   (1375, half d.w 46), (1377, half d.w 47), (1381, half d.w 48), (1383, half d.w 49),
   (1387, half d.w 50), (1389, half d.w 51), (1393, half d.w 52), (1395, half d.w 53),
   (1399, half d.w 54), (1401, half d.w 55), (1405, half d.w 56), (1407, half d.w 57),
   (1411, half d.w 58), (1413, half d.w 59), (1417, half d.w 60), (1419, half d.w 61),
   (1423, half d.w 62), (1424, half d.w 63), (1429, half d.w 64), (1431, half d.w 65),
   (1435, half d.w 66), (1437, half d.w 67), (1441, half d.w 68), (1443, half d.w 69),
   (1447, half d.w 70), (1449, half d.w 71), (1453, half d.w 72), (1455, half d.w 73),
   (1459, half d.w 74), (1461, half d.w 75), (1465, half d.w 76), (1467, half d.w 77),
   (1471, half d.w 78), (1473, half d.w 79), (1477, half d.w 80), (1479, half d.w 81),
   (1483, half d.w 82), (1485, half d.w 83), (1489, half d.w 84), (1491, half d.w 85),
   (1495, half d.w 86), (1497, half d.w 87), (1501, half d.w 88), (1503, half d.w 89),
   (1507, half d.w 90), (1509, half d.w 91), (1513, half d.w 92), (1515, half d.w 93),
   (1519, half d.w 94), (1520, half d.w 95), (3989, joinValue (d.w 96) (d.w 97)),
   (3990, joinValue (d.w 98) (d.w 99)), (3991, joinValue (d.w 100) (d.w 101)),
   (3992, joinValue (d.w 102) (d.w 103)), (3993, joinValue (d.w 104) (d.w 105)),
   (3994, joinValue (d.w 106) (d.w 107)), (3995, joinValue (d.w 108) (d.w 109)),
   (3996, joinValue (d.w 110) (d.w 111)), (3997, joinValue (d.w 112) (d.w 113)),
   (3998, joinValue (d.w 114) (d.w 115)), (3999, joinValue (d.w 116) (d.w 117)),
   (4000, joinValue (d.w 118) (d.w 119)), (4001, joinValue (d.w 120) (d.w 121)),
   (4002, joinValue (d.w 122) (d.w 123)), (4003, joinValue (d.w 124) (d.w 125)),
   (4004, joinValue (d.w 126) (d.w 127))]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
