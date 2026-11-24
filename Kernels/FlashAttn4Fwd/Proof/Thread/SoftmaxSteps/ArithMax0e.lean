-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax0Facts

@[expose] public section

/-! # The first tile's row maximum: the reads from `1683` -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem segMax0_1680 {L : Launch} {g : Nat} (d : D) :
    Seg kernel asms L g 3 1680
      (factsFrom (Flow.live 1680)
      (valueEx (valueOf L g { d with site := .ldW false 3 })
        (exMax0_1680 L d ++ exMax0_1569 L d))) 1683
      (factsFrom (Flow.live 1683)
      (valueEx (valueOf L g { d with site := .ldW false 3 })
        (exMax0_1683 L d))) := by
  intro t h
  ar_seg h

theorem segMax0_1683 {L : Launch} {g : Nat} (d : D) :
    SegD kernel asms L g 177 1683
      (factsFrom (Flow.live 1683)
      (valueEx (valueOf L g { d with site := .ldW false 3 })
        (exMax0_1683 L d))) 1860
      (factsFrom (Flow.live 1860)
      (valueEx (valueOf L g { d with site := .ldW false 3 })
        (exMax0_1860 L d ++ (exMax0_1683 L d))))
      (rCond (valueEx (valueOf L g { d with site := .ldW false 3 }) (exMax0_1683 L d))
        readsMax0_1683) := by
  refine SegD.reads (pc := 1683) (keys :=
      [1237, 1239, 1243, 1245, 1249, 1251, 1255, 1257, 1261, 1263, 1267, 1269, 1273, 1275, 1279,
       1281, 1285, 1287, 1291, 1293, 1297, 1299, 1303, 1305, 1309, 1311, 1315, 1317, 1321, 1323,
       1327, 1328, 1333, 1335, 1339, 1341, 1345, 1347, 1351, 1353, 1357, 1359, 1363, 1365, 1369,
       1371, 1375, 1377, 1381, 1383, 1387, 1389, 1393, 1395, 1399, 1401, 1405, 1407, 1411, 1413,
       1417, 1419, 1423, 1424, 1429, 1431, 1435, 1437, 1441, 1443, 1447, 1449, 1453, 1455, 1459,
       1461, 1465, 1467, 1471, 1473, 1477, 1479, 1483, 1485, 1489, 1491, 1495, 1497, 1501, 1503,
       1507, 1509, 1513, 1515, 1519, 1520, 1525, 1527, 1531, 1533, 1537, 1539, 1543, 1545, 1549,
       1551, 1555, 1557, 1561, 1563, 1567, 1569, 1573, 1575, 1579, 1581, 1585, 1587, 1591, 1593,
       1597, 1599, 1603, 1605, 1609, 1611, 1615, 1616, 3932])
    (by decide +kernel) (by decide +kernel) (by kernel_rfl)
    (by decide +kernel) (noItemRule_asms _) (segFree_asms (by decide +kernel))
    (ideal_max_range (by decide +kernel)) (decline_max_range (by decide +kernel)) (by kernel_rfl)
    rfl (by decide +kernel) (by decide +kernel)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
