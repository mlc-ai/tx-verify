-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Sites.Decl
public import Kernels.TmlFa4Fwd.Proof.Loader.Machine

@[expose] public section

/-! # The loader warps' event instructions -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

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

end
end PTX.Kernels.TmlFa4Fwd.Proof
