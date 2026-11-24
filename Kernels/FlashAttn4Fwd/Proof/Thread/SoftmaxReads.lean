-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxRuns
public import Lemmas.Flow.ReadRun

@[expose] public section

/-! # The runs that read the loaded words

A load may return any values (`Softmax.D.w`). The local runs that read them decide whether the
thread continues; the machine continues exactly when they accept the words:

* after the implicit wait of load `c < 3`, the sixteen packs of its words (`ldPacks`) need four
  bytes per word (`packsOk`);
* after the last load's wait, its packs and the row maximum: the first tile's unpacks, column
  selections and `max.f32` tree (`readsMax0_*`, from the checkpoints `exMax0_*`) and the test of
  the maximum against `-∞` (`max0T`), a loop tile's unpacks and `max.f32` chain
  (`readsMax1_2796`) and lazy rescale (`max1T`), each accepting its operands (`rCond`, `oCond`):
  `Max0Ok`, `Max1Ok`;
* after the named barrier of a tile, the exponentials (`exp0Pieces`, `exp1Pieces`): no
  instruction faults and the software `exp2`'s inputs read as numbers: `ExpOk0`, `ExpOk1`;
* after a statistics poll ending a tile, the row sum (`sum0Items`, `sum1Items`) and, in a loop
  trip, the move of the new reference maximum: `SumOk0`, `SumOk1` (`StatsOk`).

The read runs' tables are written by hand from the PTX, the outcome runs generated from it
(`SoftmaxRuns`); the theorems below are proved about the decoded program. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The packs after load `c` of the first tile (`lp = false`) or a loop tile: `(d, a, b)` for
`mov.b64 d, {a, b}`. -/
def ldPacks : Bool → Nat → List (Nat × Nat × Nat)
  | false, 0 =>
    [(3956, 1132, 1133), (3955, 1130, 1131), (3954, 1128, 1129), (3953, 1126, 1127),
     (3952, 1124, 1125), (3951, 1122, 1123), (3950, 1120, 1121), (3949, 1118, 1119),
     (3948, 1116, 1117), (3947, 1114, 1115), (3946, 1112, 1113), (3945, 1110, 1111),
     (4103, 1108, 1109), (4104, 1106, 1107), (4105, 1104, 1105), (4106, 1102, 1103)]
  | false, 1 =>
    [(3972, 1164, 1165), (3971, 1162, 1163), (3970, 1160, 1161), (3969, 1158, 1159),
     (3968, 1156, 1157), (3967, 1154, 1155), (3966, 1152, 1153), (3965, 1150, 1151),
     (3964, 1148, 1149), (3963, 1146, 1147), (3962, 1144, 1145), (3961, 1142, 1143),
     (3960, 1140, 1141), (3959, 1138, 1139), (3958, 1136, 1137), (3957, 1134, 1135)]
  | false, 2 =>
    [(3988, 1196, 1197), (3987, 1194, 1195), (3986, 1192, 1193), (3985, 1190, 1191),
     (3984, 1188, 1189), (3983, 1186, 1187), (3982, 1184, 1185), (3981, 1182, 1183),
     (3980, 1180, 1181), (3979, 1178, 1179), (3978, 1176, 1177), (3977, 1174, 1175),
     (3976, 1172, 1173), (3975, 1170, 1171), (3974, 1168, 1169), (3973, 1166, 1167)]
  | false, 3 =>
    [(4004, 1228, 1229), (4003, 1226, 1227), (4002, 1224, 1225), (4001, 1222, 1223),
     (4000, 1220, 1221), (3999, 1218, 1219), (3998, 1216, 1217), (3997, 1214, 1215),
     (3996, 1212, 1213), (3995, 1210, 1211), (3994, 1208, 1209), (3993, 1206, 1207),
     (3992, 1204, 1205), (3991, 1202, 1203), (3990, 1200, 1201), (3989, 1198, 1199)]
  | true, 0 =>
    [(4016, 2095, 2096), (4015, 2093, 2094), (4014, 2091, 2092), (4013, 2089, 2090),
     (4012, 2087, 2088), (4011, 2085, 2086), (4010, 2083, 2084), (4009, 2081, 2082),
     (4008, 2079, 2080), (4007, 2077, 2078), (4006, 2075, 2076), (4005, 2073, 2074),
     (4485, 2071, 2072), (4486, 2069, 2070), (4487, 2067, 2068), (4488, 2065, 2066)]
  | true, 1 =>
    [(4032, 2127, 2128), (4031, 2125, 2126), (4030, 2123, 2124), (4029, 2121, 2122),
     (4028, 2119, 2120), (4027, 2117, 2118), (4026, 2115, 2116), (4025, 2113, 2114),
     (4024, 2111, 2112), (4023, 2109, 2110), (4022, 2107, 2108), (4021, 2105, 2106),
     (4020, 2103, 2104), (4019, 2101, 2102), (4018, 2099, 2100), (4017, 2097, 2098)]
  | true, 2 =>
    [(4048, 2159, 2160), (4047, 2157, 2158), (4046, 2155, 2156), (4045, 2153, 2154),
     (4044, 2151, 2152), (4043, 2149, 2150), (4042, 2147, 2148), (4041, 2145, 2146),
     (4040, 2143, 2144), (4039, 2141, 2142), (4038, 2139, 2140), (4037, 2137, 2138),
     (4036, 2135, 2136), (4035, 2133, 2134), (4034, 2131, 2132), (4033, 2129, 2130)]
  | true, 3 =>
    [(4064, 2191, 2192), (4063, 2189, 2190), (4062, 2187, 2188), (4061, 2185, 2186),
     (4060, 2183, 2184), (4059, 2181, 2182), (4058, 2179, 2180), (4057, 2177, 2178),
     (4056, 2175, 2176), (4055, 2173, 2174), (4054, 2171, 2172), (4053, 2169, 2170),
     (4052, 2167, 2168), (4051, 2165, 2166), (4050, 2163, 2164), (4049, 2161, 2162)]
  | _, _ => []

/-- The first tile's read run from `1341` to `1452`. -/
def readsMax0_1341 : List RItem :=
  [.andImm 1234 1008 1, .setpImm .ne .b 147 1234 0, .unpack 1235 1236 4106,
   .selp 1237 (.reg 1235) (.f32imm 4286578688) 147, .andImm 1238 1008 2, .setpImm .eq .b 148 1238 0,
   .selp 1239 (.f32imm 4286578688) (.reg 1236) 148, .andImm 1240 1008 4, .setpImm .eq .b 149 1240 0,
   .unpack 1241 1242 4105, .selp 1243 (.f32imm 4286578688) (.reg 1241) 149, .andImm 1244 1008 8,
   .setpImm .eq .b 150 1244 0, .selp 1245 (.f32imm 4286578688) (.reg 1242) 150,
   .andImm 1246 1008 16, .setpImm .eq .b 151 1246 0, .unpack 1247 1248 4104,
   .selp 1249 (.f32imm 4286578688) (.reg 1247) 151, .andImm 1250 1008 32,
   .setpImm .eq .b 152 1250 0, .selp 1251 (.f32imm 4286578688) (.reg 1248) 152,
   .andImm 1252 1008 64, .setpImm .eq .b 153 1252 0, .unpack 1253 1254 4103,
   .selp 1255 (.f32imm 4286578688) (.reg 1253) 153, .andImm 1256 1008 128,
   .setpImm .eq .b 154 1256 0, .selp 1257 (.f32imm 4286578688) (.reg 1254) 154,
   .andImm 1258 1008 256, .setpImm .eq .b 155 1258 0, .unpack 1259 1260 3945,
   .selp 1261 (.f32imm 4286578688) (.reg 1259) 155, .andImm 1262 1008 512,
   .setpImm .eq .b 156 1262 0, .selp 1263 (.f32imm 4286578688) (.reg 1260) 156,
   .andImm 1264 1008 1024, .setpImm .eq .b 157 1264 0, .unpack 1265 1266 3946,
   .selp 1267 (.f32imm 4286578688) (.reg 1265) 157, .andImm 1268 1008 2048,
   .setpImm .eq .b 158 1268 0, .selp 1269 (.f32imm 4286578688) (.reg 1266) 158,
   .andImm 1270 1008 4096, .setpImm .eq .b 159 1270 0, .unpack 1271 1272 3947,
   .selp 1273 (.f32imm 4286578688) (.reg 1271) 159, .andImm 1274 1008 8192,
   .setpImm .eq .b 160 1274 0, .selp 1275 (.f32imm 4286578688) (.reg 1272) 160,
   .andImm 1276 1008 16384, .setpImm .eq .b 161 1276 0, .unpack 1277 1278 3948,
   .selp 1279 (.f32imm 4286578688) (.reg 1277) 161, .andImm 1280 1008 32768,
   .setpImm .eq .b 162 1280 0, .selp 1281 (.f32imm 4286578688) (.reg 1278) 162,
   .andImm 1282 1008 65536, .setpImm .eq .b 163 1282 0, .unpack 1283 1284 3949,
   .selp 1285 (.f32imm 4286578688) (.reg 1283) 163, .andImm 1286 1008 131072,
   .setpImm .eq .b 164 1286 0, .selp 1287 (.f32imm 4286578688) (.reg 1284) 164,
   .andImm 1288 1008 262144, .setpImm .eq .b 165 1288 0, .unpack 1289 1290 3950,
   .selp 1291 (.f32imm 4286578688) (.reg 1289) 165, .andImm 1292 1008 524288,
   .setpImm .eq .b 166 1292 0, .selp 1293 (.f32imm 4286578688) (.reg 1290) 166,
   .andImm 1294 1008 1048576, .setpImm .eq .b 167 1294 0, .unpack 1295 1296 3951,
   .selp 1297 (.f32imm 4286578688) (.reg 1295) 167, .andImm 1298 1008 2097152,
   .setpImm .eq .b 168 1298 0, .selp 1299 (.f32imm 4286578688) (.reg 1296) 168,
   .andImm 1300 1008 4194304, .setpImm .eq .b 169 1300 0, .unpack 1301 1302 3952,
   .selp 1303 (.f32imm 4286578688) (.reg 1301) 169, .andImm 1304 1008 8388608,
   .setpImm .eq .b 170 1304 0, .selp 1305 (.f32imm 4286578688) (.reg 1302) 170,
   .andImm 1306 1008 16777216, .setpImm .eq .b 171 1306 0, .unpack 1307 1308 3953,
   .selp 1309 (.f32imm 4286578688) (.reg 1307) 171, .andImm 1310 1008 33554432,
   .setpImm .eq .b 172 1310 0, .selp 1311 (.f32imm 4286578688) (.reg 1308) 172,
   .andImm 1312 1008 67108864, .setpImm .eq .b 173 1312 0, .unpack 1313 1314 3954,
   .selp 1315 (.f32imm 4286578688) (.reg 1313) 173, .andImm 1316 1008 134217728,
   .setpImm .eq .b 174 1316 0, .selp 1317 (.f32imm 4286578688) (.reg 1314) 174,
   .andImm 1318 1008 268435456, .setpImm .eq .b 175 1318 0, .unpack 1319 1320 3955,
   .selp 1321 (.f32imm 4286578688) (.reg 1319) 175, .andImm 1322 1008 536870912,
   .setpImm .eq .b 176 1322 0, .selp 1323 (.f32imm 4286578688) (.reg 1320) 176,
   .andImm 1324 1008 1073741824, .setpImm .eq .b 177 1324 0, .unpack 1325 1326 3956,
   .selp 1327 (.f32imm 4286578688) (.reg 1325) 177, .setpImm .gt .s 178 1008 (-1),
   .selp 1328 (.f32imm 4286578688) (.reg 1326) 178]

/-- The first tile's read run from `1455` to `1566`. -/
def readsMax0_1455 : List RItem :=
  [.andImm 1330 1011 1, .setpImm .ne .b 179 1330 0, .unpack 1331 1332 3957,
   .selp 1333 (.reg 1331) (.f32imm 4286578688) 179, .andImm 1334 1011 2, .setpImm .eq .b 180 1334 0,
   .selp 1335 (.f32imm 4286578688) (.reg 1332) 180, .andImm 1336 1011 4, .setpImm .eq .b 181 1336 0,
   .unpack 1337 1338 3958, .selp 1339 (.f32imm 4286578688) (.reg 1337) 181, .andImm 1340 1011 8,
   .setpImm .eq .b 182 1340 0, .selp 1341 (.f32imm 4286578688) (.reg 1338) 182,
   .andImm 1342 1011 16, .setpImm .eq .b 183 1342 0, .unpack 1343 1344 3959,
   .selp 1345 (.f32imm 4286578688) (.reg 1343) 183, .andImm 1346 1011 32,
   .setpImm .eq .b 184 1346 0, .selp 1347 (.f32imm 4286578688) (.reg 1344) 184,
   .andImm 1348 1011 64, .setpImm .eq .b 185 1348 0, .unpack 1349 1350 3960,
   .selp 1351 (.f32imm 4286578688) (.reg 1349) 185, .andImm 1352 1011 128,
   .setpImm .eq .b 186 1352 0, .selp 1353 (.f32imm 4286578688) (.reg 1350) 186,
   .andImm 1354 1011 256, .setpImm .eq .b 187 1354 0, .unpack 1355 1356 3961,
   .selp 1357 (.f32imm 4286578688) (.reg 1355) 187, .andImm 1358 1011 512,
   .setpImm .eq .b 188 1358 0, .selp 1359 (.f32imm 4286578688) (.reg 1356) 188,
   .andImm 1360 1011 1024, .setpImm .eq .b 189 1360 0, .unpack 1361 1362 3962,
   .selp 1363 (.f32imm 4286578688) (.reg 1361) 189, .andImm 1364 1011 2048,
   .setpImm .eq .b 190 1364 0, .selp 1365 (.f32imm 4286578688) (.reg 1362) 190,
   .andImm 1366 1011 4096, .setpImm .eq .b 191 1366 0, .unpack 1367 1368 3963,
   .selp 1369 (.f32imm 4286578688) (.reg 1367) 191, .andImm 1370 1011 8192,
   .setpImm .eq .b 192 1370 0, .selp 1371 (.f32imm 4286578688) (.reg 1368) 192,
   .andImm 1372 1011 16384, .setpImm .eq .b 193 1372 0, .unpack 1373 1374 3964,
   .selp 1375 (.f32imm 4286578688) (.reg 1373) 193, .andImm 1376 1011 32768,
   .setpImm .eq .b 194 1376 0, .selp 1377 (.f32imm 4286578688) (.reg 1374) 194,
   .andImm 1378 1011 65536, .setpImm .eq .b 195 1378 0, .unpack 1379 1380 3965,
   .selp 1381 (.f32imm 4286578688) (.reg 1379) 195, .andImm 1382 1011 131072,
   .setpImm .eq .b 196 1382 0, .selp 1383 (.f32imm 4286578688) (.reg 1380) 196,
   .andImm 1384 1011 262144, .setpImm .eq .b 197 1384 0, .unpack 1385 1386 3966,
   .selp 1387 (.f32imm 4286578688) (.reg 1385) 197, .andImm 1388 1011 524288,
   .setpImm .eq .b 198 1388 0, .selp 1389 (.f32imm 4286578688) (.reg 1386) 198,
   .andImm 1390 1011 1048576, .setpImm .eq .b 199 1390 0, .unpack 1391 1392 3967,
   .selp 1393 (.f32imm 4286578688) (.reg 1391) 199, .andImm 1394 1011 2097152,
   .setpImm .eq .b 200 1394 0, .selp 1395 (.f32imm 4286578688) (.reg 1392) 200,
   .andImm 1396 1011 4194304, .setpImm .eq .b 201 1396 0, .unpack 1397 1398 3968,
   .selp 1399 (.f32imm 4286578688) (.reg 1397) 201, .andImm 1400 1011 8388608,
   .setpImm .eq .b 202 1400 0, .selp 1401 (.f32imm 4286578688) (.reg 1398) 202,
   .andImm 1402 1011 16777216, .setpImm .eq .b 203 1402 0, .unpack 1403 1404 3969,
   .selp 1405 (.f32imm 4286578688) (.reg 1403) 203, .andImm 1406 1011 33554432,
   .setpImm .eq .b 204 1406 0, .selp 1407 (.f32imm 4286578688) (.reg 1404) 204,
   .andImm 1408 1011 67108864, .setpImm .eq .b 205 1408 0, .unpack 1409 1410 3970,
   .selp 1411 (.f32imm 4286578688) (.reg 1409) 205, .andImm 1412 1011 134217728,
   .setpImm .eq .b 206 1412 0, .selp 1413 (.f32imm 4286578688) (.reg 1410) 206,
   .andImm 1414 1011 268435456, .setpImm .eq .b 207 1414 0, .unpack 1415 1416 3971,
   .selp 1417 (.f32imm 4286578688) (.reg 1415) 207, .andImm 1418 1011 536870912,
   .setpImm .eq .b 208 1418 0, .selp 1419 (.f32imm 4286578688) (.reg 1416) 208,
   .andImm 1420 1011 1073741824, .setpImm .eq .b 209 1420 0, .unpack 1421 1422 3972,
   .selp 1423 (.f32imm 4286578688) (.reg 1421) 209, .setpImm .gt .s 210 1011 (-1),
   .selp 1424 (.f32imm 4286578688) (.reg 1422) 210]

/-- The first tile's read run from `1569` to `1680`. -/
def readsMax0_1569 : List RItem :=
  [.andImm 1426 1013 1, .setpImm .ne .b 211 1426 0, .unpack 1427 1428 3973,
   .selp 1429 (.reg 1427) (.f32imm 4286578688) 211, .andImm 1430 1013 2, .setpImm .eq .b 212 1430 0,
   .selp 1431 (.f32imm 4286578688) (.reg 1428) 212, .andImm 1432 1013 4, .setpImm .eq .b 213 1432 0,
   .unpack 1433 1434 3974, .selp 1435 (.f32imm 4286578688) (.reg 1433) 213, .andImm 1436 1013 8,
   .setpImm .eq .b 214 1436 0, .selp 1437 (.f32imm 4286578688) (.reg 1434) 214,
   .andImm 1438 1013 16, .setpImm .eq .b 215 1438 0, .unpack 1439 1440 3975,
   .selp 1441 (.f32imm 4286578688) (.reg 1439) 215, .andImm 1442 1013 32,
   .setpImm .eq .b 216 1442 0, .selp 1443 (.f32imm 4286578688) (.reg 1440) 216,
   .andImm 1444 1013 64, .setpImm .eq .b 217 1444 0, .unpack 1445 1446 3976,
   .selp 1447 (.f32imm 4286578688) (.reg 1445) 217, .andImm 1448 1013 128,
   .setpImm .eq .b 218 1448 0, .selp 1449 (.f32imm 4286578688) (.reg 1446) 218,
   .andImm 1450 1013 256, .setpImm .eq .b 219 1450 0, .unpack 1451 1452 3977,
   .selp 1453 (.f32imm 4286578688) (.reg 1451) 219, .andImm 1454 1013 512,
   .setpImm .eq .b 220 1454 0, .selp 1455 (.f32imm 4286578688) (.reg 1452) 220,
   .andImm 1456 1013 1024, .setpImm .eq .b 221 1456 0, .unpack 1457 1458 3978,
   .selp 1459 (.f32imm 4286578688) (.reg 1457) 221, .andImm 1460 1013 2048,
   .setpImm .eq .b 222 1460 0, .selp 1461 (.f32imm 4286578688) (.reg 1458) 222,
   .andImm 1462 1013 4096, .setpImm .eq .b 223 1462 0, .unpack 1463 1464 3979,
   .selp 1465 (.f32imm 4286578688) (.reg 1463) 223, .andImm 1466 1013 8192,
   .setpImm .eq .b 224 1466 0, .selp 1467 (.f32imm 4286578688) (.reg 1464) 224,
   .andImm 1468 1013 16384, .setpImm .eq .b 225 1468 0, .unpack 1469 1470 3980,
   .selp 1471 (.f32imm 4286578688) (.reg 1469) 225, .andImm 1472 1013 32768,
   .setpImm .eq .b 226 1472 0, .selp 1473 (.f32imm 4286578688) (.reg 1470) 226,
   .andImm 1474 1013 65536, .setpImm .eq .b 227 1474 0, .unpack 1475 1476 3981,
   .selp 1477 (.f32imm 4286578688) (.reg 1475) 227, .andImm 1478 1013 131072,
   .setpImm .eq .b 228 1478 0, .selp 1479 (.f32imm 4286578688) (.reg 1476) 228,
   .andImm 1480 1013 262144, .setpImm .eq .b 229 1480 0, .unpack 1481 1482 3982,
   .selp 1483 (.f32imm 4286578688) (.reg 1481) 229, .andImm 1484 1013 524288,
   .setpImm .eq .b 230 1484 0, .selp 1485 (.f32imm 4286578688) (.reg 1482) 230,
   .andImm 1486 1013 1048576, .setpImm .eq .b 231 1486 0, .unpack 1487 1488 3983,
   .selp 1489 (.f32imm 4286578688) (.reg 1487) 231, .andImm 1490 1013 2097152,
   .setpImm .eq .b 232 1490 0, .selp 1491 (.f32imm 4286578688) (.reg 1488) 232,
   .andImm 1492 1013 4194304, .setpImm .eq .b 233 1492 0, .unpack 1493 1494 3984,
   .selp 1495 (.f32imm 4286578688) (.reg 1493) 233, .andImm 1496 1013 8388608,
   .setpImm .eq .b 234 1496 0, .selp 1497 (.f32imm 4286578688) (.reg 1494) 234,
   .andImm 1498 1013 16777216, .setpImm .eq .b 235 1498 0, .unpack 1499 1500 3985,
   .selp 1501 (.f32imm 4286578688) (.reg 1499) 235, .andImm 1502 1013 33554432,
   .setpImm .eq .b 236 1502 0, .selp 1503 (.f32imm 4286578688) (.reg 1500) 236,
   .andImm 1504 1013 67108864, .setpImm .eq .b 237 1504 0, .unpack 1505 1506 3986,
   .selp 1507 (.f32imm 4286578688) (.reg 1505) 237, .andImm 1508 1013 134217728,
   .setpImm .eq .b 238 1508 0, .selp 1509 (.f32imm 4286578688) (.reg 1506) 238,
   .andImm 1510 1013 268435456, .setpImm .eq .b 239 1510 0, .unpack 1511 1512 3987,
   .selp 1513 (.f32imm 4286578688) (.reg 1511) 239, .andImm 1514 1013 536870912,
   .setpImm .eq .b 240 1514 0, .selp 1515 (.f32imm 4286578688) (.reg 1512) 240,
   .andImm 1516 1013 1073741824, .setpImm .eq .b 241 1516 0, .unpack 1517 1518 3988,
   .selp 1519 (.f32imm 4286578688) (.reg 1517) 241, .setpImm .gt .s 242 1013 (-1),
   .selp 1520 (.f32imm 4286578688) (.reg 1518) 242]

/-- The first tile's read run from `1683` to `1860`. -/
def readsMax0_1683 : List RItem :=
  [.andImm 1522 1015 1, .setpImm .ne .b 243 1522 0, .unpack 1523 1524 3989,
   .selp 1525 (.reg 1523) (.f32imm 4286578688) 243, .andImm 1526 1015 2, .setpImm .eq .b 244 1526 0,
   .selp 1527 (.f32imm 4286578688) (.reg 1524) 244, .andImm 1528 1015 4, .setpImm .eq .b 245 1528 0,
   .unpack 1529 1530 3990, .selp 1531 (.f32imm 4286578688) (.reg 1529) 245, .andImm 1532 1015 8,
   .setpImm .eq .b 246 1532 0, .selp 1533 (.f32imm 4286578688) (.reg 1530) 246,
   .andImm 1534 1015 16, .setpImm .eq .b 247 1534 0, .unpack 1535 1536 3991,
   .selp 1537 (.f32imm 4286578688) (.reg 1535) 247, .andImm 1538 1015 32,
   .setpImm .eq .b 248 1538 0, .selp 1539 (.f32imm 4286578688) (.reg 1536) 248,
   .andImm 1540 1015 64, .setpImm .eq .b 249 1540 0, .unpack 1541 1542 3992,
   .selp 1543 (.f32imm 4286578688) (.reg 1541) 249, .andImm 1544 1015 128,
   .setpImm .eq .b 250 1544 0, .selp 1545 (.f32imm 4286578688) (.reg 1542) 250,
   .andImm 1546 1015 256, .setpImm .eq .b 251 1546 0, .unpack 1547 1548 3993,
   .selp 1549 (.f32imm 4286578688) (.reg 1547) 251, .andImm 1550 1015 512,
   .setpImm .eq .b 252 1550 0, .selp 1551 (.f32imm 4286578688) (.reg 1548) 252,
   .andImm 1552 1015 1024, .setpImm .eq .b 253 1552 0, .unpack 1553 1554 3994,
   .selp 1555 (.f32imm 4286578688) (.reg 1553) 253, .andImm 1556 1015 2048,
   .setpImm .eq .b 254 1556 0, .selp 1557 (.f32imm 4286578688) (.reg 1554) 254,
   .andImm 1558 1015 4096, .setpImm .eq .b 255 1558 0, .unpack 1559 1560 3995,
   .selp 1561 (.f32imm 4286578688) (.reg 1559) 255, .andImm 1562 1015 8192,
   .setpImm .eq .b 256 1562 0, .selp 1563 (.f32imm 4286578688) (.reg 1560) 256,
   .andImm 1564 1015 16384, .setpImm .eq .b 257 1564 0, .unpack 1565 1566 3996,
   .selp 1567 (.f32imm 4286578688) (.reg 1565) 257, .andImm 1568 1015 32768,
   .setpImm .eq .b 258 1568 0, .selp 1569 (.f32imm 4286578688) (.reg 1566) 258,
   .andImm 1570 1015 65536, .setpImm .eq .b 259 1570 0, .unpack 1571 1572 3997,
   .selp 1573 (.f32imm 4286578688) (.reg 1571) 259, .andImm 1574 1015 131072,
   .setpImm .eq .b 260 1574 0, .selp 1575 (.f32imm 4286578688) (.reg 1572) 260,
   .andImm 1576 1015 262144, .setpImm .eq .b 261 1576 0, .unpack 1577 1578 3998,
   .selp 1579 (.f32imm 4286578688) (.reg 1577) 261, .andImm 1580 1015 524288,
   .setpImm .eq .b 262 1580 0, .selp 1581 (.f32imm 4286578688) (.reg 1578) 262,
   .andImm 1582 1015 1048576, .setpImm .eq .b 263 1582 0, .unpack 1583 1584 3999,
   .selp 1585 (.f32imm 4286578688) (.reg 1583) 263, .andImm 1586 1015 2097152,
   .setpImm .eq .b 264 1586 0, .selp 1587 (.f32imm 4286578688) (.reg 1584) 264,
   .andImm 1588 1015 4194304, .setpImm .eq .b 265 1588 0, .unpack 1589 1590 4000,
   .selp 1591 (.f32imm 4286578688) (.reg 1589) 265, .andImm 1592 1015 8388608,
   .setpImm .eq .b 266 1592 0, .selp 1593 (.f32imm 4286578688) (.reg 1590) 266,
   .andImm 1594 1015 16777216, .setpImm .eq .b 267 1594 0, .unpack 1595 1596 4001,
   .selp 1597 (.f32imm 4286578688) (.reg 1595) 267, .andImm 1598 1015 33554432,
   .setpImm .eq .b 268 1598 0, .selp 1599 (.f32imm 4286578688) (.reg 1596) 268,
   .andImm 1600 1015 67108864, .setpImm .eq .b 269 1600 0, .unpack 1601 1602 4002,
   .selp 1603 (.f32imm 4286578688) (.reg 1601) 269, .andImm 1604 1015 134217728,
   .setpImm .eq .b 270 1604 0, .selp 1605 (.f32imm 4286578688) (.reg 1602) 270,
   .andImm 1606 1015 268435456, .setpImm .eq .b 271 1606 0, .unpack 1607 1608 4003,
   .selp 1609 (.f32imm 4286578688) (.reg 1607) 271, .andImm 1610 1015 536870912,
   .setpImm .eq .b 272 1610 0, .selp 1611 (.f32imm 4286578688) (.reg 1608) 272,
   .andImm 1612 1015 1073741824, .setpImm .eq .b 273 1612 0, .unpack 1613 1614 4004,
   .selp 1615 (.f32imm 4286578688) (.reg 1613) 273, .setpImm .gt .s 274 1015 (-1),
   .selp 1616 (.f32imm 4286578688) (.reg 1614) 274, .fmax 1617 1237 1239 none,
   .fmax 1618 1243 1245 none, .fmax 1619 1249 1251 none, .fmax 1620 1255 1257 none,
   .fmax 1621 1617 1261 (some 1263), .fmax 1622 1618 1267 (some 1269),
   .fmax 1623 1619 1273 (some 1275), .fmax 1624 1620 1279 (some 1281),
   .fmax 1625 1621 1285 (some 1287), .fmax 1626 1622 1291 (some 1293),
   .fmax 1627 1623 1297 (some 1299), .fmax 1628 1624 1303 (some 1305),
   .fmax 1629 1625 1309 (some 1311), .fmax 1630 1626 1315 (some 1317),
   .fmax 1631 1627 1321 (some 1323), .fmax 1632 1628 1327 (some 1328),
   .fmax 1633 1629 1333 (some 1335), .fmax 1634 1630 1339 (some 1341),
   .fmax 1635 1631 1345 (some 1347), .fmax 1636 1632 1351 (some 1353),
   .fmax 1637 1633 1357 (some 1359), .fmax 1638 1634 1363 (some 1365),
   .fmax 1639 1635 1369 (some 1371), .fmax 1640 1636 1375 (some 1377),
   .fmax 1641 1637 1381 (some 1383), .fmax 1642 1638 1387 (some 1389),
   .fmax 1643 1639 1393 (some 1395), .fmax 1644 1640 1399 (some 1401),
   .fmax 1645 1641 1405 (some 1407), .fmax 1646 1642 1411 (some 1413),
   .fmax 1647 1643 1417 (some 1419), .fmax 1648 1644 1423 (some 1424),
   .fmax 1649 1645 1429 (some 1431), .fmax 1650 1646 1435 (some 1437),
   .fmax 1651 1647 1441 (some 1443), .fmax 1652 1648 1447 (some 1449),
   .fmax 1653 1649 1453 (some 1455), .fmax 1654 1650 1459 (some 1461),
   .fmax 1655 1651 1465 (some 1467), .fmax 1656 1652 1471 (some 1473),
   .fmax 1657 1653 1477 (some 1479), .fmax 1658 1654 1483 (some 1485),
   .fmax 1659 1655 1489 (some 1491), .fmax 1660 1656 1495 (some 1497),
   .fmax 1661 1657 1501 (some 1503), .fmax 1662 1658 1507 (some 1509),
   .fmax 1663 1659 1513 (some 1515), .fmax 1664 1660 1519 (some 1520),
   .fmax 1665 1661 1525 (some 1527), .fmax 1666 1662 1531 (some 1533),
   .fmax 1667 1663 1537 (some 1539), .fmax 1668 1664 1543 (some 1545),
   .fmax 1669 1665 1549 (some 1551), .fmax 1670 1666 1555 (some 1557),
   .fmax 1671 1667 1561 (some 1563), .fmax 1672 1668 1567 (some 1569),
   .fmax 1673 1669 1573 (some 1575), .fmax 1674 1670 1579 (some 1581),
   .fmax 1675 1671 1585 (some 1587), .fmax 1676 1672 1591 (some 1593),
   .fmax 1677 1673 1597 (some 1599), .fmax 1678 1674 1603 (some 1605),
   .fmax 1679 1675 1609 (some 1611), .fmax 1680 1676 1615 (some 1616), .fmax 1681 1677 1678 none,
   .fmax 3932 1681 1679 (some 1680)]

/-- A loop tile's read run from `2796` to `2926`. -/
def readsMax1_2796 : List RItem :=
  [.unpack 2193 2194 4488, .fmax 2195 3932 2193 (some 2194), .unpack 2196 2197 4487,
   .fmax 2198 2196 2197 none, .unpack 2199 2200 4486, .fmax 2201 2199 2200 none,
   .unpack 2202 2203 4485, .fmax 2204 2202 2203 none, .unpack 2205 2206 4005,
   .fmax 2207 2195 2205 (some 2206), .unpack 2208 2209 4006, .fmax 2210 2198 2208 (some 2209),
   .unpack 2211 2212 4007, .fmax 2213 2201 2211 (some 2212), .unpack 2214 2215 4008,
   .fmax 2216 2204 2214 (some 2215), .unpack 2217 2218 4009, .fmax 2219 2207 2217 (some 2218),
   .unpack 2220 2221 4010, .fmax 2222 2210 2220 (some 2221), .unpack 2223 2224 4011,
   .fmax 2225 2213 2223 (some 2224), .unpack 2226 2227 4012, .fmax 2228 2216 2226 (some 2227),
   .unpack 2229 2230 4013, .fmax 2231 2219 2229 (some 2230), .unpack 2232 2233 4014,
   .fmax 2234 2222 2232 (some 2233), .unpack 2235 2236 4015, .fmax 2237 2225 2235 (some 2236),
   .unpack 2238 2239 4016, .fmax 2240 2228 2238 (some 2239), .unpack 2241 2242 4017,
   .fmax 2243 2231 2241 (some 2242), .unpack 2244 2245 4018, .fmax 2246 2234 2244 (some 2245),
   .unpack 2247 2248 4019, .fmax 2249 2237 2247 (some 2248), .unpack 2250 2251 4020,
   .fmax 2252 2240 2250 (some 2251), .unpack 2253 2254 4021, .fmax 2255 2243 2253 (some 2254),
   .unpack 2256 2257 4022, .fmax 2258 2246 2256 (some 2257), .unpack 2259 2260 4023,
   .fmax 2261 2249 2259 (some 2260), .unpack 2262 2263 4024, .fmax 2264 2252 2262 (some 2263),
   .unpack 2265 2266 4025, .fmax 2267 2255 2265 (some 2266), .unpack 2268 2269 4026,
   .fmax 2270 2258 2268 (some 2269), .unpack 2271 2272 4027, .fmax 2273 2261 2271 (some 2272),
   .unpack 2274 2275 4028, .fmax 2276 2264 2274 (some 2275), .unpack 2277 2278 4029,
   .fmax 2279 2267 2277 (some 2278), .unpack 2280 2281 4030, .fmax 2282 2270 2280 (some 2281),
   .unpack 2283 2284 4031, .fmax 2285 2273 2283 (some 2284), .unpack 2286 2287 4032,
   .fmax 2288 2276 2286 (some 2287), .unpack 2289 2290 4033, .fmax 2291 2279 2289 (some 2290),
   .unpack 2292 2293 4034, .fmax 2294 2282 2292 (some 2293), .unpack 2295 2296 4035,
   .fmax 2297 2285 2295 (some 2296), .unpack 2298 2299 4036, .fmax 2300 2288 2298 (some 2299),
   .unpack 2301 2302 4037, .fmax 2303 2291 2301 (some 2302), .unpack 2304 2305 4038,
   .fmax 2306 2294 2304 (some 2305), .unpack 2307 2308 4039, .fmax 2309 2297 2307 (some 2308),
   .unpack 2310 2311 4040, .fmax 2312 2300 2310 (some 2311), .unpack 2313 2314 4041,
   .fmax 2315 2303 2313 (some 2314), .unpack 2316 2317 4042, .fmax 2318 2306 2316 (some 2317),
   .unpack 2319 2320 4043, .fmax 2321 2309 2319 (some 2320), .unpack 2322 2323 4044,
   .fmax 2324 2312 2322 (some 2323), .unpack 2325 2326 4045, .fmax 2327 2315 2325 (some 2326),
   .unpack 2328 2329 4046, .fmax 2330 2318 2328 (some 2329), .unpack 2331 2332 4047,
   .fmax 2333 2321 2331 (some 2332), .unpack 2334 2335 4048, .fmax 2336 2324 2334 (some 2335),
   .unpack 2337 2338 4049, .fmax 2339 2327 2337 (some 2338), .unpack 2340 2341 4050,
   .fmax 2342 2330 2340 (some 2341), .unpack 2343 2344 4051, .fmax 2345 2333 2343 (some 2344),
   .unpack 2346 2347 4052, .fmax 2348 2336 2346 (some 2347), .unpack 2349 2350 4053,
   .fmax 2351 2339 2349 (some 2350), .unpack 2352 2353 4054, .fmax 2354 2342 2352 (some 2353),
   .unpack 2355 2356 4055, .fmax 2357 2345 2355 (some 2356), .unpack 2358 2359 4056,
   .fmax 2360 2348 2358 (some 2359), .unpack 2361 2362 4057, .fmax 2363 2351 2361 (some 2362),
   .unpack 2364 2365 4058, .fmax 2366 2354 2364 (some 2365), .unpack 2367 2368 4059,
   .fmax 2369 2357 2367 (some 2368), .unpack 2370 2371 4060, .fmax 2372 2360 2370 (some 2371),
   .unpack 2373 2374 4061, .fmax 2375 2363 2373 (some 2374), .unpack 2376 2377 4062,
   .fmax 2378 2366 2376 (some 2377), .unpack 2379 2380 4063, .fmax 2381 2369 2379 (some 2380),
   .unpack 2382 2383 4064, .fmax 2384 2372 2382 (some 2383), .fmax 2385 2375 2378 none,
   .fmax 2386 2385 2381 (some 2384)]

/-- The values at `1341` that are not the table's. -/
def exMax0_1341 (_L : Launch) (d : D) : List (Nat × Value) :=
  [(1008, b32 4294967295), (1009, b32 4294967295), (1232, b32 128),
   (3989, joinValue (d.w 96) (d.w 97)), (3990, joinValue (d.w 98) (d.w 99)),
   (3991, joinValue (d.w 100) (d.w 101)), (3992, joinValue (d.w 102) (d.w 103)),
   (3993, joinValue (d.w 104) (d.w 105)), (3994, joinValue (d.w 106) (d.w 107)),
   (3995, joinValue (d.w 108) (d.w 109)), (3996, joinValue (d.w 110) (d.w 111)),
   (3997, joinValue (d.w 112) (d.w 113)), (3998, joinValue (d.w 114) (d.w 115)),
   (3999, joinValue (d.w 116) (d.w 117)), (4000, joinValue (d.w 118) (d.w 119)),
   (4001, joinValue (d.w 120) (d.w 121)), (4002, joinValue (d.w 122) (d.w 123)),
   (4003, joinValue (d.w 124) (d.w 125)), (4004, joinValue (d.w 126) (d.w 127))]

/-- The values at `1455` that are not the table's. -/
def exMax0_1455 (_L : Launch) (d : D) : List (Nat × Value) :=
  [(1009, b32 4294967295), (1011, b32 4294967295), (1232, b32 128), (1237, half d.w 0),
   (1239, half d.w 1), (1243, half d.w 2), (1245, half d.w 3), (1249, half d.w 4),
   (1251, half d.w 5), (1255, half d.w 6), (1257, half d.w 7), (1261, half d.w 8),
   (1263, half d.w 9), (1267, half d.w 10), (1269, half d.w 11), (1273, half d.w 12),
   (1275, half d.w 13), (1279, half d.w 14), (1281, half d.w 15), (1285, half d.w 16),
   (1287, half d.w 17), (1291, half d.w 18), (1293, half d.w 19), (1297, half d.w 20),
   (1299, half d.w 21), (1303, half d.w 22), (1305, half d.w 23), (1309, half d.w 24),
   (1311, half d.w 25), (1315, half d.w 26), (1317, half d.w 27), (1321, half d.w 28),
   (1323, half d.w 29), (1327, half d.w 30), (1328, half d.w 31),
   (3989, joinValue (d.w 96) (d.w 97)), (3990, joinValue (d.w 98) (d.w 99)),
   (3991, joinValue (d.w 100) (d.w 101)), (3992, joinValue (d.w 102) (d.w 103)),
   (3993, joinValue (d.w 104) (d.w 105)), (3994, joinValue (d.w 106) (d.w 107)),
   (3995, joinValue (d.w 108) (d.w 109)), (3996, joinValue (d.w 110) (d.w 111)),
   (3997, joinValue (d.w 112) (d.w 113)), (3998, joinValue (d.w 114) (d.w 115)),
   (3999, joinValue (d.w 116) (d.w 117)), (4000, joinValue (d.w 118) (d.w 119)),
   (4001, joinValue (d.w 120) (d.w 121)), (4002, joinValue (d.w 122) (d.w 123)),
   (4003, joinValue (d.w 124) (d.w 125)), (4004, joinValue (d.w 126) (d.w 127))]

/-- The values at `1569` that are not the table's. -/
def exMax0_1569 (_L : Launch) (d : D) : List (Nat × Value) :=
  [(1009, b32 4294967295), (1013, b32 4294967295), (1232, b32 128), (1237, half d.w 0),
   (1239, half d.w 1), (1243, half d.w 2), (1245, half d.w 3), (1249, half d.w 4),
   (1251, half d.w 5), (1255, half d.w 6), (1257, half d.w 7), (1261, half d.w 8),
   (1263, half d.w 9), (1267, half d.w 10), (1269, half d.w 11), (1273, half d.w 12),
   (1275, half d.w 13), (1279, half d.w 14), (1281, half d.w 15), (1285, half d.w 16),
   (1287, half d.w 17), (1291, half d.w 18), (1293, half d.w 19), (1297, half d.w 20),
   (1299, half d.w 21), (1303, half d.w 22), (1305, half d.w 23), (1309, half d.w 24),
   (1311, half d.w 25), (1315, half d.w 26), (1317, half d.w 27), (1321, half d.w 28),
   (1323, half d.w 29), (1327, half d.w 30), (1328, half d.w 31), (1333, half d.w 32),
   (1335, half d.w 33), (1339, half d.w 34), (1341, half d.w 35), (1345, half d.w 36),
   (1347, half d.w 37), (1351, half d.w 38), (1353, half d.w 39), (1357, half d.w 40),
   (1359, half d.w 41), (1363, half d.w 42), (1365, half d.w 43), (1369, half d.w 44),
   (1371, half d.w 45), (1375, half d.w 46), (1377, half d.w 47), (1381, half d.w 48),
   (1383, half d.w 49), (1387, half d.w 50), (1389, half d.w 51), (1393, half d.w 52),
   (1395, half d.w 53), (1399, half d.w 54), (1401, half d.w 55), (1405, half d.w 56),
   (1407, half d.w 57), (1411, half d.w 58), (1413, half d.w 59), (1417, half d.w 60),
   (1419, half d.w 61), (1423, half d.w 62), (1424, half d.w 63),
   (3989, joinValue (d.w 96) (d.w 97)), (3990, joinValue (d.w 98) (d.w 99)),
   (3991, joinValue (d.w 100) (d.w 101)), (3992, joinValue (d.w 102) (d.w 103)),
   (3993, joinValue (d.w 104) (d.w 105)), (3994, joinValue (d.w 106) (d.w 107)),
   (3995, joinValue (d.w 108) (d.w 109)), (3996, joinValue (d.w 110) (d.w 111)),
   (3997, joinValue (d.w 112) (d.w 113)), (3998, joinValue (d.w 114) (d.w 115)),
   (3999, joinValue (d.w 116) (d.w 117)), (4000, joinValue (d.w 118) (d.w 119)),
   (4001, joinValue (d.w 120) (d.w 121)), (4002, joinValue (d.w 122) (d.w 123)),
   (4003, joinValue (d.w 124) (d.w 125)), (4004, joinValue (d.w 126) (d.w 127))]

/-- The values at `1683` that are not the table's. -/
def exMax0_1683 (_L : Launch) (d : D) : List (Nat × Value) :=
  [(1015, b32 4294967295), (1237, half d.w 0), (1239, half d.w 1), (1243, half d.w 2),
   (1245, half d.w 3), (1249, half d.w 4), (1251, half d.w 5), (1255, half d.w 6),
   (1257, half d.w 7), (1261, half d.w 8), (1263, half d.w 9), (1267, half d.w 10),
   (1269, half d.w 11), (1273, half d.w 12), (1275, half d.w 13), (1279, half d.w 14),
   (1281, half d.w 15), (1285, half d.w 16), (1287, half d.w 17), (1291, half d.w 18),
   (1293, half d.w 19), (1297, half d.w 20), (1299, half d.w 21), (1303, half d.w 22),
   (1305, half d.w 23), (1309, half d.w 24), (1311, half d.w 25), (1315, half d.w 26),
   (1317, half d.w 27), (1321, half d.w 28), (1323, half d.w 29), (1327, half d.w 30),
   (1328, half d.w 31), (1333, half d.w 32), (1335, half d.w 33), (1339, half d.w 34),
   (1341, half d.w 35), (1345, half d.w 36), (1347, half d.w 37), (1351, half d.w 38),
   (1353, half d.w 39), (1357, half d.w 40), (1359, half d.w 41), (1363, half d.w 42),
   (1365, half d.w 43), (1369, half d.w 44), (1371, half d.w 45), (1375, half d.w 46),
   (1377, half d.w 47), (1381, half d.w 48), (1383, half d.w 49), (1387, half d.w 50),
   (1389, half d.w 51), (1393, half d.w 52), (1395, half d.w 53), (1399, half d.w 54),
   (1401, half d.w 55), (1405, half d.w 56), (1407, half d.w 57), (1411, half d.w 58),
   (1413, half d.w 59), (1417, half d.w 60), (1419, half d.w 61), (1423, half d.w 62),
   (1424, half d.w 63), (1429, half d.w 64), (1431, half d.w 65), (1435, half d.w 66),
   (1437, half d.w 67), (1441, half d.w 68), (1443, half d.w 69), (1447, half d.w 70),
   (1449, half d.w 71), (1453, half d.w 72), (1455, half d.w 73), (1459, half d.w 74),
   (1461, half d.w 75), (1465, half d.w 76), (1467, half d.w 77), (1471, half d.w 78),
   (1473, half d.w 79), (1477, half d.w 80), (1479, half d.w 81), (1483, half d.w 82),
   (1485, half d.w 83), (1489, half d.w 84), (1491, half d.w 85), (1495, half d.w 86),
   (1497, half d.w 87), (1501, half d.w 88), (1503, half d.w 89), (1507, half d.w 90),
   (1509, half d.w 91), (1513, half d.w 92), (1515, half d.w 93), (1519, half d.w 94),
   (1520, half d.w 95), (3989, joinValue (d.w 96) (d.w 97)), (3990, joinValue (d.w 98) (d.w 99)),
   (3991, joinValue (d.w 100) (d.w 101)), (3992, joinValue (d.w 102) (d.w 103)),
   (3993, joinValue (d.w 104) (d.w 105)), (3994, joinValue (d.w 106) (d.w 107)),
   (3995, joinValue (d.w 108) (d.w 109)), (3996, joinValue (d.w 110) (d.w 111)),
   (3997, joinValue (d.w 112) (d.w 113)), (3998, joinValue (d.w 114) (d.w 115)),
   (3999, joinValue (d.w 116) (d.w 117)), (4000, joinValue (d.w 118) (d.w 119)),
   (4001, joinValue (d.w 120) (d.w 121)), (4002, joinValue (d.w 122) (d.w 123)),
   (4003, joinValue (d.w 124) (d.w 125)), (4004, joinValue (d.w 126) (d.w 127))]

/-- The values at `1860` that are not the table's. -/
def exMax0_1860 (_L : Launch) (d : D) : List (Nat × Value) :=
  [(1237, half d.w 0), (1239, half d.w 1), (1243, half d.w 2), (1245, half d.w 3),
   (1249, half d.w 4), (1251, half d.w 5), (1255, half d.w 6), (1257, half d.w 7),
   (1261, half d.w 8), (1263, half d.w 9), (1267, half d.w 10), (1269, half d.w 11),
   (1273, half d.w 12), (1275, half d.w 13), (1279, half d.w 14), (1281, half d.w 15),
   (1285, half d.w 16), (1287, half d.w 17), (1291, half d.w 18), (1293, half d.w 19),
   (1297, half d.w 20), (1299, half d.w 21), (1303, half d.w 22), (1305, half d.w 23),
   (1309, half d.w 24), (1311, half d.w 25), (1315, half d.w 26), (1317, half d.w 27),
   (1321, half d.w 28), (1323, half d.w 29), (1327, half d.w 30), (1328, half d.w 31),
   (1333, half d.w 32), (1335, half d.w 33), (1339, half d.w 34), (1341, half d.w 35),
   (1345, half d.w 36), (1347, half d.w 37), (1351, half d.w 38), (1353, half d.w 39),
   (1357, half d.w 40), (1359, half d.w 41), (1363, half d.w 42), (1365, half d.w 43),
   (1369, half d.w 44), (1371, half d.w 45), (1375, half d.w 46), (1377, half d.w 47),
   (1381, half d.w 48), (1383, half d.w 49), (1387, half d.w 50), (1389, half d.w 51),
   (1393, half d.w 52), (1395, half d.w 53), (1399, half d.w 54), (1401, half d.w 55),
   (1405, half d.w 56), (1407, half d.w 57), (1411, half d.w 58), (1413, half d.w 59),
   (1417, half d.w 60), (1419, half d.w 61), (1423, half d.w 62), (1424, half d.w 63),
   (1429, half d.w 64), (1431, half d.w 65), (1435, half d.w 66), (1437, half d.w 67),
   (1441, half d.w 68), (1443, half d.w 69), (1447, half d.w 70), (1449, half d.w 71),
   (1453, half d.w 72), (1455, half d.w 73), (1459, half d.w 74), (1461, half d.w 75),
   (1465, half d.w 76), (1467, half d.w 77), (1471, half d.w 78), (1473, half d.w 79),
   (1477, half d.w 80), (1479, half d.w 81), (1483, half d.w 82), (1485, half d.w 83),
   (1489, half d.w 84), (1491, half d.w 85), (1495, half d.w 86), (1497, half d.w 87),
   (1501, half d.w 88), (1503, half d.w 89), (1507, half d.w 90), (1509, half d.w 91),
   (1513, half d.w 92), (1515, half d.w 93), (1519, half d.w 94), (1520, half d.w 95),
   (1525, half d.w 96), (1527, half d.w 97), (1531, half d.w 98), (1533, half d.w 99),
   (1537, half d.w 100), (1539, half d.w 101), (1543, half d.w 102), (1545, half d.w 103),
   (1549, half d.w 104), (1551, half d.w 105), (1555, half d.w 106), (1557, half d.w 107),
   (1561, half d.w 108), (1563, half d.w 109), (1567, half d.w 110), (1569, half d.w 111),
   (1573, half d.w 112), (1575, half d.w 113), (1579, half d.w 114), (1581, half d.w 115),
   (1585, half d.w 116), (1587, half d.w 117), (1591, half d.w 118), (1593, half d.w 119),
   (1597, half d.w 120), (1599, half d.w 121), (1603, half d.w 122), (1605, half d.w 123),
   (1609, half d.w 124), (1611, half d.w 125), (1615, half d.w 126), (1616, half d.w 127),
   (3932, rmax0V d.w)]

/-- The values at `2926` that are not the table's. -/
def exMax1_2926 (_L : Launch) (d : D) : List (Nat × Value) :=
  [(2386, mxV d.m d.w)]

/-- The packs after a load accept its words, or (after the last load) the packs, the row maximum
and its test against `-∞` accept them. -/
def Max0Ok (L : Launch) (g : Nat) (d : D) : Prop :=
  packsOk (valueEx (valueOf L g d) []) (ldPacks false 3) = true ∧
    rCond (valueEx (valueOf L g d) (exMax0_1341 L d)) readsMax0_1341 ∧
    rCond (valueEx (valueOf L g d) (exMax0_1455 L d)) readsMax0_1455 ∧
    rCond (valueEx (valueOf L g d) (exMax0_1569 L d)) readsMax0_1569 ∧
    rCond (valueEx (valueOf L g d) (exMax0_1683 L d)) readsMax0_1683 ∧
    oCond (valueEx (valueOf L g d) (exMax0_1860 L d ++ exMax0_1683 L d)) max0T

/-- A loop tile's last packs, row maximum and lazy rescale accept the words. -/
def Max1Ok (L : Launch) (g : Nat) (d : D) : Prop :=
  packsOk (valueEx (valueOf L g d) []) (ldPacks true 3) = true ∧
    rCond (valueEx (valueOf L g d) (packVals (valueEx (valueOf L g d) []) (ldPacks true 3) ++
      [])) readsMax1_2796 ∧
    oCond (valueEx (valueOf L g d) (exMax1_2926 L d ++
      (packVals (valueEx (valueOf L g d) []) (ldPacks true 3) ++ []))) max1T

/-- The run after the implicit wait of load `c` accepts the words. -/
def WaitOk (L : Launch) (g : Nat) (lp : Bool) (c : Fin 4) (d : D) : Prop :=
  if c.val < 3 then packsOk (valueEx (valueOf L g d) []) (ldPacks lp c.val) = true
  else if lp then Max1Ok L g d else Max0Ok L g d

/-- The first tile's exponentials accept their arguments: no instruction faults and the software
`exp2`'s inputs read as numbers. -/
def ExpOk0 (L : Launch) (g : Nat) (d : D) : Prop :=
  chainCond (valueOf L g d) exp0Pieces

/-- A loop tile's exponentials accept their arguments. -/
def ExpOk1 (L : Launch) (g : Nat) (d : D) : Prop :=
  chainCond (valueOf L g d) exp1Pieces

/-- The first tile's row sum accepts the probabilities: no instruction faults (the last
`add.f32`, without a rounding modifier, faults where the ideal rule declines). -/
def SumOk0 (L : Launch) (g : Nat) (d : D) : Prop :=
  oCond (valueOf L g d) sum0Items

/-- A loop tile's row sum accepts its operands, and the new reference maximum has four bytes
(`mov.b32 %r3597, %r177`). -/
def SumOk1 (L : Launch) (g : Nat) (d : D) : Prop :=
  oCond (valueOf L g d) sum1Items ∧ (mNV L d).bytes = 4

/-- The run after a successful statistics poll accepts its operands. -/
def StatsOk (L : Launch) (g : Nat) (w : Fin 4) (d : D) : Prop :=
  match w with
  | 1 => SumOk0 L g d
  | 2 => SumOk1 L g d
  | _ => True

theorem waitOk_lt {L : Launch} {g : Nat} {lp : Bool} {c : Fin 4} {d : D} (h : c.val < 3) :
    WaitOk L g lp c d ↔ packsOk (valueEx (valueOf L g d) []) (ldPacks lp c.val) = true := by
  unfold WaitOk
  simp only [h, ↓reduceIte]

theorem waitOk_max0 {L : Launch} {g : Nat} {d : D} : WaitOk L g false 3 d ↔ Max0Ok L g d := by
  unfold WaitOk
  simp only [show ¬ ((3 : Fin 4).val < 3) by decide, ↓reduceIte, Bool.false_eq_true]

theorem waitOk_max1 {L : Launch} {g : Nat} {d : D} : WaitOk L g true 3 d ↔ Max1Ok L g d := by
  unfold WaitOk
  simp only [show ¬ ((3 : Fin 4).val < 3) by decide, ↓reduceIte]

theorem expOk0_iff {L : Launch} {g : Nat} {d : D} :
    ExpOk0 L g d ↔ chainCond (valueOf L g d) exp0Pieces := by
  unfold ExpOk0
  rfl

theorem expOk1_iff {L : Launch} {g : Nat} {d : D} :
    ExpOk1 L g d ↔ chainCond (valueOf L g d) exp1Pieces := by
  unfold ExpOk1
  rfl

theorem statsOk_1 {L : Launch} {g : Nat} {d : D} : StatsOk L g 1 d ↔ SumOk0 L g d := Iff.rfl

theorem statsOk_2 {L : Launch} {g : Nat} {d : D} : StatsOk L g 2 d ↔ SumOk1 L g d := Iff.rfl

theorem statsOk_0 {L : Launch} {g : Nat} {d : D} : StatsOk L g 0 d := trivial

theorem statsOk_3 {L : Launch} {g : Nat} {d : D} : StatsOk L g 3 d := trivial

/- The conditions are opaque to evaluation: a proof uses them through these equations. -/
attribute [irreducible] WaitOk ExpOk0 ExpOk1 StatsOk

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
