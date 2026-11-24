-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftAcceptBase

@[expose] public section

/-! # Loop tiles' row maximum and the packs accept single-precision words

The loop tile's read run (`accept_2796`) and the packs after each load (`packs_ok_*`) are
accepted when the words are single-precision numbers. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The shapes of the registers `readsMax1_2796` reads first. -/
def tys_2796 : List (Nat × RTy) :=
  [(4488, .f32x2), (3932, .f32), (4487, .f32x2), (4486, .f32x2), (4485, .f32x2), (4005, .f32x2),
   (4006, .f32x2), (4007, .f32x2), (4008, .f32x2), (4009, .f32x2), (4010, .f32x2),
   (4011, .f32x2), (4012, .f32x2), (4013, .f32x2), (4014, .f32x2), (4015, .f32x2),
   (4016, .f32x2), (4017, .f32x2), (4018, .f32x2), (4019, .f32x2), (4020, .f32x2),
   (4021, .f32x2), (4022, .f32x2), (4023, .f32x2), (4024, .f32x2), (4025, .f32x2),
   (4026, .f32x2), (4027, .f32x2), (4028, .f32x2), (4029, .f32x2), (4030, .f32x2),
   (4031, .f32x2), (4032, .f32x2), (4033, .f32x2), (4034, .f32x2), (4035, .f32x2),
   (4036, .f32x2), (4037, .f32x2), (4038, .f32x2), (4039, .f32x2), (4040, .f32x2),
   (4041, .f32x2), (4042, .f32x2), (4043, .f32x2), (4044, .f32x2), (4045, .f32x2),
   (4046, .f32x2), (4047, .f32x2), (4048, .f32x2), (4049, .f32x2), (4050, .f32x2),
   (4051, .f32x2), (4052, .f32x2), (4053, .f32x2), (4054, .f32x2), (4055, .f32x2),
   (4056, .f32x2), (4057, .f32x2), (4058, .f32x2), (4059, .f32x2), (4060, .f32x2),
   (4061, .f32x2), (4062, .f32x2), (4063, .f32x2), (4064, .f32x2)]

variable {L : Launch} {g : Nat}

theorem accept_2796 {d : D} (hf : ∀ k < 128, RTy.Has .f32 (d.w k)) (hm : RTy.Has .f32 d.m) :
    rCond (valueEx (valueOf L g d) (packVals (valueEx (valueOf L g d) []) (ldPacks true 3) ++
      [])) readsMax1_2796 := by
  refine rCond_of_rTy (T := tyOf tys_2796) (all_tyOf fun p hp => ?_) (by decide +kernel)
  simp only [tys_2796, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [valueEx, valueOf, ctrlValues, PTX.Flow.lookupLit,
    Option.getD_some, packVals, ldPacks,
    List.append_nil, List.nil_append, List.cons_append]
  all_goals first
    | exact has_join (hf _ (by norm_num)) (hf _ (by norm_num))
    | exact hm

/-- The shapes of the sources of the packs after load `0`. -/
def tysP_F0 : List (Nat × RTy) :=
  [(1132, .f32), (1133, .f32), (1130, .f32), (1131, .f32), (1128, .f32), (1129, .f32),
   (1126, .f32), (1127, .f32), (1124, .f32), (1125, .f32), (1122, .f32), (1123, .f32),
   (1120, .f32), (1121, .f32), (1118, .f32), (1119, .f32), (1116, .f32), (1117, .f32),
   (1114, .f32), (1115, .f32), (1112, .f32), (1113, .f32), (1110, .f32), (1111, .f32),
   (1108, .f32), (1109, .f32), (1106, .f32), (1107, .f32), (1104, .f32), (1105, .f32),
   (1102, .f32), (1103, .f32)]

theorem packs_ok_F0 {d : D} (hf : ∀ k < 32, RTy.Has .f32 (d.w k)) :
    packsOk (valueEx (valueOf L g d) []) (ldPacks false 0) = true := by
  refine packsOk_of_ty (T := tyOf tysP_F0) (all_tyOf fun p hp => ?_) (by decide +kernel)
  simp only [tysP_F0, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp only [valueEx, valueOf, ctrlValues, PTX.Flow.lookupLit,
    Option.getD_some]
  all_goals exact hf _ (by norm_num)

/-- The shapes of the sources of the packs after load `1`. -/
def tysP_F1 : List (Nat × RTy) :=
  [(1164, .f32), (1165, .f32), (1162, .f32), (1163, .f32), (1160, .f32), (1161, .f32),
   (1158, .f32), (1159, .f32), (1156, .f32), (1157, .f32), (1154, .f32), (1155, .f32),
   (1152, .f32), (1153, .f32), (1150, .f32), (1151, .f32), (1148, .f32), (1149, .f32),
   (1146, .f32), (1147, .f32), (1144, .f32), (1145, .f32), (1142, .f32), (1143, .f32),
   (1140, .f32), (1141, .f32), (1138, .f32), (1139, .f32), (1136, .f32), (1137, .f32),
   (1134, .f32), (1135, .f32)]

theorem packs_ok_F1 {d : D} (hf : ∀ k < 64, RTy.Has .f32 (d.w k)) :
    packsOk (valueEx (valueOf L g d) []) (ldPacks false 1) = true := by
  refine packsOk_of_ty (T := tyOf tysP_F1) (all_tyOf fun p hp => ?_) (by decide +kernel)
  simp only [tysP_F1, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp only [valueEx, valueOf, ctrlValues, PTX.Flow.lookupLit,
    Option.getD_some]
  all_goals exact hf _ (by norm_num)

/-- The shapes of the sources of the packs after load `2`. -/
def tysP_F2 : List (Nat × RTy) :=
  [(1196, .f32), (1197, .f32), (1194, .f32), (1195, .f32), (1192, .f32), (1193, .f32),
   (1190, .f32), (1191, .f32), (1188, .f32), (1189, .f32), (1186, .f32), (1187, .f32),
   (1184, .f32), (1185, .f32), (1182, .f32), (1183, .f32), (1180, .f32), (1181, .f32),
   (1178, .f32), (1179, .f32), (1176, .f32), (1177, .f32), (1174, .f32), (1175, .f32),
   (1172, .f32), (1173, .f32), (1170, .f32), (1171, .f32), (1168, .f32), (1169, .f32),
   (1166, .f32), (1167, .f32)]

theorem packs_ok_F2 {d : D} (hf : ∀ k < 96, RTy.Has .f32 (d.w k)) :
    packsOk (valueEx (valueOf L g d) []) (ldPacks false 2) = true := by
  refine packsOk_of_ty (T := tyOf tysP_F2) (all_tyOf fun p hp => ?_) (by decide +kernel)
  simp only [tysP_F2, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp only [valueEx, valueOf, ctrlValues, PTX.Flow.lookupLit,
    Option.getD_some]
  all_goals exact hf _ (by norm_num)

/-- The shapes of the sources of the packs after load `3`. -/
def tysP_F3 : List (Nat × RTy) :=
  [(1228, .f32), (1229, .f32), (1226, .f32), (1227, .f32), (1224, .f32), (1225, .f32),
   (1222, .f32), (1223, .f32), (1220, .f32), (1221, .f32), (1218, .f32), (1219, .f32),
   (1216, .f32), (1217, .f32), (1214, .f32), (1215, .f32), (1212, .f32), (1213, .f32),
   (1210, .f32), (1211, .f32), (1208, .f32), (1209, .f32), (1206, .f32), (1207, .f32),
   (1204, .f32), (1205, .f32), (1202, .f32), (1203, .f32), (1200, .f32), (1201, .f32),
   (1198, .f32), (1199, .f32)]

theorem packs_ok_F3 {d : D} (hf : ∀ k < 128, RTy.Has .f32 (d.w k)) :
    packsOk (valueEx (valueOf L g d) []) (ldPacks false 3) = true := by
  refine packsOk_of_ty (T := tyOf tysP_F3) (all_tyOf fun p hp => ?_) (by decide +kernel)
  simp only [tysP_F3, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp only [valueEx, valueOf, ctrlValues, PTX.Flow.lookupLit,
    Option.getD_some]
  all_goals exact hf _ (by norm_num)

/-- The shapes of the sources of the packs after load `0`. -/
def tysP_T0 : List (Nat × RTy) :=
  [(2095, .f32), (2096, .f32), (2093, .f32), (2094, .f32), (2091, .f32), (2092, .f32),
   (2089, .f32), (2090, .f32), (2087, .f32), (2088, .f32), (2085, .f32), (2086, .f32),
   (2083, .f32), (2084, .f32), (2081, .f32), (2082, .f32), (2079, .f32), (2080, .f32),
   (2077, .f32), (2078, .f32), (2075, .f32), (2076, .f32), (2073, .f32), (2074, .f32),
   (2071, .f32), (2072, .f32), (2069, .f32), (2070, .f32), (2067, .f32), (2068, .f32),
   (2065, .f32), (2066, .f32)]

theorem packs_ok_T0 {d : D} (hf : ∀ k < 32, RTy.Has .f32 (d.w k)) :
    packsOk (valueEx (valueOf L g d) []) (ldPacks true 0) = true := by
  refine packsOk_of_ty (T := tyOf tysP_T0) (all_tyOf fun p hp => ?_) (by decide +kernel)
  simp only [tysP_T0, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp only [valueEx, valueOf, ctrlValues, PTX.Flow.lookupLit,
    Option.getD_some]
  all_goals exact hf _ (by norm_num)

/-- The shapes of the sources of the packs after load `1`. -/
def tysP_T1 : List (Nat × RTy) :=
  [(2127, .f32), (2128, .f32), (2125, .f32), (2126, .f32), (2123, .f32), (2124, .f32),
   (2121, .f32), (2122, .f32), (2119, .f32), (2120, .f32), (2117, .f32), (2118, .f32),
   (2115, .f32), (2116, .f32), (2113, .f32), (2114, .f32), (2111, .f32), (2112, .f32),
   (2109, .f32), (2110, .f32), (2107, .f32), (2108, .f32), (2105, .f32), (2106, .f32),
   (2103, .f32), (2104, .f32), (2101, .f32), (2102, .f32), (2099, .f32), (2100, .f32),
   (2097, .f32), (2098, .f32)]

theorem packs_ok_T1 {d : D} (hf : ∀ k < 64, RTy.Has .f32 (d.w k)) :
    packsOk (valueEx (valueOf L g d) []) (ldPacks true 1) = true := by
  refine packsOk_of_ty (T := tyOf tysP_T1) (all_tyOf fun p hp => ?_) (by decide +kernel)
  simp only [tysP_T1, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp only [valueEx, valueOf, ctrlValues, PTX.Flow.lookupLit,
    Option.getD_some]
  all_goals exact hf _ (by norm_num)

/-- The shapes of the sources of the packs after load `2`. -/
def tysP_T2 : List (Nat × RTy) :=
  [(2159, .f32), (2160, .f32), (2157, .f32), (2158, .f32), (2155, .f32), (2156, .f32),
   (2153, .f32), (2154, .f32), (2151, .f32), (2152, .f32), (2149, .f32), (2150, .f32),
   (2147, .f32), (2148, .f32), (2145, .f32), (2146, .f32), (2143, .f32), (2144, .f32),
   (2141, .f32), (2142, .f32), (2139, .f32), (2140, .f32), (2137, .f32), (2138, .f32),
   (2135, .f32), (2136, .f32), (2133, .f32), (2134, .f32), (2131, .f32), (2132, .f32),
   (2129, .f32), (2130, .f32)]

theorem packs_ok_T2 {d : D} (hf : ∀ k < 96, RTy.Has .f32 (d.w k)) :
    packsOk (valueEx (valueOf L g d) []) (ldPacks true 2) = true := by
  refine packsOk_of_ty (T := tyOf tysP_T2) (all_tyOf fun p hp => ?_) (by decide +kernel)
  simp only [tysP_T2, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp only [valueEx, valueOf, ctrlValues, PTX.Flow.lookupLit,
    Option.getD_some]
  all_goals exact hf _ (by norm_num)

/-- The shapes of the sources of the packs after load `3`. -/
def tysP_T3 : List (Nat × RTy) :=
  [(2191, .f32), (2192, .f32), (2189, .f32), (2190, .f32), (2187, .f32), (2188, .f32),
   (2185, .f32), (2186, .f32), (2183, .f32), (2184, .f32), (2181, .f32), (2182, .f32),
   (2179, .f32), (2180, .f32), (2177, .f32), (2178, .f32), (2175, .f32), (2176, .f32),
   (2173, .f32), (2174, .f32), (2171, .f32), (2172, .f32), (2169, .f32), (2170, .f32),
   (2167, .f32), (2168, .f32), (2165, .f32), (2166, .f32), (2163, .f32), (2164, .f32),
   (2161, .f32), (2162, .f32)]

theorem packs_ok_T3 {d : D} (hf : ∀ k < 128, RTy.Has .f32 (d.w k)) :
    packsOk (valueEx (valueOf L g d) []) (ldPacks true 3) = true := by
  refine packsOk_of_ty (T := tyOf tysP_T3) (all_tyOf fun p hp => ?_) (by decide +kernel)
  simp only [tysP_T3, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp only [valueEx, valueOf, ctrlValues, PTX.Flow.lookupLit,
    Option.getD_some]
  all_goals exact hf _ (by norm_num)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
