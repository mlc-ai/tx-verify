-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Sites.Decl
public import Kernels.TmlFa4Fwd.Proof.Correction.Base

@[expose] public section

/-! # The correction warps' event instructions -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

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

end
end PTX.Kernels.TmlFa4Fwd.Proof
