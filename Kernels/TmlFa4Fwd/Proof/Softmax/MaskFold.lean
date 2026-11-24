-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Softmax.MaskSeg
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Epilogue.Base

@[expose] public section

/-! # The masked maximum's fold

The `max.f32` tree over the 128 masked elements (pcs 4329 to 4395): from the masked elements,
the row maximum `%r6196` is `erealValue .f32 (foldM m (bpe bf sc))`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- **The fold of the masked elements.** -/
theorem mask_fold (L : Launch) (g : Nat) (m : BitVec 64) (sc : Nat → ℝ) (bf : Nat → Bool) :
    ∃ n, Seg kernel Assumptions.all L g n 4329
    ((3240, if mkeep0 0 m = true then bv32 bf sc 0
         else .bits 32 (BitVec.ofNat 64 4286578688)) ::
     (3242, if mdrop 0 m 1 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 1) ::
     (3246, if mdrop 0 m 2 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 2) ::
     (3248, if mdrop 0 m 3 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 3) ::
     (3252, if mdrop 0 m 4 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 4) ::
     (3254, if mdrop 0 m 5 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 5) ::
     (3258, if mdrop 0 m 6 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 6) ::
     (3260, if mdrop 0 m 7 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 7) ::
     (3264, if mdrop 0 m 8 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 8) ::
     (3266, if mdrop 0 m 9 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 9) ::
     (3270, if mdrop 0 m 10 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 10) ::
     (3272, if mdrop 0 m 11 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 11) ::
     (3276, if mdrop 0 m 12 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 12) ::
     (3278, if mdrop 0 m 13 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 13) ::
     (3282, if mdrop 0 m 14 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 14) ::
     (3284, if mdrop 0 m 15 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 15) ::
     (3288, if mdrop 0 m 16 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 16) ::
     (3290, if mdrop 0 m 17 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 17) ::
     (3294, if mdrop 0 m 18 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 18) ::
     (3296, if mdrop 0 m 19 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 19) ::
     (3300, if mdrop 0 m 20 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 20) ::
     (3302, if mdrop 0 m 21 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 21) ::
     (3306, if mdrop 0 m 22 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 22) ::
     (3308, if mdrop 0 m 23 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 23) ::
     (3312, if mdrop 0 m 24 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 24) ::
     (3314, if mdrop 0 m 25 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 25) ::
     (3318, if mdrop 0 m 26 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 26) ::
     (3320, if mdrop 0 m 27 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 27) ::
     (3324, if mdrop 0 m 28 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 28) ::
     (3326, if mdrop 0 m 29 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 29) ::
     (3330, if mdrop 0 m 30 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 30) ::
     (3331, if mdrop31 0 m = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 31) ::
     (3336, if mkeep0 1 m = true then bv32 bf sc 32
         else .bits 32 (BitVec.ofNat 64 4286578688)) ::
     (3338, if mdrop 1 m 1 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 33) ::
     (3342, if mdrop 1 m 2 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 34) ::
     (3344, if mdrop 1 m 3 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 35) ::
     (3348, if mdrop 1 m 4 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 36) ::
     (3350, if mdrop 1 m 5 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 37) ::
     (3354, if mdrop 1 m 6 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 38) ::
     (3356, if mdrop 1 m 7 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 39) ::
     (3360, if mdrop 1 m 8 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 40) ::
     (3362, if mdrop 1 m 9 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 41) ::
     (3366, if mdrop 1 m 10 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 42) ::
     (3368, if mdrop 1 m 11 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 43) ::
     (3372, if mdrop 1 m 12 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 44) ::
     (3374, if mdrop 1 m 13 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 45) ::
     (3378, if mdrop 1 m 14 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 46) ::
     (3380, if mdrop 1 m 15 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 47) ::
     (3384, if mdrop 1 m 16 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 48) ::
     (3386, if mdrop 1 m 17 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 49) ::
     (3390, if mdrop 1 m 18 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 50) ::
     (3392, if mdrop 1 m 19 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 51) ::
     (3396, if mdrop 1 m 20 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 52) ::
     (3398, if mdrop 1 m 21 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 53) ::
     (3402, if mdrop 1 m 22 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 54) ::
     (3404, if mdrop 1 m 23 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 55) ::
     (3408, if mdrop 1 m 24 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 56) ::
     (3410, if mdrop 1 m 25 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 57) ::
     (3414, if mdrop 1 m 26 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 58) ::
     (3416, if mdrop 1 m 27 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 59) ::
     (3420, if mdrop 1 m 28 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 60) ::
     (3422, if mdrop 1 m 29 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 61) ::
     (3426, if mdrop 1 m 30 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 62) ::
     (3427, if mdrop31 1 m = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 63) ::
     (3432, if mkeep0 2 m = true then bv32 bf sc 64
         else .bits 32 (BitVec.ofNat 64 4286578688)) ::
     (3434, if mdrop 2 m 1 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 65) ::
     (3438, if mdrop 2 m 2 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 66) ::
     (3440, if mdrop 2 m 3 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 67) ::
     (3444, if mdrop 2 m 4 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 68) ::
     (3446, if mdrop 2 m 5 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 69) ::
     (3450, if mdrop 2 m 6 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 70) ::
     (3452, if mdrop 2 m 7 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 71) ::
     (3456, if mdrop 2 m 8 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 72) ::
     (3458, if mdrop 2 m 9 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 73) ::
     (3462, if mdrop 2 m 10 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 74) ::
     (3464, if mdrop 2 m 11 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 75) ::
     (3468, if mdrop 2 m 12 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 76) ::
     (3470, if mdrop 2 m 13 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 77) ::
     (3474, if mdrop 2 m 14 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 78) ::
     (3476, if mdrop 2 m 15 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 79) ::
     (3480, if mdrop 2 m 16 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 80) ::
     (3482, if mdrop 2 m 17 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 81) ::
     (3486, if mdrop 2 m 18 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 82) ::
     (3488, if mdrop 2 m 19 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 83) ::
     (3492, if mdrop 2 m 20 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 84) ::
     (3494, if mdrop 2 m 21 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 85) ::
     (3498, if mdrop 2 m 22 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 86) ::
     (3500, if mdrop 2 m 23 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 87) ::
     (3504, if mdrop 2 m 24 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 88) ::
     (3506, if mdrop 2 m 25 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 89) ::
     (3510, if mdrop 2 m 26 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 90) ::
     (3512, if mdrop 2 m 27 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 91) ::
     (3516, if mdrop 2 m 28 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 92) ::
     (3518, if mdrop 2 m 29 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 93) ::
     (3522, if mdrop 2 m 30 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 94) ::
     (3523, if mdrop31 2 m = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 95) ::
     (3528, if mkeep0 3 m = true then bv32 bf sc 96
         else .bits 32 (BitVec.ofNat 64 4286578688)) ::
     (3530, if mdrop 3 m 1 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 97) ::
     (3534, if mdrop 3 m 2 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 98) ::
     (3536, if mdrop 3 m 3 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 99) ::
     (3540, if mdrop 3 m 4 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 100) ::
     (3542, if mdrop 3 m 5 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 101) ::
     (3546, if mdrop 3 m 6 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 102) ::
     (3548, if mdrop 3 m 7 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 103) ::
     (3552, if mdrop 3 m 8 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 104) ::
     (3554, if mdrop 3 m 9 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 105) ::
     (3558, if mdrop 3 m 10 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 106) ::
     (3560, if mdrop 3 m 11 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 107) ::
     (3564, if mdrop 3 m 12 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 108) ::
     (3566, if mdrop 3 m 13 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 109) ::
     (3570, if mdrop 3 m 14 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 110) ::
     (3572, if mdrop 3 m 15 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 111) ::
     (3576, if mdrop 3 m 16 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 112) ::
     (3578, if mdrop 3 m 17 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 113) ::
     (3582, if mdrop 3 m 18 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 114) ::
     (3584, if mdrop 3 m 19 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 115) ::
     (3588, if mdrop 3 m 20 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 116) ::
     (3590, if mdrop 3 m 21 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 117) ::
     (3594, if mdrop 3 m 22 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 118) ::
     (3596, if mdrop 3 m 23 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 119) ::
     (3600, if mdrop 3 m 24 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 120) ::
     (3602, if mdrop 3 m 25 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 121) ::
     (3606, if mdrop 3 m 26 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 122) ::
     (3608, if mdrop 3 m 27 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 123) ::
     (3612, if mdrop 3 m 28 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 124) ::
     (3614, if mdrop 3 m 29 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 125) ::
     (3618, if mdrop 3 m 30 = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 126) ::
     (3619, if mdrop31 3 m = true then .bits 32 (BitVec.ofNat 64 4286578688)
         else bv32 bf sc 127) :: [])
    4395 [(7256, Assumption.erealValue .f32 (foldM m (bpe bf sc)))] := by
  seg_sym using (intro t h; seg_fp h using first | rfl | sym_close)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
