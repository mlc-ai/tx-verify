-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.MaskSeg

@[expose] public section

/-! # The masked maximum's selects: mask word 2

The third 32 selects of the first round's causal mask (pcs 4101 to 4215): from the mask count `m`
(`%r2175`) and the bias-product pairs 7961 to 7991, each element is its bias product or `-∞` as the
code's mask word `mword 2 m` keeps it. One `Seg` per mask word, so the four check in parallel; the
piece also carries the elements selected before it and the bias-product pairs of the later words, so
that its end facts are the next piece's start facts (`MaskChain.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- **The selects of mask word 2.** -/
theorem mask_word2 (L : Launch) (g : Nat) (m : BitVec 64) (sc : Nat → ℝ) (bf : Nat → Bool) :
    ∃ n, Seg kernel Assumptions.all L g n 4101
    ((3235, .bits 32 m) ::
     (3080, .bits 32 (i32 (-1))) ::
     (3240, if mkeep0 0 m = true then bv32 bf sc 0
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
     (7961, .pair
       (if bf 64 = true then .float .f32 (sc 64) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 65 = true then .float .f32 (sc 65) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7963, .pair
       (if bf 66 = true then .float .f32 (sc 66) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 67 = true then .float .f32 (sc 67) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7965, .pair
       (if bf 68 = true then .float .f32 (sc 68) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 69 = true then .float .f32 (sc 69) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7967, .pair
       (if bf 70 = true then .float .f32 (sc 70) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 71 = true then .float .f32 (sc 71) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7969, .pair
       (if bf 72 = true then .float .f32 (sc 72) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 73 = true then .float .f32 (sc 73) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7971, .pair
       (if bf 74 = true then .float .f32 (sc 74) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 75 = true then .float .f32 (sc 75) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7973, .pair
       (if bf 76 = true then .float .f32 (sc 76) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 77 = true then .float .f32 (sc 77) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7975, .pair
       (if bf 78 = true then .float .f32 (sc 78) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 79 = true then .float .f32 (sc 79) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7977, .pair
       (if bf 80 = true then .float .f32 (sc 80) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 81 = true then .float .f32 (sc 81) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7979, .pair
       (if bf 82 = true then .float .f32 (sc 82) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 83 = true then .float .f32 (sc 83) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7981, .pair
       (if bf 84 = true then .float .f32 (sc 84) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 85 = true then .float .f32 (sc 85) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7983, .pair
       (if bf 86 = true then .float .f32 (sc 86) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 87 = true then .float .f32 (sc 87) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7985, .pair
       (if bf 88 = true then .float .f32 (sc 88) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 89 = true then .float .f32 (sc 89) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7987, .pair
       (if bf 90 = true then .float .f32 (sc 90) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 91 = true then .float .f32 (sc 91) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7989, .pair
       (if bf 92 = true then .float .f32 (sc 92) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 93 = true then .float .f32 (sc 93) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7991, .pair
       (if bf 94 = true then .float .f32 (sc 94) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 95 = true then .float .f32 (sc 95) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7993, .pair
       (if bf 96 = true then .float .f32 (sc 96) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 97 = true then .float .f32 (sc 97) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7995, .pair
       (if bf 98 = true then .float .f32 (sc 98) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 99 = true then .float .f32 (sc 99) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7997, .pair
       (if bf 100 = true then .float .f32 (sc 100) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 101 = true then .float .f32 (sc 101) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7999, .pair
       (if bf 102 = true then .float .f32 (sc 102) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 103 = true then .float .f32 (sc 103) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8001, .pair
       (if bf 104 = true then .float .f32 (sc 104) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 105 = true then .float .f32 (sc 105) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8003, .pair
       (if bf 106 = true then .float .f32 (sc 106) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 107 = true then .float .f32 (sc 107) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8005, .pair
       (if bf 108 = true then .float .f32 (sc 108) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 109 = true then .float .f32 (sc 109) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8007, .pair
       (if bf 110 = true then .float .f32 (sc 110) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 111 = true then .float .f32 (sc 111) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8009, .pair
       (if bf 112 = true then .float .f32 (sc 112) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 113 = true then .float .f32 (sc 113) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8011, .pair
       (if bf 114 = true then .float .f32 (sc 114) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 115 = true then .float .f32 (sc 115) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8013, .pair
       (if bf 116 = true then .float .f32 (sc 116) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 117 = true then .float .f32 (sc 117) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8015, .pair
       (if bf 118 = true then .float .f32 (sc 118) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 119 = true then .float .f32 (sc 119) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8017, .pair
       (if bf 120 = true then .float .f32 (sc 120) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 121 = true then .float .f32 (sc 121) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8019, .pair
       (if bf 122 = true then .float .f32 (sc 122) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 123 = true then .float .f32 (sc 123) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8021, .pair
       (if bf 124 = true then .float .f32 (sc 124) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 125 = true then .float .f32 (sc 125) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8023, .pair
       (if bf 126 = true then .float .f32 (sc 126) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 127 = true then .float .f32 (sc 127) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     [])
    4215
    ((3235, .bits 32 m) ::
     (3080, .bits 32 (i32 (-1))) ::
     (3240, if mkeep0 0 m = true then bv32 bf sc 0
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
     (7993, .pair
       (if bf 96 = true then .float .f32 (sc 96) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 97 = true then .float .f32 (sc 97) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7995, .pair
       (if bf 98 = true then .float .f32 (sc 98) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 99 = true then .float .f32 (sc 99) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7997, .pair
       (if bf 100 = true then .float .f32 (sc 100) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 101 = true then .float .f32 (sc 101) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7999, .pair
       (if bf 102 = true then .float .f32 (sc 102) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 103 = true then .float .f32 (sc 103) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8001, .pair
       (if bf 104 = true then .float .f32 (sc 104) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 105 = true then .float .f32 (sc 105) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8003, .pair
       (if bf 106 = true then .float .f32 (sc 106) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 107 = true then .float .f32 (sc 107) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8005, .pair
       (if bf 108 = true then .float .f32 (sc 108) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 109 = true then .float .f32 (sc 109) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8007, .pair
       (if bf 110 = true then .float .f32 (sc 110) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 111 = true then .float .f32 (sc 111) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8009, .pair
       (if bf 112 = true then .float .f32 (sc 112) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 113 = true then .float .f32 (sc 113) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8011, .pair
       (if bf 114 = true then .float .f32 (sc 114) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 115 = true then .float .f32 (sc 115) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8013, .pair
       (if bf 116 = true then .float .f32 (sc 116) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 117 = true then .float .f32 (sc 117) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8015, .pair
       (if bf 118 = true then .float .f32 (sc 118) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 119 = true then .float .f32 (sc 119) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8017, .pair
       (if bf 120 = true then .float .f32 (sc 120) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 121 = true then .float .f32 (sc 121) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8019, .pair
       (if bf 122 = true then .float .f32 (sc 122) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 123 = true then .float .f32 (sc 123) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8021, .pair
       (if bf 124 = true then .float .f32 (sc 124) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 125 = true then .float .f32 (sc 125) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (8023, .pair
       (if bf 126 = true then .float .f32 (sc 126) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 127 = true then .float .f32 (sc 127) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     []) := by
  seg_sym using (intro t h; seg_fp h using first | rfl | sym_close)

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
