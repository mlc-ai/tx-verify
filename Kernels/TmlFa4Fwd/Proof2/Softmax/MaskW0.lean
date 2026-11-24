-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.MaskSeg

@[expose] public section

/-! # The masked maximum's selects: mask word 0

The first 32 selects of the first round's causal mask (pcs 3872 to 3987): from the mask count `m`
(`%r2175`) and the bias-product pairs 7897 to 7927, each element is its bias product or `-∞` as the
code's mask word `mword 0 m` keeps it. One `Seg` per mask word, so the four check in parallel; the
piece also carries the elements selected before it and the bias-product pairs of the later words, so
that its end facts are the next piece's start facts (`MaskChain.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- **The selects of mask word 0.** -/
theorem mask_word0 (L : Launch) (g : Nat) (m : BitVec 64) (sc : Nat → ℝ) (bf : Nat → Bool) :
    ∃ n, Seg kernel Assumptions.all L g n 3872
    ((3235, .bits 32 m) ::
     (7897, .pair
       (if bf 0 = true then .float .f32 (sc 0) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 1 = true then .float .f32 (sc 1) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7899, .pair
       (if bf 2 = true then .float .f32 (sc 2) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 3 = true then .float .f32 (sc 3) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7901, .pair
       (if bf 4 = true then .float .f32 (sc 4) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 5 = true then .float .f32 (sc 5) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7903, .pair
       (if bf 6 = true then .float .f32 (sc 6) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 7 = true then .float .f32 (sc 7) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7905, .pair
       (if bf 8 = true then .float .f32 (sc 8) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 9 = true then .float .f32 (sc 9) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7907, .pair
       (if bf 10 = true then .float .f32 (sc 10) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 11 = true then .float .f32 (sc 11) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7909, .pair
       (if bf 12 = true then .float .f32 (sc 12) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 13 = true then .float .f32 (sc 13) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7911, .pair
       (if bf 14 = true then .float .f32 (sc 14) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 15 = true then .float .f32 (sc 15) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7913, .pair
       (if bf 16 = true then .float .f32 (sc 16) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 17 = true then .float .f32 (sc 17) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7915, .pair
       (if bf 18 = true then .float .f32 (sc 18) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 19 = true then .float .f32 (sc 19) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7917, .pair
       (if bf 20 = true then .float .f32 (sc 20) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 21 = true then .float .f32 (sc 21) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7919, .pair
       (if bf 22 = true then .float .f32 (sc 22) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 23 = true then .float .f32 (sc 23) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7921, .pair
       (if bf 24 = true then .float .f32 (sc 24) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 25 = true then .float .f32 (sc 25) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7923, .pair
       (if bf 26 = true then .float .f32 (sc 26) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 27 = true then .float .f32 (sc 27) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7925, .pair
       (if bf 28 = true then .float .f32 (sc 28) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 29 = true then .float .f32 (sc 29) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7927, .pair
       (if bf 30 = true then .float .f32 (sc 30) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 31 = true then .float .f32 (sc 31) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7929, .pair
       (if bf 32 = true then .float .f32 (sc 32) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 33 = true then .float .f32 (sc 33) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7931, .pair
       (if bf 34 = true then .float .f32 (sc 34) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 35 = true then .float .f32 (sc 35) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7933, .pair
       (if bf 36 = true then .float .f32 (sc 36) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 37 = true then .float .f32 (sc 37) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7935, .pair
       (if bf 38 = true then .float .f32 (sc 38) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 39 = true then .float .f32 (sc 39) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7937, .pair
       (if bf 40 = true then .float .f32 (sc 40) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 41 = true then .float .f32 (sc 41) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7939, .pair
       (if bf 42 = true then .float .f32 (sc 42) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 43 = true then .float .f32 (sc 43) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7941, .pair
       (if bf 44 = true then .float .f32 (sc 44) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 45 = true then .float .f32 (sc 45) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7943, .pair
       (if bf 46 = true then .float .f32 (sc 46) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 47 = true then .float .f32 (sc 47) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7945, .pair
       (if bf 48 = true then .float .f32 (sc 48) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 49 = true then .float .f32 (sc 49) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7947, .pair
       (if bf 50 = true then .float .f32 (sc 50) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 51 = true then .float .f32 (sc 51) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7949, .pair
       (if bf 52 = true then .float .f32 (sc 52) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 53 = true then .float .f32 (sc 53) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7951, .pair
       (if bf 54 = true then .float .f32 (sc 54) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 55 = true then .float .f32 (sc 55) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7953, .pair
       (if bf 56 = true then .float .f32 (sc 56) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 57 = true then .float .f32 (sc 57) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7955, .pair
       (if bf 58 = true then .float .f32 (sc 58) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 59 = true then .float .f32 (sc 59) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7957, .pair
       (if bf 60 = true then .float .f32 (sc 60) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 61 = true then .float .f32 (sc 61) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7959, .pair
       (if bf 62 = true then .float .f32 (sc 62) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 63 = true then .float .f32 (sc 63) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
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
    3987
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
     (7929, .pair
       (if bf 32 = true then .float .f32 (sc 32) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 33 = true then .float .f32 (sc 33) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7931, .pair
       (if bf 34 = true then .float .f32 (sc 34) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 35 = true then .float .f32 (sc 35) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7933, .pair
       (if bf 36 = true then .float .f32 (sc 36) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 37 = true then .float .f32 (sc 37) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7935, .pair
       (if bf 38 = true then .float .f32 (sc 38) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 39 = true then .float .f32 (sc 39) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7937, .pair
       (if bf 40 = true then .float .f32 (sc 40) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 41 = true then .float .f32 (sc 41) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7939, .pair
       (if bf 42 = true then .float .f32 (sc 42) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 43 = true then .float .f32 (sc 43) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7941, .pair
       (if bf 44 = true then .float .f32 (sc 44) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 45 = true then .float .f32 (sc 45) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7943, .pair
       (if bf 46 = true then .float .f32 (sc 46) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 47 = true then .float .f32 (sc 47) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7945, .pair
       (if bf 48 = true then .float .f32 (sc 48) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 49 = true then .float .f32 (sc 49) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7947, .pair
       (if bf 50 = true then .float .f32 (sc 50) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 51 = true then .float .f32 (sc 51) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7949, .pair
       (if bf 52 = true then .float .f32 (sc 52) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 53 = true then .float .f32 (sc 53) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7951, .pair
       (if bf 54 = true then .float .f32 (sc 54) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 55 = true then .float .f32 (sc 55) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7953, .pair
       (if bf 56 = true then .float .f32 (sc 56) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 57 = true then .float .f32 (sc 57) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7955, .pair
       (if bf 58 = true then .float .f32 (sc 58) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 59 = true then .float .f32 (sc 59) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7957, .pair
       (if bf 60 = true then .float .f32 (sc 60) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 61 = true then .float .f32 (sc 61) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
     (7959, .pair
       (if bf 62 = true then .float .f32 (sc 62) else .bits 32 (BitVec.ofNat 64 4286578688))
       (if bf 63 = true then .float .f32 (sc 63) else .bits 32 (BitVec.ofNat 64 4286578688))) ::
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
     []) := by
  seg_sym using (intro t h; seg_fp h using first | rfl | sym_close)

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
