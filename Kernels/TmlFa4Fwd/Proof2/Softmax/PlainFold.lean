-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Basic.Real.Basic

@[expose] public section

/-! # A plain round's maximum: the code's fold

The `max.f32` tree of a plain round (pcs 6748 to 6876) over the row maximum before the round
(`%r6195`) and the round's 128 scores `x`, with four accumulators as the code computes it (a
three-operand `max` is the maximum of the first two, then the third): `foldPT mr x` when the
maximum before the round is the finite `mr`, `foldPF x` when it is `-∞` (the code's first
`max` then reads `-∞`, which the maximum drops). The terms mirror the code (rule M2), so the
walk's values close by `rfl`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax

noncomputable section

/-- The fold from the finite maximum `mr`. -/
def foldPT (mr : ℝ) (x : Nat → ℝ) : ℝ :=
  let a5318 := max (max mr (x 0)) (x 1)
  let a5321 := max (x 2) (x 3)
  let a5324 := max (x 4) (x 5)
  let a5327 := max (x 6) (x 7)
  let a5330 := max (max a5318 (x 8)) (x 9)
  let a5333 := max (max a5321 (x 10)) (x 11)
  let a5336 := max (max a5324 (x 12)) (x 13)
  let a5339 := max (max a5327 (x 14)) (x 15)
  let a5342 := max (max a5330 (x 16)) (x 17)
  let a5345 := max (max a5333 (x 18)) (x 19)
  let a5348 := max (max a5336 (x 20)) (x 21)
  let a5351 := max (max a5339 (x 22)) (x 23)
  let a5354 := max (max a5342 (x 24)) (x 25)
  let a5357 := max (max a5345 (x 26)) (x 27)
  let a5360 := max (max a5348 (x 28)) (x 29)
  let a5363 := max (max a5351 (x 30)) (x 31)
  let a5366 := max (max a5354 (x 32)) (x 33)
  let a5369 := max (max a5357 (x 34)) (x 35)
  let a5372 := max (max a5360 (x 36)) (x 37)
  let a5375 := max (max a5363 (x 38)) (x 39)
  let a5378 := max (max a5366 (x 40)) (x 41)
  let a5381 := max (max a5369 (x 42)) (x 43)
  let a5384 := max (max a5372 (x 44)) (x 45)
  let a5387 := max (max a5375 (x 46)) (x 47)
  let a5390 := max (max a5378 (x 48)) (x 49)
  let a5393 := max (max a5381 (x 50)) (x 51)
  let a5396 := max (max a5384 (x 52)) (x 53)
  let a5399 := max (max a5387 (x 54)) (x 55)
  let a5402 := max (max a5390 (x 56)) (x 57)
  let a5405 := max (max a5393 (x 58)) (x 59)
  let a5408 := max (max a5396 (x 60)) (x 61)
  let a5411 := max (max a5399 (x 62)) (x 63)
  let a5414 := max (max a5402 (x 64)) (x 65)
  let a5417 := max (max a5405 (x 66)) (x 67)
  let a5420 := max (max a5408 (x 68)) (x 69)
  let a5423 := max (max a5411 (x 70)) (x 71)
  let a5426 := max (max a5414 (x 72)) (x 73)
  let a5429 := max (max a5417 (x 74)) (x 75)
  let a5432 := max (max a5420 (x 76)) (x 77)
  let a5435 := max (max a5423 (x 78)) (x 79)
  let a5438 := max (max a5426 (x 80)) (x 81)
  let a5441 := max (max a5429 (x 82)) (x 83)
  let a5444 := max (max a5432 (x 84)) (x 85)
  let a5447 := max (max a5435 (x 86)) (x 87)
  let a5450 := max (max a5438 (x 88)) (x 89)
  let a5453 := max (max a5441 (x 90)) (x 91)
  let a5456 := max (max a5444 (x 92)) (x 93)
  let a5459 := max (max a5447 (x 94)) (x 95)
  let a5462 := max (max a5450 (x 96)) (x 97)
  let a5465 := max (max a5453 (x 98)) (x 99)
  let a5468 := max (max a5456 (x 100)) (x 101)
  let a5471 := max (max a5459 (x 102)) (x 103)
  let a5474 := max (max a5462 (x 104)) (x 105)
  let a5477 := max (max a5465 (x 106)) (x 107)
  let a5480 := max (max a5468 (x 108)) (x 109)
  let a5483 := max (max a5471 (x 110)) (x 111)
  let a5486 := max (max a5474 (x 112)) (x 113)
  let a5489 := max (max a5477 (x 114)) (x 115)
  let a5492 := max (max a5480 (x 116)) (x 117)
  let a5495 := max (max a5483 (x 118)) (x 119)
  let a5498 := max (max a5486 (x 120)) (x 121)
  let a5501 := max (max a5489 (x 122)) (x 123)
  let a5504 := max (max a5492 (x 124)) (x 125)
  let a5507 := max (max a5495 (x 126)) (x 127)
  let a5508 := max a5498 a5501
  let a5509 := max (max a5508 a5504) a5507
  a5509

/-- The fold from `-∞`. -/
def foldPF (x : Nat → ℝ) : ℝ :=
  let a5318 := max (x 0) (x 1)
  let a5321 := max (x 2) (x 3)
  let a5324 := max (x 4) (x 5)
  let a5327 := max (x 6) (x 7)
  let a5330 := max (max a5318 (x 8)) (x 9)
  let a5333 := max (max a5321 (x 10)) (x 11)
  let a5336 := max (max a5324 (x 12)) (x 13)
  let a5339 := max (max a5327 (x 14)) (x 15)
  let a5342 := max (max a5330 (x 16)) (x 17)
  let a5345 := max (max a5333 (x 18)) (x 19)
  let a5348 := max (max a5336 (x 20)) (x 21)
  let a5351 := max (max a5339 (x 22)) (x 23)
  let a5354 := max (max a5342 (x 24)) (x 25)
  let a5357 := max (max a5345 (x 26)) (x 27)
  let a5360 := max (max a5348 (x 28)) (x 29)
  let a5363 := max (max a5351 (x 30)) (x 31)
  let a5366 := max (max a5354 (x 32)) (x 33)
  let a5369 := max (max a5357 (x 34)) (x 35)
  let a5372 := max (max a5360 (x 36)) (x 37)
  let a5375 := max (max a5363 (x 38)) (x 39)
  let a5378 := max (max a5366 (x 40)) (x 41)
  let a5381 := max (max a5369 (x 42)) (x 43)
  let a5384 := max (max a5372 (x 44)) (x 45)
  let a5387 := max (max a5375 (x 46)) (x 47)
  let a5390 := max (max a5378 (x 48)) (x 49)
  let a5393 := max (max a5381 (x 50)) (x 51)
  let a5396 := max (max a5384 (x 52)) (x 53)
  let a5399 := max (max a5387 (x 54)) (x 55)
  let a5402 := max (max a5390 (x 56)) (x 57)
  let a5405 := max (max a5393 (x 58)) (x 59)
  let a5408 := max (max a5396 (x 60)) (x 61)
  let a5411 := max (max a5399 (x 62)) (x 63)
  let a5414 := max (max a5402 (x 64)) (x 65)
  let a5417 := max (max a5405 (x 66)) (x 67)
  let a5420 := max (max a5408 (x 68)) (x 69)
  let a5423 := max (max a5411 (x 70)) (x 71)
  let a5426 := max (max a5414 (x 72)) (x 73)
  let a5429 := max (max a5417 (x 74)) (x 75)
  let a5432 := max (max a5420 (x 76)) (x 77)
  let a5435 := max (max a5423 (x 78)) (x 79)
  let a5438 := max (max a5426 (x 80)) (x 81)
  let a5441 := max (max a5429 (x 82)) (x 83)
  let a5444 := max (max a5432 (x 84)) (x 85)
  let a5447 := max (max a5435 (x 86)) (x 87)
  let a5450 := max (max a5438 (x 88)) (x 89)
  let a5453 := max (max a5441 (x 90)) (x 91)
  let a5456 := max (max a5444 (x 92)) (x 93)
  let a5459 := max (max a5447 (x 94)) (x 95)
  let a5462 := max (max a5450 (x 96)) (x 97)
  let a5465 := max (max a5453 (x 98)) (x 99)
  let a5468 := max (max a5456 (x 100)) (x 101)
  let a5471 := max (max a5459 (x 102)) (x 103)
  let a5474 := max (max a5462 (x 104)) (x 105)
  let a5477 := max (max a5465 (x 106)) (x 107)
  let a5480 := max (max a5468 (x 108)) (x 109)
  let a5483 := max (max a5471 (x 110)) (x 111)
  let a5486 := max (max a5474 (x 112)) (x 113)
  let a5489 := max (max a5477 (x 114)) (x 115)
  let a5492 := max (max a5480 (x 116)) (x 117)
  let a5495 := max (max a5483 (x 118)) (x 119)
  let a5498 := max (max a5486 (x 120)) (x 121)
  let a5501 := max (max a5489 (x 122)) (x 123)
  let a5504 := max (max a5492 (x 124)) (x 125)
  let a5507 := max (max a5495 (x 126)) (x 127)
  let a5508 := max a5498 a5501
  let a5509 := max (max a5508 a5504) a5507
  a5509
/-- A plain round's row sum as the code adds it (pcs 7466 to 7598): two lanes, the first from
`x0` (the rescaled sum before the round), the second from 0, each with four accumulators over
the 128 weights `w` in the reduction's order, then the two lanes. -/
def rowSumT (x0 : ℝ) (w : Nat → ℝ) : ℝ :=
  x0 + (w 0) + (w 8) + (w 16) + (w 24) + (w 32) + (w 40) + (w 48) + (w 56) + (w 64) + (w 72) +
    (w 80) + (w 88) + (w 96) + (w 104) + (w 112) + (w 120) + (w 2 + (w 10) + (w 18) + (w 26) +
    (w 34) + (w 42) + (w 50) + (w 58) + (w 66) + (w 74) + (w 82) + (w 90) + (w 98) + (w 106) +
    (w 114) + (w 122)) + (w 4 + (w 12) + (w 20) + (w 28) + (w 36) + (w 44) + (w 52) + (w 60) +
    (w 68) + (w 76) + (w 84) + (w 92) + (w 100) + (w 108) + (w 116) + (w 124) + (w 6 + (w 14) +
    (w 22) + (w 30) + (w 38) + (w 46) + (w 54) + (w 62) + (w 70) + (w 78) + (w 86) + (w 94) + (w
    102) + (w 110) + (w 118) + (w 126))) + (0 + (w 1) + (w 9) + (w 17) + (w 25) + (w 33) + (w
    41) + (w 49) + (w 57) + (w 65) + (w 73) + (w 81) + (w 89) + (w 97) + (w 105) + (w 113) + (w
    121) + (w 3 + (w 11) + (w 19) + (w 27) + (w 35) + (w 43) + (w 51) + (w 59) + (w 67) + (w 75)
    + (w 83) + (w 91) + (w 99) + (w 107) + (w 115) + (w 123)) + (w 5 + (w 13) + (w 21) + (w 29)
    + (w 37) + (w 45) + (w 53) + (w 61) + (w 69) + (w 77) + (w 85) + (w 93) + (w 101) + (w 109)
    + (w 117) + (w 125) + (w 7 + (w 15) + (w 23) + (w 31) + (w 39) + (w 47) + (w 55) + (w 63) +
    (w 71) + (w 79) + (w 87) + (w 95) + (w 103) + (w 111) + (w 119) + (w 127))))

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
