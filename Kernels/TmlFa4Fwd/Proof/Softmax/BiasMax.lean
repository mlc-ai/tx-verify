-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.BiasFold
public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.MaxB
public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
import Lemmas.Flow.Step.RuleStep

@[expose] public section

/-! # The bias round's maximum

The `max.f32` tree of the bias round (pcs 5536 to 5665, `Gen.maxB_run`): from the maximum before
the round `x0` and the 128 products' readings `e`, the maximum is `erealValue .f32 (foldB x0 e)`
(`maxB_value`), `foldB` the code's tree (four accumulators; a three-operand `max` is the maximum
of the first two, then the third). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000

theorem maxE_er2 (x y : EReal) :
    okVal (.bits 32 0) (maxE [erealValue .f32 x, erealValue .f32 y]) =
      erealValue .f32 (max x y) := by
  unfold maxE
  simp only [idealMax, readEReal_erealValue_f32, bindRead, pure, Except.pure]
  rfl

theorem maxE_er3 (x y z : EReal) :
    okVal (.bits 32 0) (maxE [erealValue .f32 x, erealValue .f32 y, erealValue .f32 z]) =
      erealValue .f32 (max (max x y) z) := by
  unfold maxE
  simp only [idealMax, readEReal_erealValue_f32, bindRead, pure, Except.pure]
  rfl

theorem split_pair (a b : Value) : splitValue 64 (.pair a b) = (a, b) := rfl

/-- **The bias round's maximum** at pc 5666 from the values at pc 5536. -/
theorem maxB_value (V : Nat → Value) (x0 : EReal) (e : Nat → EReal)
    (h0 : V 7251 = erealValue .f32 x0)
    (hP : ∀ j < 64, V (8317 + 2 * j) =
      .pair (erealValue .f32 (e (2 * j))) (erealValue .f32 (e (2 * j + 1)))) :
    Gen.maxB_v5665 V = erealValue .f32 (foldB x0 e) := by
  have p0 : V 8317 =
      .pair (erealValue .f32 (e 0)) (erealValue .f32 (e 1)) := hP 0 (by decide)
  have p1 : V 8319 =
      .pair (erealValue .f32 (e 2)) (erealValue .f32 (e 3)) := hP 1 (by decide)
  have p2 : V 8321 =
      .pair (erealValue .f32 (e 4)) (erealValue .f32 (e 5)) := hP 2 (by decide)
  have p3 : V 8323 =
      .pair (erealValue .f32 (e 6)) (erealValue .f32 (e 7)) := hP 3 (by decide)
  have p4 : V 8325 =
      .pair (erealValue .f32 (e 8)) (erealValue .f32 (e 9)) := hP 4 (by decide)
  have p5 : V 8327 =
      .pair (erealValue .f32 (e 10)) (erealValue .f32 (e 11)) := hP 5 (by decide)
  have p6 : V 8329 =
      .pair (erealValue .f32 (e 12)) (erealValue .f32 (e 13)) := hP 6 (by decide)
  have p7 : V 8331 =
      .pair (erealValue .f32 (e 14)) (erealValue .f32 (e 15)) := hP 7 (by decide)
  have p8 : V 8333 =
      .pair (erealValue .f32 (e 16)) (erealValue .f32 (e 17)) := hP 8 (by decide)
  have p9 : V 8335 =
      .pair (erealValue .f32 (e 18)) (erealValue .f32 (e 19)) := hP 9 (by decide)
  have p10 : V 8337 =
      .pair (erealValue .f32 (e 20)) (erealValue .f32 (e 21)) := hP 10 (by decide)
  have p11 : V 8339 =
      .pair (erealValue .f32 (e 22)) (erealValue .f32 (e 23)) := hP 11 (by decide)
  have p12 : V 8341 =
      .pair (erealValue .f32 (e 24)) (erealValue .f32 (e 25)) := hP 12 (by decide)
  have p13 : V 8343 =
      .pair (erealValue .f32 (e 26)) (erealValue .f32 (e 27)) := hP 13 (by decide)
  have p14 : V 8345 =
      .pair (erealValue .f32 (e 28)) (erealValue .f32 (e 29)) := hP 14 (by decide)
  have p15 : V 8347 =
      .pair (erealValue .f32 (e 30)) (erealValue .f32 (e 31)) := hP 15 (by decide)
  have p16 : V 8349 =
      .pair (erealValue .f32 (e 32)) (erealValue .f32 (e 33)) := hP 16 (by decide)
  have p17 : V 8351 =
      .pair (erealValue .f32 (e 34)) (erealValue .f32 (e 35)) := hP 17 (by decide)
  have p18 : V 8353 =
      .pair (erealValue .f32 (e 36)) (erealValue .f32 (e 37)) := hP 18 (by decide)
  have p19 : V 8355 =
      .pair (erealValue .f32 (e 38)) (erealValue .f32 (e 39)) := hP 19 (by decide)
  have p20 : V 8357 =
      .pair (erealValue .f32 (e 40)) (erealValue .f32 (e 41)) := hP 20 (by decide)
  have p21 : V 8359 =
      .pair (erealValue .f32 (e 42)) (erealValue .f32 (e 43)) := hP 21 (by decide)
  have p22 : V 8361 =
      .pair (erealValue .f32 (e 44)) (erealValue .f32 (e 45)) := hP 22 (by decide)
  have p23 : V 8363 =
      .pair (erealValue .f32 (e 46)) (erealValue .f32 (e 47)) := hP 23 (by decide)
  have p24 : V 8365 =
      .pair (erealValue .f32 (e 48)) (erealValue .f32 (e 49)) := hP 24 (by decide)
  have p25 : V 8367 =
      .pair (erealValue .f32 (e 50)) (erealValue .f32 (e 51)) := hP 25 (by decide)
  have p26 : V 8369 =
      .pair (erealValue .f32 (e 52)) (erealValue .f32 (e 53)) := hP 26 (by decide)
  have p27 : V 8371 =
      .pair (erealValue .f32 (e 54)) (erealValue .f32 (e 55)) := hP 27 (by decide)
  have p28 : V 8373 =
      .pair (erealValue .f32 (e 56)) (erealValue .f32 (e 57)) := hP 28 (by decide)
  have p29 : V 8375 =
      .pair (erealValue .f32 (e 58)) (erealValue .f32 (e 59)) := hP 29 (by decide)
  have p30 : V 8377 =
      .pair (erealValue .f32 (e 60)) (erealValue .f32 (e 61)) := hP 30 (by decide)
  have p31 : V 8379 =
      .pair (erealValue .f32 (e 62)) (erealValue .f32 (e 63)) := hP 31 (by decide)
  have p32 : V 8381 =
      .pair (erealValue .f32 (e 64)) (erealValue .f32 (e 65)) := hP 32 (by decide)
  have p33 : V 8383 =
      .pair (erealValue .f32 (e 66)) (erealValue .f32 (e 67)) := hP 33 (by decide)
  have p34 : V 8385 =
      .pair (erealValue .f32 (e 68)) (erealValue .f32 (e 69)) := hP 34 (by decide)
  have p35 : V 8387 =
      .pair (erealValue .f32 (e 70)) (erealValue .f32 (e 71)) := hP 35 (by decide)
  have p36 : V 8389 =
      .pair (erealValue .f32 (e 72)) (erealValue .f32 (e 73)) := hP 36 (by decide)
  have p37 : V 8391 =
      .pair (erealValue .f32 (e 74)) (erealValue .f32 (e 75)) := hP 37 (by decide)
  have p38 : V 8393 =
      .pair (erealValue .f32 (e 76)) (erealValue .f32 (e 77)) := hP 38 (by decide)
  have p39 : V 8395 =
      .pair (erealValue .f32 (e 78)) (erealValue .f32 (e 79)) := hP 39 (by decide)
  have p40 : V 8397 =
      .pair (erealValue .f32 (e 80)) (erealValue .f32 (e 81)) := hP 40 (by decide)
  have p41 : V 8399 =
      .pair (erealValue .f32 (e 82)) (erealValue .f32 (e 83)) := hP 41 (by decide)
  have p42 : V 8401 =
      .pair (erealValue .f32 (e 84)) (erealValue .f32 (e 85)) := hP 42 (by decide)
  have p43 : V 8403 =
      .pair (erealValue .f32 (e 86)) (erealValue .f32 (e 87)) := hP 43 (by decide)
  have p44 : V 8405 =
      .pair (erealValue .f32 (e 88)) (erealValue .f32 (e 89)) := hP 44 (by decide)
  have p45 : V 8407 =
      .pair (erealValue .f32 (e 90)) (erealValue .f32 (e 91)) := hP 45 (by decide)
  have p46 : V 8409 =
      .pair (erealValue .f32 (e 92)) (erealValue .f32 (e 93)) := hP 46 (by decide)
  have p47 : V 8411 =
      .pair (erealValue .f32 (e 94)) (erealValue .f32 (e 95)) := hP 47 (by decide)
  have p48 : V 8413 =
      .pair (erealValue .f32 (e 96)) (erealValue .f32 (e 97)) := hP 48 (by decide)
  have p49 : V 8415 =
      .pair (erealValue .f32 (e 98)) (erealValue .f32 (e 99)) := hP 49 (by decide)
  have p50 : V 8417 =
      .pair (erealValue .f32 (e 100)) (erealValue .f32 (e 101)) := hP 50 (by decide)
  have p51 : V 8419 =
      .pair (erealValue .f32 (e 102)) (erealValue .f32 (e 103)) := hP 51 (by decide)
  have p52 : V 8421 =
      .pair (erealValue .f32 (e 104)) (erealValue .f32 (e 105)) := hP 52 (by decide)
  have p53 : V 8423 =
      .pair (erealValue .f32 (e 106)) (erealValue .f32 (e 107)) := hP 53 (by decide)
  have p54 : V 8425 =
      .pair (erealValue .f32 (e 108)) (erealValue .f32 (e 109)) := hP 54 (by decide)
  have p55 : V 8427 =
      .pair (erealValue .f32 (e 110)) (erealValue .f32 (e 111)) := hP 55 (by decide)
  have p56 : V 8429 =
      .pair (erealValue .f32 (e 112)) (erealValue .f32 (e 113)) := hP 56 (by decide)
  have p57 : V 8431 =
      .pair (erealValue .f32 (e 114)) (erealValue .f32 (e 115)) := hP 57 (by decide)
  have p58 : V 8433 =
      .pair (erealValue .f32 (e 116)) (erealValue .f32 (e 117)) := hP 58 (by decide)
  have p59 : V 8435 =
      .pair (erealValue .f32 (e 118)) (erealValue .f32 (e 119)) := hP 59 (by decide)
  have p60 : V 8437 =
      .pair (erealValue .f32 (e 120)) (erealValue .f32 (e 121)) := hP 60 (by decide)
  have p61 : V 8439 =
      .pair (erealValue .f32 (e 122)) (erealValue .f32 (e 123)) := hP 61 (by decide)
  have p62 : V 8441 =
      .pair (erealValue .f32 (e 124)) (erealValue .f32 (e 125)) := hP 62 (by decide)
  have p63 : V 8443 =
      .pair (erealValue .f32 (e 126)) (erealValue .f32 (e 127)) := hP 63 (by decide)
  simp only [Gen.maxB_v5536_0, Gen.maxB_v5536_1, Gen.maxB_v5537, Gen.maxB_v5538_0,
    Gen.maxB_v5538_1, Gen.maxB_v5539, Gen.maxB_v5540_0, Gen.maxB_v5540_1, Gen.maxB_v5541,
    Gen.maxB_v5542_0, Gen.maxB_v5542_1, Gen.maxB_v5543, Gen.maxB_v5544_0, Gen.maxB_v5544_1,
    Gen.maxB_v5545, Gen.maxB_v5546_0, Gen.maxB_v5546_1, Gen.maxB_v5547, Gen.maxB_v5548_0,
    Gen.maxB_v5548_1, Gen.maxB_v5549, Gen.maxB_v5550_0, Gen.maxB_v5550_1, Gen.maxB_v5551,
    Gen.maxB_v5552_0, Gen.maxB_v5552_1, Gen.maxB_v5553, Gen.maxB_v5554_0, Gen.maxB_v5554_1,
    Gen.maxB_v5555, Gen.maxB_v5556_0, Gen.maxB_v5556_1, Gen.maxB_v5557, Gen.maxB_v5558_0,
    Gen.maxB_v5558_1, Gen.maxB_v5559, Gen.maxB_v5560_0, Gen.maxB_v5560_1, Gen.maxB_v5561,
    Gen.maxB_v5562_0, Gen.maxB_v5562_1, Gen.maxB_v5563, Gen.maxB_v5564_0, Gen.maxB_v5564_1,
    Gen.maxB_v5565, Gen.maxB_v5566_0, Gen.maxB_v5566_1, Gen.maxB_v5567, Gen.maxB_v5568_0,
    Gen.maxB_v5568_1, Gen.maxB_v5569, Gen.maxB_v5570_0, Gen.maxB_v5570_1, Gen.maxB_v5571,
    Gen.maxB_v5572_0, Gen.maxB_v5572_1, Gen.maxB_v5573, Gen.maxB_v5574_0, Gen.maxB_v5574_1,
    Gen.maxB_v5575, Gen.maxB_v5576_0, Gen.maxB_v5576_1, Gen.maxB_v5577, Gen.maxB_v5578_0,
    Gen.maxB_v5578_1, Gen.maxB_v5579, Gen.maxB_v5580_0, Gen.maxB_v5580_1, Gen.maxB_v5581,
    Gen.maxB_v5582_0, Gen.maxB_v5582_1, Gen.maxB_v5583, Gen.maxB_v5584_0, Gen.maxB_v5584_1,
    Gen.maxB_v5585, Gen.maxB_v5586_0, Gen.maxB_v5586_1, Gen.maxB_v5587, Gen.maxB_v5588_0,
    Gen.maxB_v5588_1, Gen.maxB_v5589, Gen.maxB_v5590_0, Gen.maxB_v5590_1, Gen.maxB_v5591,
    Gen.maxB_v5592_0, Gen.maxB_v5592_1, Gen.maxB_v5593, Gen.maxB_v5594_0, Gen.maxB_v5594_1,
    Gen.maxB_v5595, Gen.maxB_v5596_0, Gen.maxB_v5596_1, Gen.maxB_v5597, Gen.maxB_v5598_0,
    Gen.maxB_v5598_1, Gen.maxB_v5599, Gen.maxB_v5600_0, Gen.maxB_v5600_1, Gen.maxB_v5601,
    Gen.maxB_v5602_0, Gen.maxB_v5602_1, Gen.maxB_v5603, Gen.maxB_v5604_0, Gen.maxB_v5604_1,
    Gen.maxB_v5605, Gen.maxB_v5606_0, Gen.maxB_v5606_1, Gen.maxB_v5607, Gen.maxB_v5608_0,
    Gen.maxB_v5608_1, Gen.maxB_v5609, Gen.maxB_v5610_0, Gen.maxB_v5610_1, Gen.maxB_v5611,
    Gen.maxB_v5612_0, Gen.maxB_v5612_1, Gen.maxB_v5613, Gen.maxB_v5614_0, Gen.maxB_v5614_1,
    Gen.maxB_v5615, Gen.maxB_v5616_0, Gen.maxB_v5616_1, Gen.maxB_v5617, Gen.maxB_v5618_0,
    Gen.maxB_v5618_1, Gen.maxB_v5619, Gen.maxB_v5620_0, Gen.maxB_v5620_1, Gen.maxB_v5621,
    Gen.maxB_v5622_0, Gen.maxB_v5622_1, Gen.maxB_v5623, Gen.maxB_v5624_0, Gen.maxB_v5624_1,
    Gen.maxB_v5625, Gen.maxB_v5626_0, Gen.maxB_v5626_1, Gen.maxB_v5627, Gen.maxB_v5628_0,
    Gen.maxB_v5628_1, Gen.maxB_v5629, Gen.maxB_v5630_0, Gen.maxB_v5630_1, Gen.maxB_v5631,
    Gen.maxB_v5632_0, Gen.maxB_v5632_1, Gen.maxB_v5633, Gen.maxB_v5634_0, Gen.maxB_v5634_1,
    Gen.maxB_v5635, Gen.maxB_v5636_0, Gen.maxB_v5636_1, Gen.maxB_v5637, Gen.maxB_v5638_0,
    Gen.maxB_v5638_1, Gen.maxB_v5639, Gen.maxB_v5640_0, Gen.maxB_v5640_1, Gen.maxB_v5641,
    Gen.maxB_v5642_0, Gen.maxB_v5642_1, Gen.maxB_v5643, Gen.maxB_v5644_0, Gen.maxB_v5644_1,
    Gen.maxB_v5645, Gen.maxB_v5646_0, Gen.maxB_v5646_1, Gen.maxB_v5647, Gen.maxB_v5648_0,
    Gen.maxB_v5648_1, Gen.maxB_v5649, Gen.maxB_v5650_0, Gen.maxB_v5650_1, Gen.maxB_v5651,
    Gen.maxB_v5652_0, Gen.maxB_v5652_1, Gen.maxB_v5653, Gen.maxB_v5654_0, Gen.maxB_v5654_1,
    Gen.maxB_v5655, Gen.maxB_v5656_0, Gen.maxB_v5656_1, Gen.maxB_v5657, Gen.maxB_v5658_0,
    Gen.maxB_v5658_1, Gen.maxB_v5659, Gen.maxB_v5660_0, Gen.maxB_v5660_1, Gen.maxB_v5661,
    Gen.maxB_v5662_0, Gen.maxB_v5662_1, Gen.maxB_v5663, Gen.maxB_v5664, Gen.maxB_v5665,
    p0, p1, p2, p3, p4,
    p5, p6, p7, p8, p9,
    p10, p11, p12, p13, p14,
    p15, p16, p17, p18, p19,
    p20, p21, p22, p23, p24,
    p25, p26, p27, p28, p29,
    p30, p31, p32, p33, p34,
    p35, p36, p37, p38, p39,
    p40, p41, p42, p43, p44,
    p45, p46, p47, p48, p49,
    p50, p51, p52, p53, p54,
    p55, p56, p57, p58, p59,
    p60, p61, p62, p63, h0, split_pair,
    maxE_er2, maxE_er3]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
