-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Gen.MaxP
public import Kernels.TmlFa4Fwd.Proof2.Softmax.BiasMax
public import Kernels.TmlFa4Fwd.Proof2.Softmax.PlainFold

@[expose] public section

/-! # A plain round's maximum: the run's value

The `max.f32` tree of a plain round (pcs 6747 to 6876, `Gen.maxP_run`) has the shape of the bias
round's (`foldB`): from the maximum before the round `x0` and the 128 scores' readings `e`, the
maximum is `erealValue .f32 (foldB x0 e)` (`maxP_value`). On real scores it is the code's real
fold: `foldPT mr x` from the finite maximum `mr` (`foldB_coe`), `foldPF x` from `-∞`
(`foldB_bot`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000

/-- **A plain round's maximum** at pc 6877 from the values at pc 6747. -/
theorem maxP_value (V : Nat → Value) (x0 : EReal) (e : Nat → EReal)
    (h0 : V 7255 = erealValue .f32 x0)
    (hP : ∀ j < 64, V (pairReg .plain j) =
      .pair (erealValue .f32 (e (2 * j))) (erealValue .f32 (e (2 * j + 1)))) :
    Gen.maxP_v6876 V = erealValue .f32 (foldB x0 e) := by
  have p0 : V 8690 =
      .pair (erealValue .f32 (e 0)) (erealValue .f32 (e 1)) := hP 0 (by decide)
  have p1 : V 8689 =
      .pair (erealValue .f32 (e 2)) (erealValue .f32 (e 3)) := hP 1 (by decide)
  have p2 : V 8688 =
      .pair (erealValue .f32 (e 4)) (erealValue .f32 (e 5)) := hP 2 (by decide)
  have p3 : V 8687 =
      .pair (erealValue .f32 (e 6)) (erealValue .f32 (e 7)) := hP 3 (by decide)
  have p4 : V 7431 =
      .pair (erealValue .f32 (e 8)) (erealValue .f32 (e 9)) := hP 4 (by decide)
  have p5 : V 7432 =
      .pair (erealValue .f32 (e 10)) (erealValue .f32 (e 11)) := hP 5 (by decide)
  have p6 : V 7433 =
      .pair (erealValue .f32 (e 12)) (erealValue .f32 (e 13)) := hP 6 (by decide)
  have p7 : V 7434 =
      .pair (erealValue .f32 (e 14)) (erealValue .f32 (e 15)) := hP 7 (by decide)
  have p8 : V 7435 =
      .pair (erealValue .f32 (e 16)) (erealValue .f32 (e 17)) := hP 8 (by decide)
  have p9 : V 7436 =
      .pair (erealValue .f32 (e 18)) (erealValue .f32 (e 19)) := hP 9 (by decide)
  have p10 : V 7437 =
      .pair (erealValue .f32 (e 20)) (erealValue .f32 (e 21)) := hP 10 (by decide)
  have p11 : V 7438 =
      .pair (erealValue .f32 (e 22)) (erealValue .f32 (e 23)) := hP 11 (by decide)
  have p12 : V 7439 =
      .pair (erealValue .f32 (e 24)) (erealValue .f32 (e 25)) := hP 12 (by decide)
  have p13 : V 7440 =
      .pair (erealValue .f32 (e 26)) (erealValue .f32 (e 27)) := hP 13 (by decide)
  have p14 : V 7441 =
      .pair (erealValue .f32 (e 28)) (erealValue .f32 (e 29)) := hP 14 (by decide)
  have p15 : V 7442 =
      .pair (erealValue .f32 (e 30)) (erealValue .f32 (e 31)) := hP 15 (by decide)
  have p16 : V 7443 =
      .pair (erealValue .f32 (e 32)) (erealValue .f32 (e 33)) := hP 16 (by decide)
  have p17 : V 7444 =
      .pair (erealValue .f32 (e 34)) (erealValue .f32 (e 35)) := hP 17 (by decide)
  have p18 : V 7445 =
      .pair (erealValue .f32 (e 36)) (erealValue .f32 (e 37)) := hP 18 (by decide)
  have p19 : V 7446 =
      .pair (erealValue .f32 (e 38)) (erealValue .f32 (e 39)) := hP 19 (by decide)
  have p20 : V 7447 =
      .pair (erealValue .f32 (e 40)) (erealValue .f32 (e 41)) := hP 20 (by decide)
  have p21 : V 7448 =
      .pair (erealValue .f32 (e 42)) (erealValue .f32 (e 43)) := hP 21 (by decide)
  have p22 : V 7449 =
      .pair (erealValue .f32 (e 44)) (erealValue .f32 (e 45)) := hP 22 (by decide)
  have p23 : V 7450 =
      .pair (erealValue .f32 (e 46)) (erealValue .f32 (e 47)) := hP 23 (by decide)
  have p24 : V 7451 =
      .pair (erealValue .f32 (e 48)) (erealValue .f32 (e 49)) := hP 24 (by decide)
  have p25 : V 7452 =
      .pair (erealValue .f32 (e 50)) (erealValue .f32 (e 51)) := hP 25 (by decide)
  have p26 : V 7453 =
      .pair (erealValue .f32 (e 52)) (erealValue .f32 (e 53)) := hP 26 (by decide)
  have p27 : V 7454 =
      .pair (erealValue .f32 (e 54)) (erealValue .f32 (e 55)) := hP 27 (by decide)
  have p28 : V 7455 =
      .pair (erealValue .f32 (e 56)) (erealValue .f32 (e 57)) := hP 28 (by decide)
  have p29 : V 7456 =
      .pair (erealValue .f32 (e 58)) (erealValue .f32 (e 59)) := hP 29 (by decide)
  have p30 : V 7457 =
      .pair (erealValue .f32 (e 60)) (erealValue .f32 (e 61)) := hP 30 (by decide)
  have p31 : V 7458 =
      .pair (erealValue .f32 (e 62)) (erealValue .f32 (e 63)) := hP 31 (by decide)
  have p32 : V 7459 =
      .pair (erealValue .f32 (e 64)) (erealValue .f32 (e 65)) := hP 32 (by decide)
  have p33 : V 7460 =
      .pair (erealValue .f32 (e 66)) (erealValue .f32 (e 67)) := hP 33 (by decide)
  have p34 : V 7461 =
      .pair (erealValue .f32 (e 68)) (erealValue .f32 (e 69)) := hP 34 (by decide)
  have p35 : V 7462 =
      .pair (erealValue .f32 (e 70)) (erealValue .f32 (e 71)) := hP 35 (by decide)
  have p36 : V 7463 =
      .pair (erealValue .f32 (e 72)) (erealValue .f32 (e 73)) := hP 36 (by decide)
  have p37 : V 7464 =
      .pair (erealValue .f32 (e 74)) (erealValue .f32 (e 75)) := hP 37 (by decide)
  have p38 : V 7465 =
      .pair (erealValue .f32 (e 76)) (erealValue .f32 (e 77)) := hP 38 (by decide)
  have p39 : V 7466 =
      .pair (erealValue .f32 (e 78)) (erealValue .f32 (e 79)) := hP 39 (by decide)
  have p40 : V 7467 =
      .pair (erealValue .f32 (e 80)) (erealValue .f32 (e 81)) := hP 40 (by decide)
  have p41 : V 7468 =
      .pair (erealValue .f32 (e 82)) (erealValue .f32 (e 83)) := hP 41 (by decide)
  have p42 : V 7469 =
      .pair (erealValue .f32 (e 84)) (erealValue .f32 (e 85)) := hP 42 (by decide)
  have p43 : V 7470 =
      .pair (erealValue .f32 (e 86)) (erealValue .f32 (e 87)) := hP 43 (by decide)
  have p44 : V 7471 =
      .pair (erealValue .f32 (e 88)) (erealValue .f32 (e 89)) := hP 44 (by decide)
  have p45 : V 7472 =
      .pair (erealValue .f32 (e 90)) (erealValue .f32 (e 91)) := hP 45 (by decide)
  have p46 : V 7473 =
      .pair (erealValue .f32 (e 92)) (erealValue .f32 (e 93)) := hP 46 (by decide)
  have p47 : V 7474 =
      .pair (erealValue .f32 (e 94)) (erealValue .f32 (e 95)) := hP 47 (by decide)
  have p48 : V 7475 =
      .pair (erealValue .f32 (e 96)) (erealValue .f32 (e 97)) := hP 48 (by decide)
  have p49 : V 7476 =
      .pair (erealValue .f32 (e 98)) (erealValue .f32 (e 99)) := hP 49 (by decide)
  have p50 : V 7477 =
      .pair (erealValue .f32 (e 100)) (erealValue .f32 (e 101)) := hP 50 (by decide)
  have p51 : V 7478 =
      .pair (erealValue .f32 (e 102)) (erealValue .f32 (e 103)) := hP 51 (by decide)
  have p52 : V 7479 =
      .pair (erealValue .f32 (e 104)) (erealValue .f32 (e 105)) := hP 52 (by decide)
  have p53 : V 7480 =
      .pair (erealValue .f32 (e 106)) (erealValue .f32 (e 107)) := hP 53 (by decide)
  have p54 : V 7481 =
      .pair (erealValue .f32 (e 108)) (erealValue .f32 (e 109)) := hP 54 (by decide)
  have p55 : V 7482 =
      .pair (erealValue .f32 (e 110)) (erealValue .f32 (e 111)) := hP 55 (by decide)
  have p56 : V 7483 =
      .pair (erealValue .f32 (e 112)) (erealValue .f32 (e 113)) := hP 56 (by decide)
  have p57 : V 7484 =
      .pair (erealValue .f32 (e 114)) (erealValue .f32 (e 115)) := hP 57 (by decide)
  have p58 : V 7485 =
      .pair (erealValue .f32 (e 116)) (erealValue .f32 (e 117)) := hP 58 (by decide)
  have p59 : V 7486 =
      .pair (erealValue .f32 (e 118)) (erealValue .f32 (e 119)) := hP 59 (by decide)
  have p60 : V 7487 =
      .pair (erealValue .f32 (e 120)) (erealValue .f32 (e 121)) := hP 60 (by decide)
  have p61 : V 7488 =
      .pair (erealValue .f32 (e 122)) (erealValue .f32 (e 123)) := hP 61 (by decide)
  have p62 : V 7489 =
      .pair (erealValue .f32 (e 124)) (erealValue .f32 (e 125)) := hP 62 (by decide)
  have p63 : V 7490 =
      .pair (erealValue .f32 (e 126)) (erealValue .f32 (e 127)) := hP 63 (by decide)
  simp only [Gen.maxP_v6747_0, Gen.maxP_v6747_1, Gen.maxP_v6748, Gen.maxP_v6749_0,
    Gen.maxP_v6749_1, Gen.maxP_v6750, Gen.maxP_v6751_0, Gen.maxP_v6751_1, Gen.maxP_v6752,
    Gen.maxP_v6753_0, Gen.maxP_v6753_1, Gen.maxP_v6754, Gen.maxP_v6755_0, Gen.maxP_v6755_1,
    Gen.maxP_v6756, Gen.maxP_v6757_0, Gen.maxP_v6757_1, Gen.maxP_v6758, Gen.maxP_v6759_0,
    Gen.maxP_v6759_1, Gen.maxP_v6760, Gen.maxP_v6761_0, Gen.maxP_v6761_1, Gen.maxP_v6762,
    Gen.maxP_v6763_0, Gen.maxP_v6763_1, Gen.maxP_v6764, Gen.maxP_v6765_0, Gen.maxP_v6765_1,
    Gen.maxP_v6766, Gen.maxP_v6767_0, Gen.maxP_v6767_1, Gen.maxP_v6768, Gen.maxP_v6769_0,
    Gen.maxP_v6769_1, Gen.maxP_v6770, Gen.maxP_v6771_0, Gen.maxP_v6771_1, Gen.maxP_v6772,
    Gen.maxP_v6773_0, Gen.maxP_v6773_1, Gen.maxP_v6774, Gen.maxP_v6775_0, Gen.maxP_v6775_1,
    Gen.maxP_v6776, Gen.maxP_v6777_0, Gen.maxP_v6777_1, Gen.maxP_v6778, Gen.maxP_v6779_0,
    Gen.maxP_v6779_1, Gen.maxP_v6780, Gen.maxP_v6781_0, Gen.maxP_v6781_1, Gen.maxP_v6782,
    Gen.maxP_v6783_0, Gen.maxP_v6783_1, Gen.maxP_v6784, Gen.maxP_v6785_0, Gen.maxP_v6785_1,
    Gen.maxP_v6786, Gen.maxP_v6787_0, Gen.maxP_v6787_1, Gen.maxP_v6788, Gen.maxP_v6789_0,
    Gen.maxP_v6789_1, Gen.maxP_v6790, Gen.maxP_v6791_0, Gen.maxP_v6791_1, Gen.maxP_v6792,
    Gen.maxP_v6793_0, Gen.maxP_v6793_1, Gen.maxP_v6794, Gen.maxP_v6795_0, Gen.maxP_v6795_1,
    Gen.maxP_v6796, Gen.maxP_v6797_0, Gen.maxP_v6797_1, Gen.maxP_v6798, Gen.maxP_v6799_0,
    Gen.maxP_v6799_1, Gen.maxP_v6800, Gen.maxP_v6801_0, Gen.maxP_v6801_1, Gen.maxP_v6802,
    Gen.maxP_v6803_0, Gen.maxP_v6803_1, Gen.maxP_v6804, Gen.maxP_v6805_0, Gen.maxP_v6805_1,
    Gen.maxP_v6806, Gen.maxP_v6807_0, Gen.maxP_v6807_1, Gen.maxP_v6808, Gen.maxP_v6809_0,
    Gen.maxP_v6809_1, Gen.maxP_v6810, Gen.maxP_v6811_0, Gen.maxP_v6811_1, Gen.maxP_v6812,
    Gen.maxP_v6813_0, Gen.maxP_v6813_1, Gen.maxP_v6814, Gen.maxP_v6815_0, Gen.maxP_v6815_1,
    Gen.maxP_v6816, Gen.maxP_v6817_0, Gen.maxP_v6817_1, Gen.maxP_v6818, Gen.maxP_v6819_0,
    Gen.maxP_v6819_1, Gen.maxP_v6820, Gen.maxP_v6821_0, Gen.maxP_v6821_1, Gen.maxP_v6822,
    Gen.maxP_v6823_0, Gen.maxP_v6823_1, Gen.maxP_v6824, Gen.maxP_v6825_0, Gen.maxP_v6825_1,
    Gen.maxP_v6826, Gen.maxP_v6827_0, Gen.maxP_v6827_1, Gen.maxP_v6828, Gen.maxP_v6829_0,
    Gen.maxP_v6829_1, Gen.maxP_v6830, Gen.maxP_v6831_0, Gen.maxP_v6831_1, Gen.maxP_v6832,
    Gen.maxP_v6833_0, Gen.maxP_v6833_1, Gen.maxP_v6834, Gen.maxP_v6835_0, Gen.maxP_v6835_1,
    Gen.maxP_v6836, Gen.maxP_v6837_0, Gen.maxP_v6837_1, Gen.maxP_v6838, Gen.maxP_v6839_0,
    Gen.maxP_v6839_1, Gen.maxP_v6840, Gen.maxP_v6841_0, Gen.maxP_v6841_1, Gen.maxP_v6842,
    Gen.maxP_v6843_0, Gen.maxP_v6843_1, Gen.maxP_v6844, Gen.maxP_v6845_0, Gen.maxP_v6845_1,
    Gen.maxP_v6846, Gen.maxP_v6847_0, Gen.maxP_v6847_1, Gen.maxP_v6848, Gen.maxP_v6849_0,
    Gen.maxP_v6849_1, Gen.maxP_v6850, Gen.maxP_v6851_0, Gen.maxP_v6851_1, Gen.maxP_v6852,
    Gen.maxP_v6853_0, Gen.maxP_v6853_1, Gen.maxP_v6854, Gen.maxP_v6855_0, Gen.maxP_v6855_1,
    Gen.maxP_v6856, Gen.maxP_v6857_0, Gen.maxP_v6857_1, Gen.maxP_v6858, Gen.maxP_v6859_0,
    Gen.maxP_v6859_1, Gen.maxP_v6860, Gen.maxP_v6861_0, Gen.maxP_v6861_1, Gen.maxP_v6862,
    Gen.maxP_v6863_0, Gen.maxP_v6863_1, Gen.maxP_v6864, Gen.maxP_v6865_0, Gen.maxP_v6865_1,
    Gen.maxP_v6866, Gen.maxP_v6867_0, Gen.maxP_v6867_1, Gen.maxP_v6868, Gen.maxP_v6869_0,
    Gen.maxP_v6869_1, Gen.maxP_v6870, Gen.maxP_v6871_0, Gen.maxP_v6871_1, Gen.maxP_v6872,
    Gen.maxP_v6873_0, Gen.maxP_v6873_1, Gen.maxP_v6874, Gen.maxP_v6875, Gen.maxP_v6876, p0, p1,
    p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21,
    p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36, p37, p38, p39, p40,
    p41, p42, p43, p44, p45, p46, p47, p48, p49, p50, p51, p52, p53, p54, p55, p56, p57, p58, p59,
    p60, p61, p62, p63, h0, split_pair, maxE_er2, maxE_er3]
  rfl

theorem foldB_coe (mr : ℝ) (x : Nat → ℝ) :
    foldB (mr : EReal) (fun i => (x i : EReal)) = ((foldPT mr x : ℝ) : EReal) := by
  simp only [foldB, foldPT, coe_max]

theorem foldB_bot (x : Nat → ℝ) :
    foldB ⊥ (fun i => (x i : EReal)) = ((foldPF x : ℝ) : EReal) := by
  simp only [foldB, foldPF, coe_max, max_eq_right (bot_le : (⊥ : EReal) ≤ _)]

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
