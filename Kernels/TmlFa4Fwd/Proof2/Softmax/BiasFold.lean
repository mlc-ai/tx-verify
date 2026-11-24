-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.EReal.Basic

@[expose] public section

/-! # The bias round's maximum: the code's fold

The `max.f32` tree of a bias round (pcs 5536 to 5665) over the row maximum before the round `x0`
and the readings `e` of the round's 128 products (a real, or `-∞` for a masked bias half), with
four accumulators as the code computes it (a three-operand `max` is the maximum of the first two,
then the third). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax

noncomputable section

/-- The code's tree of the bias round's maximum. -/
def foldB (x0 : EReal) (e : Nat → EReal) : EReal :=
  let m5537 := max (max (x0) (e 0)) (e 1)
  let m5539 := max (e 2) (e 3)
  let m5541 := max (e 4) (e 5)
  let m5543 := max (e 6) (e 7)
  let m5545 := max (max (m5537) (e 8)) (e 9)
  let m5547 := max (max (m5539) (e 10)) (e 11)
  let m5549 := max (max (m5541) (e 12)) (e 13)
  let m5551 := max (max (m5543) (e 14)) (e 15)
  let m5553 := max (max (m5545) (e 16)) (e 17)
  let m5555 := max (max (m5547) (e 18)) (e 19)
  let m5557 := max (max (m5549) (e 20)) (e 21)
  let m5559 := max (max (m5551) (e 22)) (e 23)
  let m5561 := max (max (m5553) (e 24)) (e 25)
  let m5563 := max (max (m5555) (e 26)) (e 27)
  let m5565 := max (max (m5557) (e 28)) (e 29)
  let m5567 := max (max (m5559) (e 30)) (e 31)
  let m5569 := max (max (m5561) (e 32)) (e 33)
  let m5571 := max (max (m5563) (e 34)) (e 35)
  let m5573 := max (max (m5565) (e 36)) (e 37)
  let m5575 := max (max (m5567) (e 38)) (e 39)
  let m5577 := max (max (m5569) (e 40)) (e 41)
  let m5579 := max (max (m5571) (e 42)) (e 43)
  let m5581 := max (max (m5573) (e 44)) (e 45)
  let m5583 := max (max (m5575) (e 46)) (e 47)
  let m5585 := max (max (m5577) (e 48)) (e 49)
  let m5587 := max (max (m5579) (e 50)) (e 51)
  let m5589 := max (max (m5581) (e 52)) (e 53)
  let m5591 := max (max (m5583) (e 54)) (e 55)
  let m5593 := max (max (m5585) (e 56)) (e 57)
  let m5595 := max (max (m5587) (e 58)) (e 59)
  let m5597 := max (max (m5589) (e 60)) (e 61)
  let m5599 := max (max (m5591) (e 62)) (e 63)
  let m5601 := max (max (m5593) (e 64)) (e 65)
  let m5603 := max (max (m5595) (e 66)) (e 67)
  let m5605 := max (max (m5597) (e 68)) (e 69)
  let m5607 := max (max (m5599) (e 70)) (e 71)
  let m5609 := max (max (m5601) (e 72)) (e 73)
  let m5611 := max (max (m5603) (e 74)) (e 75)
  let m5613 := max (max (m5605) (e 76)) (e 77)
  let m5615 := max (max (m5607) (e 78)) (e 79)
  let m5617 := max (max (m5609) (e 80)) (e 81)
  let m5619 := max (max (m5611) (e 82)) (e 83)
  let m5621 := max (max (m5613) (e 84)) (e 85)
  let m5623 := max (max (m5615) (e 86)) (e 87)
  let m5625 := max (max (m5617) (e 88)) (e 89)
  let m5627 := max (max (m5619) (e 90)) (e 91)
  let m5629 := max (max (m5621) (e 92)) (e 93)
  let m5631 := max (max (m5623) (e 94)) (e 95)
  let m5633 := max (max (m5625) (e 96)) (e 97)
  let m5635 := max (max (m5627) (e 98)) (e 99)
  let m5637 := max (max (m5629) (e 100)) (e 101)
  let m5639 := max (max (m5631) (e 102)) (e 103)
  let m5641 := max (max (m5633) (e 104)) (e 105)
  let m5643 := max (max (m5635) (e 106)) (e 107)
  let m5645 := max (max (m5637) (e 108)) (e 109)
  let m5647 := max (max (m5639) (e 110)) (e 111)
  let m5649 := max (max (m5641) (e 112)) (e 113)
  let m5651 := max (max (m5643) (e 114)) (e 115)
  let m5653 := max (max (m5645) (e 116)) (e 117)
  let m5655 := max (max (m5647) (e 118)) (e 119)
  let m5657 := max (max (m5649) (e 120)) (e 121)
  let m5659 := max (max (m5651) (e 122)) (e 123)
  let m5661 := max (max (m5653) (e 124)) (e 125)
  let m5663 := max (max (m5655) (e 126)) (e 127)
  let m5664 := max (m5657) (m5659)
  let m5665 := max (max (m5664) (m5661)) (m5663)
  m5665

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
