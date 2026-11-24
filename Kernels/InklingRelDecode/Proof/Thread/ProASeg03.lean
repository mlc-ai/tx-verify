-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProATac

@[expose] public section

/-! # The prologue's local segments, pc 505 to 573

Each lemma is one run of local instructions between two checkpoints, from the registers live at
the first (valued by the table of the thread's data) to the registers live at the second. A run
that starts after an election carries the facts of the election's result (the predicate of the
elected lane and of the guard, `a` and `b`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

seg_run seg_507_515_skipG 507 515 skip 84 q 60 64
seg_run seg_515_522 515 522 [v_r325, v_r326, v_r327, v_r328, v_r329, v_r330, v_r285]
seg_pack seg_522_523 522 0 1
seg_pack seg_523_524 523 2 3
seg_pack seg_524_525 524 4 5
seg_pack seg_525_526 525 6 7
seg_run seg_527_528 527 528 [v_r290]
seg_pack seg_528_529 528 8 9
seg_pack seg_529_530 529 10 11
seg_pack seg_530_531 530 12 13
seg_pack seg_531_532 531 14 15
seg_run seg_533_534 533 534 [v_r295]
seg_pack seg_534_535 534 16 17
seg_pack seg_535_536 535 18 19
seg_pack seg_536_537 536 20 21
seg_pack seg_537_538 537 22 23
seg_run seg_539_540 539 540 [v_r300]
seg_pack seg_540_541 540 24 25
seg_pack seg_541_542 541 26 27
seg_pack seg_542_543 542 28 29
seg_pack seg_543_544 543 30 31
seg_run seg_545_546 545 546 [v_r305]
seg_pack seg_546_547 546 32 33
seg_pack seg_547_548 547 34 35
seg_pack seg_548_549 548 36 37
seg_pack seg_549_550 549 38 39
seg_run seg_551_552 551 552 [v_r310]
seg_pack seg_552_553 552 40 41
seg_pack seg_553_554 553 42 43
seg_pack seg_554_555 554 44 45
seg_pack seg_555_556 555 46 47
seg_run seg_557_558 557 558 [v_r315]
seg_pack seg_558_559 558 48 49
seg_pack seg_559_560 559 50 51
seg_pack seg_560_561 560 52 53
seg_pack seg_561_562 561 54 55
seg_run seg_563_564 563 564 [v_r320]
seg_pack seg_564_565 564 56 57
seg_pack seg_565_566 565 58 59
seg_pack seg_566_567 566 60 61
seg_pack seg_567_568 567 62 63
seg_run seg_572_573 572 573 [v_r331]

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
