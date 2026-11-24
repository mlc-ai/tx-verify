-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Base
public import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

theorem stepAt_start (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : d.site = .start) :
    (code p L g ent).StepAt d := by
  have hparams := params hp
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, word32, tlOf, afterTotal, loopHead, scanExit, loopOf, Scan.late, storeNext]
    seg_by (ep_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

theorem stepAt_word_first (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : d.site = .word .first) :
    (code p L g ent).StepAt d := by
  have hparams := params hp
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, word32, tlOf, afterTotal, loopHead, scanExit, loopOf, Scan.late, storeNext]
    seg_by (ep_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

theorem stepAt_down_first (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : d.site = .down .first) :
    (code p L g ent).StepAt d := by
  have hparams := params hp
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, word32, tlOf, afterTotal, loopHead, scanExit, loopOf, Scan.late, storeNext]
    seg_by (ep_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

theorem stepAt_up_first (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : ∃ j, d.site = .up .first j) :
    (code p L g ent).StepAt d := by
  have hparams := params hp
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, word32, tlOf, afterTotal, loopHead, scanExit, loopOf, Scan.late, storeNext]
    seg_by (ep_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

theorem stepAt_total_first (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : d.site = .total .first) :
    (code p L g ent).StepAt d := by
  have hparams := params hp
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, word32, tlOf, afterTotal, loopHead, scanExit, loopOf, Scan.late, storeNext]
    seg_by (ep_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
