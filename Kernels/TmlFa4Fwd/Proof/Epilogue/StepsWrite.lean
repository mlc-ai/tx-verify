-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Epilogue.Base
import Lemmas.Flow.Step.SiteCases
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Gen.StepEpilogue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

theorem stepAt_read (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : d.site = .q0 ∨ d.site = .q1) :
    (code p L g ent).StepAt d := by
  have hparams := params hp
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, word32, tlOf, afterTotal, loopHead, scanExit, loopOf, Scan.late, storeNext]
    seg_by (ep_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

theorem stepAt_ready (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : ∃ st, d.site = .ready st) :
    (code p L g ent).StepAt d := by
  have hparams := params hp
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, word32, tlOf, afterTotal, loopHead, scanExit, loopOf, Scan.late, storeNext]
    seg_by (ep_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

theorem stepAt_store (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : ∃ st b, d.site = .store st b) :
    (code p L g ent).StepAt d := by
  have hparams := params hp
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, word32, tlOf, afterTotal, loopHead, scanExit, loopOf, Scan.late, storeNext]
    seg_by (ep_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

theorem stepAt_commit (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : (∃ st, d.site = .commit st) ∨ (∃ st, d.site = .drain st)) :
    (code p L g ent).StepAt d := by
  have hparams := params hp
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, word32, tlOf, afterTotal, loopHead, scanExit, loopOf, Scan.late, storeNext]
    seg_by (ep_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

theorem stepAt_free (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : ∃ st, d.site = .free st) :
    (code p L g ent).StepAt d := by
  have hparams := params hp
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, word32, tlOf, afterTotal, loopHead, scanExit, loopOf, Scan.late, storeNext]
    seg_by (ep_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

theorem stepAt_exit (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : ∃ l, d.site = .exit l) :
    (code p L g ent).StepAt d := by
  have hparams := params hp
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, word32, tlOf, afterTotal, loopHead, scanExit, loopOf, Scan.late, storeNext]
    seg_by (ep_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
