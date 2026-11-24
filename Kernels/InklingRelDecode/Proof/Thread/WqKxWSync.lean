-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WqKxWStep

@[expose] public section

/-!
# The key time of the loader at synchronizing steps

`kstep_L`: two lanes' loader states at one synchronizing site with one key time (so one loop
counter in the loop), whose counters at `bar0` are equal (`WValid`) and which agree on the
branches at `bar0` and `el3` (`WAgree`), have successors of one key time. The MMA warp's steps
are in `WqKxWMma.lean`, the other roles' and the composition (`kxW_step`) in `WqKxWComp.lean`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g h : Nat} {e e' : Event}

/-! ### The loader -/

theorem loader_site_eq (a b : Loader.Site) (hs : syPc a.pc = true) (hs' : syPc b.pc = true)
    (hpc : a.pc = b.pc) : a = b := by
  cases a <;> cases b <;> first | rfl | (exfalso; revert hs hs' hpc; decide +kernel)

theorem kstep_L {d d' t t' : Loader.D} (hs : syPc d.site.pc = true)
    (hs' : syPc d'.site.pc = true) (hpc : d.site.pc = d'.site.pc) (hx : kxL d = kxL d')
    (hb : d.site = .bar0 → d.i = d'.i)
    (ha : LdAgree d d')
    (hn : Loader.next L g d e = some (some t)) (hn' : Loader.next L h d' e' = some (some t')) :
    kxL t = kxL t' := by
  have hab := loader_site_eq _ _ hs hs' hpc
  obtain ⟨a, pro, i, n, p0, p1, ln⟩ := d
  obtain ⟨b, pro', i', n', p0', p1', ln'⟩ := d'
  unfold LdAgree at ha
  simp only at hab ha hn hn' hb hx
  subst hab
  cases a <;>
    (simp only [forall_const, reduceCtorEq, false_implies, and_true, true_and] at ha hb
     simp only [kxL, loaderT, Bound.Loader.pos] at hx
     simp only [Loader.next, Loader.afterIter, Loader.readI, Loader.readN] at hn hn'
     (repeat' split at hn)
     all_goals (repeat' split at hn')
     all_goals
       first
       | (simp at hn; done)
       | (simp at hn'; done)
       | (simp only [Option.some.injEq] at hn hn'
          subst hn hn'
          first
          | rfl
          | (simp only [kxL, loaderT, Bound.Loader.pos]; done)
          | (simp only [kxL, loaderT, Bound.Loader.pos]
             (repeat' split) <;> first | (simp_all; done) | wt_omega)))

end
end PTX.Kernels.InklingRelDecode.Proof.Lk
