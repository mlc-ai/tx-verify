-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.PollRounds
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import all Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section

/-! # The rescale store is in a round below the number of blocks

The store of pc 2328 is at the site `stO` of the loop, past the score poll of its round, and the
loop's counter is below the number of blocks there. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Frame

private theorem site_2328 (s : Site) (h : s.pc = 2328) : s = .stO := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **A rescale store follows at most as many score polls as there are blocks.** -/
public theorem rescale_round_le {Q L m X g k a vals sh} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g, k) = some ⟨2328, .tc (.st a vals sh)⟩) :
    pollRound 1257 ((X.tr g).take k) ≤ Lib.blocksOf Q L (g / L.block) := by
  have clean : ∀ f, (Event.mk 2328 (.tc (.st a vals sh))).kind ≠ .ub f := fun _ => nofun
  obtain ⟨w, ent, d, n, hs, pc⟩ := at_site hp hX he clean (by show 574 < 2328; omega)
    (by show 2328 < 2331; omega)
  have hg := lt_of_get hX he
  have hle := (List.getElem?_eq_some_iff.mp he).1.le
  have tbl := reached_table hf hg (noUbBefore_of_get hX he) hs
  have ref := tbl.2
  change Softmax.Ref _ d (softCounts n) at ref
  have sc := congrArg Softmax.Cnt.s ref.ledger
  change n (.poll 1257) = d.i + d.site.afterS.toNat at sc
  have cnt : n (.poll 1257) = ((X.tr g).take k).countP (cls (.poll 1257)) := fcount hs _
  rw [cnt] at sc
  have site : d.site = .stO := site_2328 _ pc.symm
  have lim := reached_loop hp hX hg hle hs
  have below : d.i < ent.limit := tbl.1.1.loop (by simp [site]) (by simp [site]) (by simp [site])
    (fun j => by simp [site])
  have a1 : d.site.afterS = true := by simp [site, Softmax.Site.afterS]
  have pr : pollRound 1257 ((X.tr g).take k) = d.i + d.site.afterS.toNat := sc
  rw [pr, a1, ← lim.1]
  simp only [Bool.toNat_true]
  omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
