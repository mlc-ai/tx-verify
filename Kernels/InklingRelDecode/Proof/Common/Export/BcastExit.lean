-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Common.TcCount
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Softmax.Export.ExitShuffles
import Lemmas.Kernel.FrameU

@[expose] public section

/-! # No lane of a warp has exited before a warp-index broadcast

A data lane that makes the broadcast of a Softmax round (pc 1261) is below the launch's trip
count, and a data lane exits only after every shuffle of the rounds. A data lane that makes the
epilogue's broadcast (pc 2603) has not skipped it, so no data lane of its CTA exits without having
made it either. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow

private theorem shfl4_site (s : Softmax.Site) (h : s.pc=1261) : s=.shfl4 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem epi_shfl_site (s : Epilogue.Site) (h : s.pc=2603) : s=.shfl := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **A lane that makes a warp-index broadcast has no data lane of its CTA gone before its
shuffle.** -/
public theorem bcast_not_exited {Q L m X g k h n pc mode a b c recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (site : pc=1261 ∨ pc=2603) (get : X.get (g,k)=some ⟨pc,.shfl mode a b c recv ok⟩)
    (count : ((X.tr g).take k).countP Execution.isShfl=n)
    (lh : h%L.block<128) (cta : h/L.block=g/L.block) : ¬ ShflExited X h n := by
  rintro ⟨v,pc',exit,low⟩
  have clean : ∀ f, (Event.mk pc (.shfl mode a b c recv ok)).kind≠.ub f := fun _ => nofun
  have hg := Frame.lt_of_get hX get
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nu := Frame.noUbBefore_of_get hX get
  obtain ⟨total,after⟩ := Softmax.Export.exit_shuffles hp hX exit lh
  rw [cta] at total after
  rcases site with rfl|rfl
  · obtain ⟨w,ent,d,cnt,hs,at_pc⟩ := at_site hp hX get clean (by show 574<1261; omega)
      (by show 1261<2331; omega)
    have dsite : d.site=.shfl4 := shfl4_site _ at_pc.symm
    have ord := shfl_ordinal hp hX len hs nu
    have limit := reached_limit hp hX hg len hs
    have inv := reached_table hf hg nu hs
    have q : Softmax.Control.Inv ent (g%L.block) d := inv.1.1
    have below : d.i<ent.limit := by
      exact q.loop (by rw [dsite]; nofun) (by rw [dsite]; nofun) (by rw [dsite]; nofun)
        (fun _ => by rw [dsite]; nofun)
    have cnt_eq : cnt .shfl=((X.tr g).take k).countP Execution.isShfl := fcount hs _
    simp only [Softmax.shflCount,dsite,Softmax.shflInRound] at ord
    have lt := Lib.shflBase_lt below
    rw [limit] at lt
    omega
  · obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True)
      (fun g hg => thread_sound hp hg) hX get (fun _ f h => clean f (congrArg Event.kind h))
      ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
    have loc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get hs clean
    have hi := (reached_table hf hg nu hs).1
    have loc' : (2603:Nat)=(thread Q L g).pc s := loc
    have pl : Placement s 2603 := by rw [loc']; exact state_role s
    obtain ⟨w,ent,d,n',rfl⟩ := pl.epilogue (by omega) (by omega) hi
    have dsite : d.site=.shfl := epi_shfl_site _ loc.symm
    obtain ⟨exact,-,-⟩ := shfl_epi hp hX len hs nu
    have cnt_eq : n' .shfl=((X.tr g).take k).countP Execution.isShfl := fcount hs _
    obtain ⟨-,live⟩ := tc_inv hp hX hf hg len hs nu
    have skip := live (.inl dsite)
    have lim := reached_loop hp hX hg len hs
    have nz : Lib.blocksOf Q L (g/L.block)≠0 := by
      have : decide (ent.limit=0)=false := lim.2.symm.trans skip
      rw [←lim.1]
      simpa using this
    have := exact (.inr dsite)
    have bound := after nz
    rw [lim.1] at this
    dsimp only at this
    omega

end PTX.Kernels.InklingRelDecode.Proof.Export
