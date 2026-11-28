-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Softmax.Export.RoundBar
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Kernels.InklingRelDecode.Proof.Lib.ShuffleRounds
import Kernels.InklingRelDecode.Proof.Softmax.ShuffleCount
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.SoftFixed
import Kernels.InklingRelDecode.Proof.Common.Where
import Lemmas.Kernel.Frame

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow

private theorem store_site (s : Site) (h : s.pc=2250) : s=.store10 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **The round of the scratch store.** The mandatory rendezvous before it and the shuffles of
the lane before it are fixed by the round `r`. -/
public theorem store_round {Q L m X g u dst ys} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,u)=some ⟨2250,.wr dst ys⟩) :
    ∃ r, mandatory ((X.tr g).take u)+2=4*r+1 ∧
      ((X.tr g).take u).countP Execution.isShfl=
        1+Iface.preloadCount Q L (g/L.block)+Lib.shflBase r+7 := by
  have clean : ∀ f, (Event.mk 2250 (.wr dst ys)).kind≠.ub f := fun _ => nofun
  obtain ⟨w,ent,d,n,hs,pce⟩ := at_site hp hX get clean (by show 574<2250; decide)
    (by show 2250<2331; decide)
  have site : d.site=.store10 := store_site _ pce.symm
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nu := Frame.noUbBefore_of_get hX get
  have fixed := soft_fixed_total hp hX len hs nu
  have ord := shfl_ordinal hp hX len hs nu
  have cnt (key : Cls) : n key=((X.tr g).take u).countP (cls key) := fcount hs key
  have shf : n Cls.shfl=((X.tr g).take u).countP Execution.isShfl := fcount hs _
  simp only [cnt] at fixed
  refine ⟨d.i,?_,?_⟩
  · simp only [Softmax.fixedCount,site,Softmax.syncPosition] at fixed
    exact fixed
  · rw [←shf,ord]
    simp [Softmax.shflCount,site,Softmax.shflInRound]
    omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
