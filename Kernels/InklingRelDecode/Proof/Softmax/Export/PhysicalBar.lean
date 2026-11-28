-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Export.RoundBar
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Prologue
import Kernels.InklingRelDecode.Proof.Common.DataOrdinal
import Kernels.InklingRelDecode.Proof.Common.SoftFixed
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Softmax.ScratchIteration

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Frame

def entryOrdinal (Q L c) := 3+5*Iface.preloadCount Q L c

private theorem previous_round {Q L X g k w ent d n}
    (len : k≤(X.tr g).length) (hs : stateAt (thread Q L) X g k=some (some (softState w ent d n))) :
    needsPrevious d.site=true → 0<d.i := by
  induction k using Nat.strong_induction_on generalizing d n with
  | h k ih =>
    by_cases initial : d={}
    · subst d; nofun
    obtain ⟨u,old,c,ev,eq,prev,_,move⟩ := soft_prev len initial hs
    exact previous_next (ih u (by omega) (by omega) prev) move

/-- Actual ordinal before any nonfaulting event in the Softmax interior:
setup, preloads, the fixed loop positions, and recorded visits to pc 2326. -/
theorem physical_bar {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,k)=some e)
    (clean : ∀ f, e.kind≠.ub f) (lo : 574<e.pc) (hi : e.pc<2331) :
    let es := (X.tr g).take k
    es.countP (Execution.isBarId 0)=entryOrdinal Q L (g/L.block)+mandatory es+
      es.countP (fun x => x.pc==2326) := by
  have hg := lt_of_get hX get
  obtain ⟨s,hs,_⟩ := good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX get (fun _ f h => clean f (congrArg Event.kind h))
    ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pc := event_pcU (fun g hg => thread_sound hp hg) hX get hs clean
  obtain ⟨w,ent,d,n,rfl⟩ := (pc ▸ state_role s).softmax lo hi
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nu := noUbBefore_of_get hX get
  have fixed := soft_fixed_total hp hX len hs nu
  have physical := data_ordinal hp hX len hs nu
  have count (key : Cls) : n key=((X.tr g).take k).countP (cls key) := fcount hs key
  rw [←fixed] at physical
  simp only [count,cls_bar0] at physical
  change ((X.tr g).take k).countP (Execution.isBarId 0)+2=entryOrdinal Q L (g/L.block)+
    (mandatory ((X.tr g).take k)+2)+((X.tr g).take k).countP (fun e => e.pc==2326) at physical
  dsimp only
  omega

/-- The optional rendezvous can be reached only after the first score round
and after the current round's scratch publication. -/
theorem rescale_mandatory {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,k)=some e)
    (atPc : e.pc=2326) (clean : ∀ f, e.kind≠.ub f) : 4≤mandatory ((X.tr g).take k) := by
  have hg := lt_of_get hX get
  obtain ⟨s,hs,_⟩ := good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX get (fun _ f h => clean f (congrArg Event.kind h))
    ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pc := event_pcU (fun g hg => thread_sound hp hg) hX get hs clean
  rw [atPc] at pc
  obtain ⟨w,ent,d,n,rfl⟩ := (pc ▸ state_role s).softmax (by decide : 574<2326)
    (by decide : 2326<2331)
  have only (s : Site) : 2326=s.pc → s=.bar24 := by
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  have tag := only d.site pc
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have pos := previous_round len hs (tag ▸ rfl)
  have fixed := soft_fixed_total hp hX len hs (noUbBefore_of_get hX get)
  have count (key : Cls) : n key=((X.tr g).take k).countP (cls key) := fcount hs key
  simp only [count,fixedCount,tag] at fixed
  change mandatory ((X.tr g).take k)+2=4*d.i+2 at fixed
  omega

theorem rescale_floor {Q L m X g k c} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (get : X.IsBarrier (g,k) 0 c 2326) : entryOrdinal Q L (g/L.block)+4≤
      ((X.tr g).take k).countP (Execution.isBarId 0) := by
  change X.get (g,k)=some ⟨2326,.bar 0 c .sync⟩ at get
  have low := rescale_mandatory hp hX get rfl (by simp)
  have phys := physical_bar hp hX get (by simp) (by dsimp; decide) (by dsimp; decide)
  dsimp only at phys
  omega

private theorem mandatory_mono (es : List Event) {j k : Nat} (le : j≤k) :
    mandatory (es.take j)≤mandatory (es.take k) := by
  unfold mandatory
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (countP_take_mono _ es le)
    (countP_take_mono _ es le)) (countP_take_mono _ es le)) (countP_take_mono _ es le)

/-- No optional rescale has yet occurred at the first scratch publication. -/
theorem before_rescale {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,k)=some e)
    (early : mandatory ((X.tr g).take k)<4) : ((X.tr g).take k).countP (fun x => x.pc==2326)=0 := by
  apply List.countP_eq_zero.mpr
  intro x mem hit
  obtain ⟨j,jlt,atJ⟩ := List.mem_iff_getElem.mp mem
  have jk : j<k := by simp only [List.length_take] at jlt; omega
  have full : X.get (g,j)=some x := by
    change (X.tr g)[j]?=some x
    rw [←List.getElem?_take_of_lt jk]
    exact List.getElem?_eq_some_iff.mpr ⟨jlt,atJ⟩
  have late := rescale_mandatory hp hX full (beq_iff_eq.mp hit)
    (noUbBefore_of_get hX get j jk x full)
  exact (Nat.not_le_of_lt early) (late.trans (mandatory_mono _ jk.le))

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
