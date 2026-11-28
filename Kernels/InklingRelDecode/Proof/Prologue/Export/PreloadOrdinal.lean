-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Prologue
import Kernels.InklingRelDecode.Proof.Common.DataOrdinal
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Frame

private theorem upper (p : Nat) (s : Site) (gate : ∀ b, s.block=some b → b.val<p) :
    preloadPosition p s≤3+5*p := by
  cases s
  all_goals try exact Nat.le_refl _
  all_goals try exact (by change 2≤_; omega)
  all_goals have lt := gate _ rfl
  all_goals first
    | (rename_i b j; fin_cases j <;> simp [preloadPosition] <;> omega)
    | (simp [preloadPosition]; omega)

/-- A prologue barrier cannot belong to any later Softmax round. -/
public theorem preload_ordinal_bound {Q L m X g k pc cnt} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.IsBarrier (g,k) 0 cnt pc)
    (lo : 180≤pc) (hi : pc<574) :
    ((X.tr g).take k).countP (Execution.isBarId 0)≤3+5*Iface.preloadCount Q L (g/L.block) := by
  change X.get (g,k)=some ⟨pc,.bar 0 cnt .sync⟩ at get
  have hg := lt_of_get hX get
  obtain ⟨s,hs,_⟩ := good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX get (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pos := event_pcU (fun g hg => thread_sound hp hg) hX get hs (by simp)
  change pc=_ at pos
  obtain ⟨w,d,n,rfl⟩ := (pos ▸ state_role s).prologue (by omega) hi
  change pc=d.site.pc at pos
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nu := noUbBefore_of_get hX get
  have before := preload_ordinal hp hX len hs nu
  have hist := (data_reference hp hX len hs (prefix_ub_zero hs nu)).1
  have cap := preload_count hp hg (hist.known.first (by omega)) (hist.known.last (by omega))
    (hist.known.seq (by omega))
  have le := upper (Iface.preloadCount Q L (g/L.block)) d.site (fun b block => by
    rw [←cap]
    exact lt_min b.isLt (hist.block b block))
  have count : n (.bar 0)=_ := (fcount hs (.bar 0)).trans (by rw [cls_bar0])
  exact count ▸ before ▸ le

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
