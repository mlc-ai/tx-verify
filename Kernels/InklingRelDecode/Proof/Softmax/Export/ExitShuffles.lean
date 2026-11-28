-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.ShuffleRounds
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Lib.ResPcs
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Lemmas.Flow.NotBulk

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow PTX.Frame

private theorem startup_far (st : Startup.Site) : st.pc≠2855 := by
  cases st <;> first | decide | (rename_i r; cases r <;> decide)

set_option maxRecDepth 10000 in
/-- A data lane exits only after every shuffle of the Softmax rounds: one for the startup, one
for each preloaded block and the loop's own. -/
theorem exit_shuffles {Q L m X h v pc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (exit : X.get (h,v)=some ⟨pc,.exit⟩) (lane : h%L.block<128) :
    1+Iface.preloadCount Q L (h/L.block)+Lib.shflBase (Lib.blocksOf Q L (h/L.block))≤
      ((X.tr h).take v).countP Execution.isShfl ∧
    (Lib.blocksOf Q L (h/L.block)≠0 → 2+Iface.preloadCount Q L (h/L.block)+
      Lib.shflBase (Lib.blocksOf Q L (h/L.block))≤((X.tr h).take v).countP Execution.isShfl) := by
  have hg := lt_of_get hX exit
  obtain ⟨s,hs,_⟩ := good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX exit (by simp) ⟨control_tracked hp hX h v hg,fun _ _ => trivial⟩
  have at_pc := event_pcU (fun g hg => thread_sound hp hg) hX exit hs (by simp)
  have len := (List.getElem?_eq_some_iff.mp exit).1.le
  have nu := noUbBefore_of_get hX exit
  obtain ⟨_,bad⟩|⟨_,_,_,_,hc,fire⟩ := get_source hX exit
  · cases bad
  have ret := Lib.ret_pc' hc fire rfl
  obtain rfl : pc=2855 := by simpa [Lib.retPcs] using ret
  obtain ⟨s,n⟩ := s
  rcases s with s|⟨r,d⟩
  · exfalso
    exact startup_far s.site at_pc.symm
  rcases r with r|r
  swap
  · exfalso
    change 2855=Startup.Entry.pc r at at_pc
    cases r <;> contradiction
  cases r with
  | dispatch =>
    obtain ⟨wide,_⟩ := worker_warp hp hX len hs
    change 128≤h%L.block at wide
    omega
  | prologue w =>
    rcases d with d|⟨ent,d|⟨⟨⟩,d⟩⟩
    · have := d.site.pc_range
      change 2855=d.site.pc at at_pc
      omega
    · have range := d.site.pc_range
      change 2855=d.site.pc at at_pc
      rcases range with range|range
      · omega
      · rw [range] at at_pc
        exact absurd at_pc (by decide)
    · have bound : 1+Iface.preloadCount Q L (h/L.block)+Lib.shflBase ent.limit≤n .shfl :=
        shfl_epilogue hp hX len hs nu
      have limit := reached_limit hp hX hg len hs
      have count : n .shfl=((X.tr h).take v).countP Execution.isShfl := fcount hs _
      rw [limit] at bound
      refine ⟨by omega,fun nz => ?_⟩
      obtain ⟨_,_,past⟩ := shfl_epi hp hX len hs nu
      have site : d.site=.exit := by
        have eq := d.site.pc_range
        revert at_pc
        change 2855=d.site.pc → _
        generalize d.site=st
        intro h
        cases st <;> first | rfl | (exfalso; revert h; decide) |
          (exfalso; rename_i j; revert h j; decide +kernel)
      have lim := reached_loop hp hX hg len hs
      have skip : (epiEntry ent (h%L.block)).skip=false := by
        have : (epiEntry ent (h%L.block)).skip=decide (ent.limit=0) := lim.2
        rw [this,lim.1]
        simp [nz]
      have after := past (by rw [site]; rfl) skip
      rw [limit] at after
      dsimp only at after
      omega
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
