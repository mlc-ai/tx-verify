-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.Classes
import Kernels.InklingRelDecode.Proof.Common.Export.BarSteps
import Kernels.InklingRelDecode.Proof.Common.Export.BarFinal
import Kernels.InklingRelDecode.Proof.Common.Export.BarZero
import Kernels.InklingRelDecode.Proof.Protocol.Bar.Groups
import Kernels.InklingRelDecode.Proof.Protocol.Bar.One
import Kernels.InklingRelDecode.Proof.Protocol.Bar.AlignedLanes
import Kernels.InklingRelDecode.Proof.Protocol.Bar.LoopLag
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Kernels.InklingRelDecode.Proof.Top.Safe.UbWeaken
import Lemmas.Kernel.Progress.BarPhasedSteps

/-! # A lane blocked at a named barrier steps

A barrier of the kernel is barrier 1 (the whole CTA, four generations), or barrier 0 in one of
its three uses: the two startup rendezvous, the loop (the four data warps with the count 128), the
final rendezvous (the whole CTA). Each is the progress tool of its generation with the group of
the barrier (`Protocol.Bar`) and the clock facts of the lanes (`Export`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow PTX.Sched Protocol

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A lane blocked at a rendezvous of a named barrier steps.** -/
public theorem Prog.bar_steps (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    {g : Nat} (hpd : Frame.Pending L X g) (hrel : ¬ Step.Released L X g)
    (hw : Sched.BarWait L X g) : Sched.Steps (schedule Q L) m X (.thread g) := by
  have hX := hmax.1
  have hsafe := hs.2 X hX
  have safe : ¬Race L X := fun h => hsafe (by simp [Unsafe, h])
  have hu := Sched.safe_noUb hsafe
  have nu : ∀ y, NoUbLane X y := fun y => .of_noUb hu y
  have hb : L.block = 256 := hp.block
  obtain ⟨id, cnt, pc, hlen, hlast, -⟩ := hw
  have hget : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id cnt .sync⟩ := hlast
  have modlt : g % L.block / 32 < 8 := by
    have := Nat.mod_lt g (show L.block > 0 by omega)
    omega
  obtain ⟨-, r⟩ := Lib.recorded_bar hX hb hget
  rcases r with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, hc, -⟩
  · exact Export.bar1_steps hp hs hmax hf words nu (Bar.one_shape hp) (Bar.one_sources hp hX)
      hpd hrel hlen hlast
  · have hS := Export.barZeroSources hp hX
    by_cases hlt : ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 0) < 2
    · refine Export.bar0_early_steps hp hs hmax hf nu (Bar.group_sub hp) (Finset.card_range 4)
        (Bar.group_ne hp) Bar.group_target hS (Bar.all_shape hp) hpd hrel hlen hlast
        (Finset.mem_range.mpr (by simp [CtaBarrier.warps, hb]; omega)) ?_ hlt
      intro y j pc' cnt' md hy hc hw hy' ord
      rcases hS (y, j) pc' cnt' ⟨md, hy'⟩ hy with h | ⟨-, -, h⟩
      · exact h
      · exact absurd (ord ▸ h) (by omega)
    · refine Export.bar0_final_steps hp hs hmax hf words nu (Bar.group_sub hp)
        (Finset.card_range 4) (Bar.group_ne hp) Bar.group_target hS (Bar.all_shape hp)
        hpd hrel hlen hlast (by omega) ?_
      intro y y' j j' hy hy' cy cy' hw ⟨pj, mj, gj, oj⟩ ⟨pj', mj', gj', oj'⟩
      obtain rfl := (Lib.recorded_bar hX hb gj).1
      obtain rfl := (Lib.recorded_bar hX hb gj').1
      by_cases low : y % L.block < 128
      · exact Bar.final_ordinal_agree hp hX hf safe (cy.trans cy'.symm) low
          (by omega) gj gj' oj oj'
      · have a := Export.worker_final_c0 hp hX hf words gj oj (by omega)
        have b := Export.worker_final_c0 hp hX hf words gj' oj' (by omega)
        exact a.trans b.symm
  · have hc' : cnt = some 128 := by simpa [BarRow.recCnt, hb] using hc
    subst hc'
    rcases Export.barZeroSources hp hX (g, (X.tr g).length - 1) pc (some 128) ⟨.sync, hget⟩
      hpd.1 with h | ⟨-, hgp, hord⟩
    · cases h
    · have lg : g % L.block < 128 := by
        have h4 : g % L.block / 32 < 4 := Finset.mem_range.mp hgp
        omega
      refine Export.bar0_loop_steps hp hs hmax hf (Bar.group_sub hp) (Finset.card_range 4)
        (Bar.group_ne hp) Bar.group_target (Export.barZeroSources hp hX) (Bar.loop_shape hp)
        hpd hrel hlen hlast hgp ?_ ?_
      · intro y j pc' cnt' md hy hc hw hy' ord
        have ly : y % L.block < 128 := by
          have := Finset.mem_range.mp hw
          omega
        exact (Bar.alpha_agree hp hX hf safe (by rw [hc]) lg ly hget hy' ord.symm).symm
      · intro y hy hc hw hle
        have ly : y % L.block < 128 := by
          have := Finset.mem_range.mp hw
          omega
        exact Bar.loop_lag hp hX hf safe nu hy hc lg ly hget hle

end PTX.Kernels.InklingRelDecode.Proof.Top
