-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithBase

@[expose] public section

/-! # The publication of a tile's probabilities

After the stores of columns `64 … 111` the `tcgen05.wait::st` and the remote arrival on the
leader's P-ready barrier (`+144 + 8 st`, `mov.b32 …, 1` before it); after the last store the
second wait, the warp barrier and the election; the elected lane arrives on the leader's
`+160 + 8 st`. Each continues at the next instruction (the election writes its predicate,
whose value decides the branch around the elected lane's arrival). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState} {e : Event}

/-- The two `tcgen05.wait::st`: the P-ready arrival, or the warp barrier. -/
theorem step_pwait {ins : Instr} (hpre : Pre P L mem0) (lp : Bool) (hh : Fin 2)
    (hs : d.site = .pwait lp hh) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  cases lp <;> rcases fin2_cases hh with rfl | rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_0)
    obtain ⟨rfl, -⟩ := fires_tcWaitSt hf
    refine step_of_run (d' := ⟨.pArr false, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (fun _ => rfl) (by simp [Site.inTrip]) (by simp)) rfl rfl
      ⟨1, ?_⟩
    sm_seg (At.next h) hpre
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_1)
    obtain ⟨rfl, -⟩ := fires_tcWaitSt hf
    refine step_of_run (d' := ⟨.warpBar false, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (fun _ => rfl) (by simp [Site.inTrip]) (by simp)) rfl rfl
      ⟨0, ?_⟩
    sm_seg (At.next h) hpre
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_2)
    obtain ⟨rfl, -⟩ := fires_tcWaitSt hf
    refine step_of_run (d' := ⟨.pArr true, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (by simp [Site.tile0]) (fun _ => rfl) (by simp)) rfl rfl
      ⟨1, ?_⟩
    sm_seg (At.next h) hpre
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_3)
    obtain ⟨rfl, -⟩ := fires_tcWaitSt hf
    refine step_of_run (d' := ⟨.warpBar true, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (by simp [Site.tile0]) (fun _ => rfl) (by simp)) rfl rfl
      ⟨0, ?_⟩
    sm_seg (At.next h) hpre

/-- The P-ready arrival, then the last store of the tile. -/
theorem step_pArr {ins : Instr} (_hpre : Pre P L mem0) (lp : Bool) (hs : d.site = .pArr lp)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  cases lp
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_10)
    obtain rfl := fires_next (by exact trivial) hf
    refine step_of_run (d' := ⟨.pst false 3, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (fun _ => rfl) (by simp [Site.inTrip]) (by simp)) rfl rfl
      ⟨8, ?_⟩
    exact (seg_outs (pc := 2551) (items := pst0c) (liveS := Flow.live 2550 ++ [])
      (W := valueOf L g ⟨.pst false 3, i, tt, s, m, l⟩)
      (by decide +kernel) (by decide +kernel) (by kernel_rfl) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by unpacks_ok) (by kernel_rfl)) _ (At.next h)
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_12)
    obtain rfl := fires_next (by exact trivial) hf
    refine step_of_run (d' := ⟨.pst true 3, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (by simp [Site.tile0]) (fun _ => rfl) (by simp)) rfl rfl
      ⟨8, ?_⟩
    exact (seg_outs (pc := 3566) (items := pst1c) (liveS := Flow.live 3565 ++ [])
      (W := valueOf L g ⟨.pst true 3, i, tt, s, m, l⟩)
      (by decide +kernel) (by decide +kernel) (by kernel_rfl) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by unpacks_ok) (by kernel_rfl)) _ (At.next h)

/-- The warp barrier, then the election. -/
theorem step_warpBar {ins : Instr} (hpre : Pre P L mem0) (lp : Bool) (hs : d.site = .warpBar lp)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  cases lp
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_0)
    obtain rfl := fires_next (by exact trivial) hf
    refine step_of_run (d' := ⟨.el false, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (fun _ => rfl) (by simp [Site.inTrip]) (by simp)) rfl rfl
      ⟨0, ?_⟩
    sm_seg (At.next h) hpre
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_1)
    obtain rfl := fires_next (by exact trivial) hf
    refine step_of_run (d' := ⟨.el true, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (by simp [Site.tile0]) (fun _ => rfl) (by simp)) rfl rfl
      ⟨0, ?_⟩
    sm_seg (At.next h) hpre

/-- The elected lane's arrival on `+160 + 8 st`, then the statistics poll. The address of the
statistics barrier depends on the stage (`setp.gt.s32 p, %r1, 3; selp.b16`): the segment is cut
after the comparison, whose value is decided by the warp. -/
theorem step_p2Arr {ins : Instr} (hpre : Pre P L mem0) (lp : Bool) (hs : d.site = .p2Arr lp)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hn := trips_lt hpre
  have hw8 := hi.warp
  cases lp
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_11)
    obtain rfl := fires_next (by exact trivial) hf
    refine step_of_run (d' := ⟨.statsW 1, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (fun _ => rfl) (by simp [Site.inTrip]) (by simp)) rfl rfl ?_
    have h1 := At.next h
    by_cases hw : 3 < warpOf L g
    · obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 3 _ = some t1 ∧
          At t1 2570 (factsX L g 2570 ⟨.statsW 1, i, tt, s, m, l⟩ [(279, .pred true)]) := by
        sm_seg h1 hpre
      obtain ⟨t2, hr2, ht2⟩ : ∃ t2, run kernel asms L g 4 t1 = some t2 ∧
          At t2 (Site.statsW 1).pc
            (factsAt L g (Site.statsW 1).pc ⟨.statsW 1, i, tt, s, m, l⟩) := by
        sm_seg ht1 hpre
      exact ⟨_, t2, run_comp hr1 hr2, ht2⟩
    · obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 3 _ = some t1 ∧
          At t1 2570 (factsX L g 2570 ⟨.statsW 1, i, tt, s, m, l⟩ [(279, .pred false)]) := by
        sm_seg h1 hpre
      obtain ⟨t2, hr2, ht2⟩ : ∃ t2, run kernel asms L g 4 t1 = some t2 ∧
          At t2 (Site.statsW 1).pc
            (factsAt L g (Site.statsW 1).pc ⟨.statsW 1, i, tt, s, m, l⟩) := by
        sm_seg ht1 hpre
      exact ⟨_, t2, run_comp hr1 hr2, ht2⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_13)
    obtain rfl := fires_next (by exact trivial) hf
    refine step_of_run (d' := ⟨.statsW 2, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (by simp [Site.tile0]) (fun _ => rfl) (by simp)) rfl rfl ?_
    have h1 := At.next h
    by_cases hw : 3 < warpOf L g
    · obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 1 _ = some t1 ∧
          At t1 3583 (factsX L g 3583 ⟨.statsW 2, i, tt, s, m, l⟩ [(285, .pred true)]) := by
        sm_seg h1 hpre
      obtain ⟨t2, hr2, ht2⟩ : ∃ t2, run kernel asms L g 4 t1 = some t2 ∧
          At t2 (Site.statsW 2).pc
            (factsAt L g (Site.statsW 2).pc ⟨.statsW 2, i, tt, s, m, l⟩) := by
        sm_seg ht1 hpre
      exact ⟨_, t2, run_comp hr1 hr2, ht2⟩
    · obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 1 _ = some t1 ∧
          At t1 3583 (factsX L g 3583 ⟨.statsW 2, i, tt, s, m, l⟩ [(285, .pred false)]) := by
        sm_seg h1 hpre
      obtain ⟨t2, hr2, ht2⟩ : ∃ t2, run kernel asms L g 4 t1 = some t2 ∧
          At t2 (Site.statsW 2).pc
            (factsAt L g (Site.statsW 2).pc ⟨.statsW 2, i, tt, s, m, l⟩) := by
        sm_seg ht1 hpre
      exact ⟨_, t2, run_comp hr1 hr2, ht2⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
