-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxBase

@[expose] public section

/-! # The election after a tile's stores

`elect.sync` writes the leader's lane to a dead register and the thread's election to a
predicate; `not.pred` and `@p bra` send the elected lane to its arrival on `+160 + 8 st` and the
others past it, to the statistics poll (whose address depends on the stage: the segment is cut
after the stage comparison, as in `step_p2Arr`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- After an election that writes the dead register `dr` and the predicate `p`. -/
theorem at_elect {L : Launch} {g : Nat} {d : D} {t : TState} {pc dr p : Nat} {x : Value}
    {b : Bool} (h : At t pc (factsAt L g pc d)) (hd : dr ∉ Flow.live pc)
    (hp : p ∉ Flow.live pc) :
    At (PTX.next (setReg (setReg t dr x) p (.pred b))) (pc + 1)
      ((p, .pred b) :: factsAt L g pc d) := by
  refine At.set ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩ (facts_ne hp)
  exact holds_update h.2.2.2.2 (facts_ne hd)

theorem step_el {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (lp : Bool)
    (hs : d.site = .el lp) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hn := trips_lt hpre
  have hw8 := hi.warp
  cases lp
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_52)
    obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
    have h1 := at_elect (d := ⟨.el false, i, tt, s, m, l⟩) (dr := 1972) (p := 276)
      (x := .bits 32 (BitVec.ofNat 64 ld)) (b := laneOf L g == ld) h (by table_decide)
      (by table_decide)
    cases hb : (laneOf L g == ld)
    · rw [hb] at h1
      have hne : laneOf L g ≠ ld := by simpa using hb
      refine step_of_run (d' := ⟨.statsW 1, i, tt, s, m, l⟩) (by simp [next, hne])
        (inv_move hi rfl rfl rfl rfl (fun _ => rfl) (by simp [Site.inTrip]) (by simp)) rfl rfl
        ?_
      by_cases hw : 3 < warpOf L g
      · obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 5 _ = some t1 ∧
            At t1 2570 (factsX L g 2570 ⟨.statsW 1, i, tt, s, m, l⟩ [(279, .pred true)]) := by
          sm_seg h1 hpre
        obtain ⟨t2, hr2, ht2⟩ : ∃ t2, run kernel asms L g 4 t1 = some t2 ∧
            At t2 (Site.statsW 1).pc
              (factsAt L g (Site.statsW 1).pc ⟨.statsW 1, i, tt, s, m, l⟩) := by
          sm_seg ht1 hpre
        exact ⟨_, t2, run_comp hr1 hr2, ht2⟩
      · obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 5 _ = some t1 ∧
            At t1 2570 (factsX L g 2570 ⟨.statsW 1, i, tt, s, m, l⟩ [(279, .pred false)]) := by
          sm_seg h1 hpre
        obtain ⟨t2, hr2, ht2⟩ : ∃ t2, run kernel asms L g 4 t1 = some t2 ∧
            At t2 (Site.statsW 1).pc
              (factsAt L g (Site.statsW 1).pc ⟨.statsW 1, i, tt, s, m, l⟩) := by
          sm_seg ht1 hpre
        exact ⟨_, t2, run_comp hr1 hr2, ht2⟩
    · rw [hb] at h1
      have heq : laneOf L g = ld := by simpa using hb
      refine step_of_run (d' := ⟨.p2Arr false, i, tt, s, m, l⟩) (by simp [next, heq])
        (inv_move hi rfl rfl rfl rfl (fun _ => rfl) (by simp [Site.inTrip]) (by simp)) rfl rfl
        ⟨3, ?_⟩
      sm_seg h1 hpre
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_53)
    obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
    have h1 := at_elect (d := ⟨.el true, i, tt, s, m, l⟩) (dr := 2685) (p := 283)
      (x := .bits 32 (BitVec.ofNat 64 ld)) (b := laneOf L g == ld) h (by table_decide)
      (by table_decide)
    cases hb : (laneOf L g == ld)
    · rw [hb] at h1
      have hne : laneOf L g ≠ ld := by simpa using hb
      refine step_of_run (d' := ⟨.statsW 2, i, tt, s, m, l⟩) (by simp [next, hne])
        (inv_move hi rfl rfl rfl rfl (by simp [Site.tile0]) (fun _ => rfl) (by simp)) rfl rfl
        ?_
      by_cases hw : 3 < warpOf L g
      · obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 3 _ = some t1 ∧
            At t1 3583 (factsX L g 3583 ⟨.statsW 2, i, tt, s, m, l⟩ [(285, .pred true)]) := by
          sm_seg h1 hpre
        obtain ⟨t2, hr2, ht2⟩ : ∃ t2, run kernel asms L g 4 t1 = some t2 ∧
            At t2 (Site.statsW 2).pc
              (factsAt L g (Site.statsW 2).pc ⟨.statsW 2, i, tt, s, m, l⟩) := by
          sm_seg ht1 hpre
        exact ⟨_, t2, run_comp hr1 hr2, ht2⟩
      · obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 3 _ = some t1 ∧
            At t1 3583 (factsX L g 3583 ⟨.statsW 2, i, tt, s, m, l⟩ [(285, .pred false)]) := by
          sm_seg h1 hpre
        obtain ⟨t2, hr2, ht2⟩ : ∃ t2, run kernel asms L g 4 t1 = some t2 ∧
            At t2 (Site.statsW 2).pc
              (factsAt L g (Site.statsW 2).pc ⟨.statsW 2, i, tt, s, m, l⟩) := by
          sm_seg ht1 hpre
        exact ⟨_, t2, run_comp hr1 hr2, ht2⟩
    · rw [hb] at h1
      have heq : laneOf L g = ld := by simpa using hb
      refine step_of_run (d' := ⟨.p2Arr true, i, tt, s, m, l⟩) (by simp [next, heq])
        (inv_move hi rfl rfl rfl rfl (by simp [Site.tile0]) (fun _ => rfl) (by simp)) rfl rfl
        ⟨3, ?_⟩
      sm_seg h1 hpre

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
