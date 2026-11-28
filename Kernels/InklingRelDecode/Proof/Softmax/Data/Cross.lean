-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Phase
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Stop
public import Lemmas.Flow.Step.TcSteps
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The data steps that leave the round

The shuffles of pcs 2234 and 2255 and the wait of pc 2329 leave the round for the barrier of
pc 999 (through the update of pc 949) or for the next event of the round. The facts are given by
position (`Data/Phase.lean`) and the control machine names the stop. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

theorem hseg_ivs {ivs : List (Nat × Nat)} {spec : Nat → Bool}
    (h : ((pcsOf ivs).all fun pc => !Assumptions.emuSites.contains pc) = true) :
    ∀ pc, inIvs ivs pc = true → spec pc = false → Assumption.SegFreePc Assumptions.all pc := by
  intro pc hp _
  refine Kernels.InklingRelDecode.Proof.segFree ?_
  have : pc ∈ pcsOf ivs := List.contains_iff_mem.mp (by rw [pcsOf_contains]; exact hp)
  simpa using List.all_eq_true.mp h pc this

/-- Where the successor's data facts come from, by the successor's site. -/
theorem conv_succ {d d' : D} (hd : d'.c.site = .bar20 ∨ d'.c.site = .waitO ∨ d'.c.site = .ldO)
    (hv : (d'.c.site = .bar20 → d'.v.m = Lib.mNext (scaleW L) d.v.m d.v.mx) ∧
      (d'.c.site ≠ .bar20 → d'.v.main d.v))
    {R : Nat → Option Value}
    (h : Holds R (phi updKeys updPost (updV1 L d.v.m d.v.mx) (updV2 L d.v.m d.v.mx)
      d'.c.site.pc)) : Holds R (dF L d') := by
  rcases hd with h1 | h1 | h1
  · rw [h1] at h
    simp only [dF, h1]
    exact phi_bar20 _ _ _ (hv.1 h1) h
  · rw [h1] at h
    simp only [dF, h1]
    rw [dFS_congr L _ (hv.2 (by rw [h1]; decide))]
    exact phi_round (Or.inl rfl) _ h
  · rw [h1] at h
    simp only [dF, h1]
    rw [dFS_congr L _ (hv.2 (by rw [h1]; decide))]
    exact phi_round (Or.inr rfl) _ h

theorem hv_cross {L : Launch} {d : D} {ev : Event} {z : Site}
    (hs : d.c.site = .shfl6 ∨ d.c.site = .shfl12 ∨ d.c.site = .waitStO) {v : Vals}
    (hv : v = record L d ev z) :
    (z = .bar20 → v.m = Lib.mNext (scaleW L) d.v.m d.v.mx) ∧ (z ≠ .bar20 → v.main d.v) := by
  subst hv
  unfold record
  rcases hs with h | h | h <;> rw [h] <;> constructor <;> intro hz <;> simp [hz, Vals.main]

/-- **The data step of an event that leaves the round**, from the state after it. -/
theorem cross_step {d d' : D} {t u : TState} {ev : Event} {ins : Instr} {ivs : List (Nat × Nat)}
    (hat : (code e L g).AtD d t) (hi : (code e L g).inv d)
    (hc : kernel.code[(code e L g).pc d]? = some ins)
    (hf : Fires ((code e L g).pc d) (eventTmpl Assumptions.all L g t ins.op) ev (some u))
    (hn : (code e L g).next d ev = some (some d'))
    (hscan : tabScan kernel ivs updKeys updPost updSpec = true)
    (hemu : ((pcsOf ivs).all fun pc => !Assumptions.emuSites.contains pc) = true)
    (hiv : inIvs ivs 950 = true)
    (hu : (inIvs ivs u.pc || evAtB kernel u.pc) = true)
    (hT : TabAt updKeys updPost (updV1 L d.v.m d.v.mx) (updV2 L d.v.m d.v.mx) u)
    (hd : d'.c.site = .bar20 ∨ d'.c.site = .waitO ∨ d'.c.site = .ldO)
    (hv : (d'.c.site = .bar20 → d'.v.m = Lib.mNext (scaleW L) d.v.m d.v.mx) ∧
      (d'.c.site ≠ .bar20 → d'.v.main d.v)) :
    (∀ t', Relation.ReflTransGen (Tau kernel Assumptions.all L g) u t' →
      Stops kernel Assumptions.all L g t' → Holds t'.regs (dF L d')) ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u :=
  goal_tab hscan (hseg_ivs hemu) (upd_spec hiv d.v.m d.v.mx) hu hT (q := d'.c.site.pc)
    (stops_pc hat hi hc hf hn) (fun _ => conv_succ hd hv)

theorem data_waitStO {d : D} (hs : d.c.site = .waitStO) : DataStep (code e L g) (dF L) d := by
  have pc : (code e L g).pc d = 2329 := by
    change d.c.site.pc = 2329
    rw [hs]
    rfl
  intro t ev u d' ins hat hi hc' hf hn
  rw [pc] at hc' hf
  rw [Flow.code_tmemWait_3] at hc'
  obtain rfl := Option.some.inj hc'
  obtain rfl := fires_tcWaitSt_next hf
  have hn' := hn
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  have hreg : Holds t.regs (dFS L d.c.site d.v) := atD_dF hat
  have hr : inRound d.c.site = true := by rw [hs]; rfl
  have hpc : (PTX.next t).pc = 2330 := by
    have h1 := hat.1
    simp only [PTX.next]
    omega
  refine cross_step (ivs := [(949, 50), (2330, 3)]) hat hi (by rw [pc]; exact Flow.code_tmemWait_3)
    (by rw [pc]; exact hf) hn' (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [hpc]; decide +kernel) ?_ (.inl rfl) (hv_cross (.inr (.inr hs)) rfl)
  exact tab_of hr d.v hreg (hat.2.1.trans rfl) (hat.2.2.1.trans rfl) hpc (by decide)
    (fun r _ => rfl)

theorem data_shfl6 {d : D} (hs : d.c.site = .shfl6) : DataStep (code e L g) (dF L) d := by
  have pc : (code e L g).pc d = 2234 := by
    change d.c.site.pc = 2234
    rw [hs]
    rfl
  intro t ev u d' ins hat hi hc' hf hn
  rw [pc] at hc' hf
  rw [Flow.code_shfl_6] at hc'
  obtain rfl := Option.some.inj hc'
  obtain ⟨sent, bv, cv, recv, ok, rfl, hu⟩ := fires_shfl (p := none) hf
  simp only [Option.elim] at hu
  subst hu
  have hn' := hn
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  have hreg : Holds t.regs (dFS L d.c.site d.v) := atD_dF hat
  have hr : inRound d.c.site = true := by rw [hs]; rfl
  have hpc : (PTX.next (setReg t 1530 recv)).pc = 2235 := by
    have h1 := hat.1
    simp only [PTX.next, setReg]
    omega
  refine cross_step (ivs := [(949, 50), (2235, 4)]) hat hi (by rw [pc]; exact Flow.code_shfl_6)
    (by rw [pc]; exact hf) hn' (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [hpc]; decide +kernel) ?_ ?_ ?_
  · refine tab_of hr d.v hreg (hat.2.1.trans rfl) (hat.2.2.1.trans rfl) hpc (by decide) ?_
    intro r hr'
    simp only [PTX.next, setReg]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rw [Function.update_of_ne (by omega)]
  · split <;> simp
  · exact hv_cross (.inl hs) rfl


theorem data_shfl12 {d : D} (hs : d.c.site = .shfl12) : DataStep (code e L g) (dF L) d := by
  have pc : (code e L g).pc d = 2255 := by
    change d.c.site.pc = 2255
    rw [hs]
    rfl
  intro t ev u d' ins hat hi hc' hf hn
  rw [pc] at hc' hf
  rw [Flow.code_shfl_12] at hc'
  obtain rfl := Option.some.inj hc'
  obtain ⟨sent, bv, cv, recv, ok, rfl, hu⟩ := fires_shfl (p := none) hf
  simp only [Option.elim] at hu
  subst hu
  have hn' := hn
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  have hreg : Holds t.regs (dFS L d.c.site d.v) := atD_dF hat
  have hr : inRound d.c.site = true := by rw [hs]; rfl
  have hpc : (PTX.next (setReg t 1545 recv)).pc = 2256 := by
    have h1 := hat.1
    simp only [PTX.next, setReg]
    omega
  refine cross_step (ivs := [(949, 50), (2256, 4)]) hat hi (by rw [pc]; exact Flow.code_shfl_12)
    (by rw [pc]; exact hf) hn' (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [hpc]; decide +kernel) ?_ ?_ ?_
  · refine tab_of hr d.v hreg (hat.2.1.trans rfl) (hat.2.2.1.trans rfl) hpc (by decide) ?_
    intro r hr'
    simp only [PTX.next, setReg]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rw [Function.update_of_ne (by omega)]
  · split <;> simp
  · exact hv_cross (.inr (.inl hs)) rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
