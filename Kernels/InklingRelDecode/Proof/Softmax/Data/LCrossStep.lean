-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.LCross
import Kernels.InklingRelDecode.Proof.Lib.ShuffleOperand
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The data steps of the three events that leave the round, for the running sum -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Assumption Control Lib

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- Where the successor's running-sum facts come from, by the successor's site. -/
theorem lconv_succ {d d' : D} {a s r p : Value}
    (hd : d'.c.site = .bar20 ∨ d'.c.site = .waitO ∨ d'.c.site = .ldO)
    (hv : (d'.c.site = .bar20 → d'.v.l = lStep d.v.l a p) ∧
      (d'.c.site ≠ .bar20 → d'.v.l = d.v.l ∧ d'.v.ps = p)) {R : Nat → Option Value}
    (h : Holds R (phi lUKeys lUPost (lUV1 d.v.l a s r p) (lUV2 d.v.l a s r p) d'.c.site.pc)) :
    Holds R (lF d') := by
  rcases hd with h1 | h1 | h1
  · rw [h1] at h
    change Holds R (factsFrom [1915] (lUV2 d.v.l a s r p)) at h
    have := holds_mem h (mem_factsFrom (val := lUV2 d.v.l a s r p) (r := 1915) (by simp))
    simp only [lF, lFS, h1, psB, Bool.false_eq_true, ↓reduceIte, lUV2, ↓reduceIte] at this ⊢
    exact ⟨this.trans (by rw [(hv.1 h1)]), trivial⟩
  all_goals
    rw [h1] at h
    change Holds R (factsFrom [1915, 507, 1531] (lUV1 d.v.l a s r p)) at h
    obtain ⟨hl, hp⟩ := hv.2 (by rw [h1]; decide)
    have e1 := holds_mem h (mem_factsFrom (val := lUV1 d.v.l a s r p) (r := 1915) (by simp))
    have e2 := holds_mem h (mem_factsFrom (val := lUV1 d.v.l a s r p) (r := 1531) (by simp))
    simp only [lUV1, ↓reduceIte, show (1531 = 1915) = False by decide,
      show (1531 = 507) = False by decide, show (1531 = 1529) = False by decide,
      show (1531 = 1530) = False by decide] at e1 e2
    simp only [lF, lFS, h1, psB, ↓reduceIte]
    exact ⟨e1.trans (by rw [hl]), e2.trans (by rw [hp]), trivial⟩

theorem lrec_cross {d : D} {ev : Event} {z : Site} {q : Value}
    (hs : d.c.site = .shfl6 ∨ d.c.site = .shfl12 ∨ d.c.site = .waitStO)
    (hq : q = if d.c.site = .shfl6 then psOf ev.kind d.v.ps else d.v.ps) :
    (z = .bar20 → (record L d ev z).l = lStep d.v.l (alphaVal (scaleW L) d.v.m d.v.mx 507) q) ∧
      (z ≠ .bar20 → (record L d ev z).l = d.v.l ∧ (record L d ev z).ps = q) := by
  subst hq
  unfold record
  rcases hs with h | h | h <;> rw [h] <;> constructor <;> intro hz <;> simp [hz]

/-- **The data step of an event that leaves the round**, from the state after it. -/
theorem lcross_step {d d' : D} {t u : TState} {ev : Event} {ins : Instr}
    {ivs : List (Nat × Nat)} {a s r p : Value}
    (hat : (code e L g).AtD d t) (hi : (code e L g).inv d)
    (hc : kernel.code[(code e L g).pc d]? = some ins)
    (hf : Fires ((code e L g).pc d) (eventTmpl Assumptions.all L g t ins.op) ev (some u))
    (hn : (code e L g).next d ev = some (some d'))
    (hscan : tabScan kernel ivs lUKeys lUPost lUSpec = true)
    (hemu : ((pcsOf ivs).all fun pc => !Assumptions.emuSites.contains pc) = true)
    (h950 : inIvs ivs 950 = true → inIvs ivs 951 = true)
    (h2235 : inIvs ivs 2235 = true → inIvs ivs 2236 = true ∧ p = psWord s r)
    (hu : (inIvs ivs u.pc || evAtB kernel u.pc) = true)
    (hT : TabAt lUKeys lUPost (lUV1 d.v.l a s r p) (lUV2 d.v.l a s r p) u)
    (hd : d'.c.site = .bar20 ∨ d'.c.site = .waitO ∨ d'.c.site = .ldO)
    (hv : (d'.c.site = .bar20 → d'.v.l = lStep d.v.l a p) ∧
      (d'.c.site ≠ .bar20 → d'.v.l = d.v.l ∧ d'.v.ps = p)) :
    (∀ t', Relation.ReflTransGen (Tau kernel Assumptions.all L g) u t' →
      Stops kernel Assumptions.all L g t' → Holds t'.regs (lF d')) ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u :=
  goal_tab hscan (hseg_ivs hemu) (lu_spec (L := L) (g := g) d.v.l a s r p h950 h2235) hu hT
    (q := d'.c.site.pc) (stops_pc hat hi hc hf hn) (fun _ => lconv_succ hd hv)

theorem lat_facts {d : D} {t : TState} (hat : (codeS e L g).AtD d t) : Holds t.regs (lF d) := by
  obtain ⟨-, -, -, -, r⟩ := hat
  exact atS_lF r

theorem regs_next_set (t : TState) (x : Nat) (v : Value) (r : Nat) :
    (PTX.next (setReg t x v)).regs r = if r = x then some v else t.regs r := by
  simp [PTX.next, setReg, Function.update]

/-- The running sum, the factor and the row sum's operands hold after the shuffle of pc 2234. -/
theorem lstart {d : D} {t : TState} (hat : (codeS e L g).AtD d t)
    (hs : d.c.site = .shfl6 ∨ d.c.site = .shfl12 ∨ d.c.site = .waitStO) :
    t.regs 1915 = some d.v.l ∧ t.regs 507 = some (alphaVal (scaleW L) d.v.m d.v.mx 507) := by
  have h1 := lat_facts hat
  have h2 : Holds t.regs (dFS L d.c.site d.v) := atD_dF (atS_code hat)
  rcases hs with h | h | h <;> simp only [lF, h] at h1 <;> rw [h] at h2
  all_goals
    refine ⟨holds_mem h1 (by simp [lFS]), holds_mem h2 ?_⟩
    simp [dFS, inRound, alphaFacts]

/-- **The running sum after the shuffle of pc 2234.** -/
theorem l_shfl6 {d : D} (hs : d.c.site = .shfl6) : DataStep (codeS e L g) lF d := by
  have pc : (codeS e L g).pc d = 2234 := by
    change d.c.site.pc = 2234
    rw [hs]
    rfl
  have pc0 : (code e L g).pc d = 2234 := pc
  intro t ev u d' ins hat hi hc' hf hn
  have hat0 := atS_code hat
  have hn' : (code e L g).next d ev = some (some d') := hn
  rw [pc] at hc' hf
  rw [Flow.code_shfl_6] at hc'
  obtain rfl := Option.some.inj hc'
  have hf0 := hf
  obtain ⟨sent, bv, cv, recv, ok, rfl, hu⟩ := fires_shfl (p := none) hf
  simp only [Option.elim] at hu
  subst hu
  obtain ⟨same, -, -, -⟩ := Lib.shfl_operand (src := 1529) (dst := 1530) (n := 16)
    (m := (16 : Nat)) (bv := 16) rfl rfl hf0 rfl
  obtain ⟨hl, ha⟩ := lstart hat (.inl hs)
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn'
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  have hpc : (PTX.next (setReg t 1530 recv)).pc = 2235 := by
    have h1 := hat.1
    simp only [PTX.next, setReg]
    omega
  refine lcross_step (ivs := [(949, 50), (2235, 4)]) (a := alphaVal (scaleW L) d.v.m d.v.mx 507)
    (s := sent) (r := recv) (p := psWord sent recv) hat0 hi (by rw [pc0]; exact Flow.code_shfl_6)
    (by rw [pc0]; exact hf) hn' (by decide +kernel) (by decide +kernel) (fun _ => by decide +kernel)
    (fun _ => ⟨by decide +kernel, rfl⟩) (by rw [hpc]; decide +kernel) ?_ ?_ ?_
  · refine ⟨hat.2.1.trans rfl, hat.2.2.1.trans rfl, ?_⟩
    rw [hpc]
    change Holds _ (factsFrom [1915, 507, 1529, 1530] _)
    refine holds_of_pointwise fun x hx => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [regs_next_set]
    have hup : lUPost 2235 = false := by decide
    rcases hx with rfl | rfl | rfl | rfl <;> simp [hup, lUV1, hl, ha, same]
  · split <;> simp
  · exact lrec_cross (hs := .inl hs) (q := psWord sent recv) (by simp [hs, psOf])

/-- The running sum, the factor and the row sum hold at the shuffle of pc 2255 and the wait of
pc 2329. -/
theorem lstart2 {d : D} {t : TState} (hat : (codeS e L g).AtD d t)
    (hs : d.c.site = .shfl12 ∨ d.c.site = .waitStO) :
    t.regs 1915 = some d.v.l ∧ t.regs 507 = some (alphaVal (scaleW L) d.v.m d.v.mx 507) ∧
      t.regs 1531 = some d.v.ps := by
  have h1 := lat_facts hat
  have h2 : Holds t.regs (dFS L d.c.site d.v) := atD_dF (atS_code hat)
  rcases hs with h | h <;> simp only [lF, h] at h1 <;> rw [h] at h2
  all_goals
    refine ⟨holds_mem h1 (by simp [lFS]), holds_mem h2 ?_, holds_mem h1 (by simp [lFS, psB])⟩
    simp [dFS, inRound, alphaFacts]

theorem ltab2 {u : TState} {d : D} {pc : Nat} (hpc : u.pc = pc) (hk : lUKeys pc = [1915, 507, 1531])
    (hp : lUPost pc = false) (h1 : u.regs 1915 = some d.v.l)
    (h2 : u.regs 507 = some (alphaVal (scaleW L) d.v.m d.v.mx 507))
    (h3 : u.regs 1531 = some d.v.ps) (hsub : u.sub = 0) (hacc : u.acc = []) :
    TabAt lUKeys lUPost (lUV1 d.v.l (alphaVal (scaleW L) d.v.m d.v.mx 507) (b32 0) (b32 0) d.v.ps)
      (lUV2 d.v.l (alphaVal (scaleW L) d.v.m d.v.mx 507) (b32 0) (b32 0) d.v.ps) u := by
  refine ⟨hsub, hacc, ?_⟩
  unfold phi
  rw [hpc, hk, hp]
  refine holds_of_pointwise fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp [lUV1, h1, h2, h3]

/-- **The running sum after the shuffle of pc 2255.** -/
theorem l_shfl12 {d : D} (hs : d.c.site = .shfl12) : DataStep (codeS e L g) lF d := by
  have pc : (codeS e L g).pc d = 2255 := by
    change d.c.site.pc = 2255
    rw [hs]
    rfl
  have pc0 : (code e L g).pc d = 2255 := pc
  intro t ev u d' ins hat hi hc' hf hn
  have hat0 := atS_code hat
  have hn' : (code e L g).next d ev = some (some d') := hn
  rw [pc] at hc' hf
  rw [Flow.code_shfl_12] at hc'
  obtain rfl := Option.some.inj hc'
  obtain ⟨sent, bv, cv, recv, ok, rfl, hu⟩ := fires_shfl (p := none) hf
  simp only [Option.elim] at hu
  subst hu
  obtain ⟨hl, ha, hp⟩ := lstart2 hat (.inl hs)
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn'
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  have hpc : (PTX.next (setReg t 1545 recv)).pc = 2256 := by
    have h1 := hat.1
    simp only [PTX.next, setReg]
    omega
  refine lcross_step (ivs := [(949, 50), (2256, 4)]) (a := alphaVal (scaleW L) d.v.m d.v.mx 507)
    (s := b32 0) (r := b32 0) (p := d.v.ps) hat0 hi (by rw [pc0]; exact Flow.code_shfl_12)
    (by rw [pc0]; exact hf) hn' (by decide +kernel) (by decide +kernel)
    (fun _ => by decide +kernel) (fun h => absurd h (by decide +kernel))
    (by rw [hpc]; decide +kernel) ?_ ?_ ?_
  · refine ltab2 hpc (by decide) (by decide) ?_ ?_ ?_ (hat.2.1.trans rfl) (hat.2.2.1.trans rfl)
    exacts [by simpa [regs_next_set] using hl, by simpa [regs_next_set] using ha,
      by simpa [regs_next_set] using hp]
  · split <;> simp
  · exact lrec_cross (hs := .inr (.inl hs)) (q := d.v.ps) (by simp [hs])

/-- **The running sum after the wait of pc 2329.** -/
theorem l_waitStO {d : D} (hs : d.c.site = .waitStO) : DataStep (codeS e L g) lF d := by
  have pc : (codeS e L g).pc d = 2329 := by
    change d.c.site.pc = 2329
    rw [hs]
    rfl
  have pc0 : (code e L g).pc d = 2329 := pc
  intro t ev u d' ins hat hi hc' hf hn
  have hat0 := atS_code hat
  have hn' : (code e L g).next d ev = some (some d') := hn
  rw [pc] at hc' hf
  rw [Flow.code_tmemWait_3] at hc'
  obtain rfl := Option.some.inj hc'
  obtain rfl := fires_tcWaitSt_next hf
  obtain ⟨hl, ha, hp⟩ := lstart2 hat (.inr hs)
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn'
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  have hpc : (PTX.next t).pc = 2330 := by
    have h1 := hat.1
    simp only [PTX.next]
    omega
  refine lcross_step (ivs := [(949, 50), (2330, 3)]) (a := alphaVal (scaleW L) d.v.m d.v.mx 507)
    (s := b32 0) (r := b32 0) (p := d.v.ps) hat0 hi (by rw [pc0]; exact Flow.code_tmemWait_3)
    (by rw [pc0]; exact hf) hn' (by decide +kernel) (by decide +kernel)
    (fun _ => by decide +kernel) (fun h => absurd h (by decide +kernel))
    (by rw [hpc]; decide +kernel) ?_ (.inl rfl) ?_
  · exact ltab2 hpc (by decide) (by decide) hl ha hp (hat.2.1.trans rfl) (hat.2.2.1.trans rfl)
  · exact lrec_cross (hs := .inr (.inr hs)) (q := d.v.ps) (by simp [hs])

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
