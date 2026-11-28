-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpFam
public import Kernels.InklingRelDecode.Proof.Softmax.Data.TabGoal
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Cross
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Stop
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The exponent window's facts across the update

From the shuffles of pcs 2234 and 2255 and the wait of pc 2329 the thread runs to the next event of
the round or, through the update of pc 949, to the barrier of pc 999. The exponentials' facts
hold by position (the table `xtKeys`); the pack of pcs 951 to 998 is a jump of the table whose
facts at the barrier are the pack's words and the singles. After the barrier the second pack
(pcs 1000 to 1007) is a jump to the store. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The registers of the facts by position: the exponentials, at the barrier the pack's words. -/
def xtKeys (pc : Nat) : List Nat := if pc = 999 then kB20 else xKeys
def xtPost (pc : Nat) : Bool := decide (pc = 999)
def xtSpec (pc : Nat) : Bool := decide (pc = 951)

/-- The tables' facts after the barrier: the singles, at the store the 32 words. -/
def ytKeys (pc : Nat) : List Nat := if 1008 ≤ pc then kTm else kB20
def ytPost (pc : Nat) : Bool := decide (1008 ≤ pc)
def ytSpec (pc : Nat) : Bool := decide (pc = 1000)

theorem ev_999 : evAtB kernel 999 = true := by decide +kernel

theorem xt_jump {ivs : List (Nat × Nat)} (W : Nat → Value) :
    ∀ pc, xtSpec pc = true → inIvs ivs pc = true → ∀ t : TState, t.pc = pc → t.fault = none →
      TabAt xtKeys xtPost W (vP1 W) t →
      (∃ w, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t w ∧ t ≠ w ∧
        TabGood kernel ivs xtKeys xtPost W (vP1 W) w) ∨
        Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) t := by
  intro pc hsp hin t hpc hf hT
  have h : pc = 951 := by simpa [xtSpec] using hsp
  subst h
  refine jump_segU (pk1_seg (K := xKeys) (by decide +kernel) W) (by decide) (by simp [ev_999])
    (fun R hR => ?_) (fun R hR => ?_) t hpc hf hT
  · simpa [phi, xtKeys, xtPost] using hR
  · exact holds_factsFrom_mono hR (by decide +kernel)

theorem yt_jump {ivs : List (Nat × Nat)} (h8 : inIvs ivs 1008 = true) (W : Nat → Value) :
    ∀ pc, ytSpec pc = true → inIvs ivs pc = true → ∀ t : TState, t.pc = pc → t.fault = none →
      TabAt ytKeys ytPost (vP1 W) (vP2 (vP1 W)) t →
      (∃ w, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t w ∧ t ≠ w ∧
        TabGood kernel ivs ytKeys ytPost (vP1 W) (vP2 (vP1 W)) w) ∨
        Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) t := by
  intro pc hsp hin t hpc hf hT
  have h : pc = 1000 := by simpa [ytSpec] using hsp
  subst h
  refine jump_segU (pk2_seg (K := kB20) (by decide +kernel) (vP1 W)) (by decide) (by simp [h8])
    (fun R hR => ?_) (fun R hR => ?_) t hpc hf hT
  · simpa [phi, ytKeys, ytPost] using hR
  · exact holds_factsFrom_mono hR (by decide +kernel)

theorem xt_scan1 : tabScan kernel [(949, 3), (2235, 4)] xtKeys xtPost xtSpec = true := by
  decide +kernel
theorem xt_scan2 : tabScan kernel [(949, 3), (2256, 4)] xtKeys xtPost xtSpec = true := by
  decide +kernel
theorem xt_scan3 : tabScan kernel [(949, 3), (2330, 3)] xtKeys xtPost xtSpec = true := by
  decide +kernel
theorem yt_scan : tabScan kernel [(1000, 1), (1008, 2)] ytKeys ytPost ytSpec = true := by
  decide +kernel

theorem xV_cross {d : D} {ev : Event} {c' : Control.D}
    (hs : d.c.site = .shfl6 ∨ d.c.site = .shfl12 ∨ d.c.site = .waitStO)
    (hnc : Control.next e L g d.c ev = some (some c'))
    (hz : c'.site = .bar20 ∨ c'.site = .waitO ∨ c'.site = .ldO) :
    xV e L g ⟨c', record L d ev c'.site⟩ = xV e L g d := by
  have hb : d.c.site ≠ .bar21 ∧ d.c.site ≠ .arrive := by rcases hs with h | h | h <;> simp [h]
  refine (xV_congr ?_ ?_ (next_i hnc hb.1 hb.2).symm ?_ ?_ ?_).symm
  all_goals rcases hs with h | h | h <;> rcases hz with hz | hz | hz <;>
    simp [m0, record, h, hz]

theorem x_tab {t u : TState} {d : D} (hat : (codeS e L g).AtD d t) (hs : inRound d.c.site = true)
    (hE : ExpIn (xV e L g d)) (hsub : u.sub = 0) (hacc : u.acc = [])
    (hk : ∀ r ∈ xKeys, u.regs r = t.regs r) {pc : Nat} (hpc : u.pc = pc) (hp : pc ≠ 999) :
    TabAt xtKeys xtPost (xE e L g d) (vP1 (xE e L g d)) u := by
  refine ⟨hsub, hacc, ?_⟩
  obtain ⟨-, -, -, -, hreg⟩ := id hat
  have hF := atS_xF hreg
  simp only [xF, xF0, hE, hs, ite_true] at hF
  rw [hpc]
  refine holds_of_pointwise fun r hr => ?_
  simp only [xtKeys, xtPost, hp, decide_false, ite_false, Bool.false_eq_true] at hr ⊢
  rw [hk r hr]
  exact holds_mem hF (mem_factsFrom hr)

open Classical in
/-- **The exponent window's facts after an event that leaves the round**, from the table. -/
theorem x_cross {d d' : D} {t u : TState} {ev : Event} {ins : Instr} {ivs : List (Nat × Nat)}
    (hat : (codeS e L g).AtD d t) (hi : (codeS e L g).inv d)
    (hc : kernel.code[(codeS e L g).pc d]? = some ins)
    (hf : Fires ((codeS e L g).pc d) (eventTmpl Assumptions.all L g t ins.op) ev (some u))
    (hn : (codeS e L g).next d ev = some (some d')) (hs : inRound d.c.site = true)
    (hscan : tabScan kernel ivs xtKeys xtPost xtSpec = true)
    (hemu : ((pcsOf ivs).all fun pc => !Assumptions.emuSites.contains pc) = true)
    (hu : (inIvs ivs u.pc || evAtB kernel u.pc) = true) (hsub : u.sub = 0) (hacc : u.acc = [])
    (hk : ∀ r ∈ xKeys, u.regs r = t.regs r) (hp : u.pc ≠ 999)
    (hx : xV e L g d' = xV e L g d)
    (hd : d'.c.site = .bar20 ∨ d'.c.site = .waitO ∨ d'.c.site = .ldO) :
    (∀ t', Relation.ReflTransGen (Tau kernel Assumptions.all L g) u t' →
      Stops kernel Assumptions.all L g t' → Holds t'.regs (xF e L g d')) ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u := by
  by_cases hE : ExpIn (xV e L g d)
  · have hE' : ExpIn (xV e L g d') := by rw [hx]; exact hE
    refine goal_tabJ hscan (hseg_ivs hemu) (xt_jump (ivs := ivs) _)
      ⟨hu, x_tab hat hs hE hsub hacc hk rfl hp⟩ (stops_pc (atS_code hat) hi hc hf hn)
      (fun R h => ?_)
    have hq : (code e L g).pc d' = d'.c.site.pc := rfl
    have hxe : xE e L g d' = xE e L g d := by simp only [xE, hx]
    rw [hq] at h
    have hkn : ∀ pc, pc ≠ 999 → phi xtKeys xtPost (xE e L g d) (vP1 (xE e L g d)) pc =
        factsFrom xKeys (xE e L g d) := fun pc hp => by simp [phi, xtKeys, xtPost, hp]
    rcases hd with hd | hd | hd
    · have e1 : d'.c.site.pc = 999 := by rw [hd]; rfl
      have e2 : phi xtKeys xtPost (xE e L g d) (vP1 (xE e L g d)) 999 =
          factsFrom kB20 (vP1 (xE e L g d)) := by simp [phi, xtKeys, xtPost]
      rw [e1, e2] at h
      rw [xF_bar20 hd hE', hxe]
      exact h
    all_goals
      have e1 : d'.c.site.pc ≠ 999 := by rw [hd]; decide
      rw [hkn _ e1] at h
      rw [xF_round (by rw [hd]; rfl) hE', hxe]
      exact h
  · exact .inl fun _ _ _ => by rw [xF_no (by rw [hx]; exact hE)]; trivial

theorem xKeys_ne : ∀ r ∈ xKeys, r ≠ 1530 ∧ r ≠ 1545 := by decide +kernel

theorem xV_bar20 {d : D} {ev : Event} {c' : Control.D} (hs : d.c.site = .bar20)
    (hnc : Control.next e L g d.c ev = some (some c')) (hz : c'.site = .tmemSt) :
    xV e L g ⟨c', record L d ev c'.site⟩ = xV e L g d := by
  have hp : plainX d.c.site = true := by rw [hs]; rfl
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := record_x (L := L) (d := d) ev c'.site hp
  refine (xV_congr ?_ r2.symm (next_i hnc (by simp [hs]) (by simp [hs])).symm r4.symm r5.symm
    r6.symm).symm
  simp only [m0, hs, hz, true_or, or_true, ite_true]
  rw [hz] at r3
  exact r3.symm

theorem shfl_keep {t u : TState} {pc rr : Nat} {ty : Option DType} {a b c mask : Opnd}
    {ev : Event}
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.warp ⟨.shfl .bfly, ty, [some rr], [a, b, c], some mask⟩)) ev (some u))
    (hr : ∀ r ∈ xKeys, r ≠ rr) :
    u.pc = t.pc + 1 ∧ u.sub = t.sub ∧ u.acc = t.acc ∧ ∀ r ∈ xKeys, u.regs r = t.regs r := by
  obtain ⟨-, -, -, recv, ok, -, hu⟩ := fires_shfl (p := none) hf
  simp only [Option.elim] at hu
  subst hu
  exact ⟨rfl, rfl, rfl, fun r h => by
    simp only [PTX.next, setReg]
    rw [Function.update_of_ne (hr r h)]⟩

/-- **A site of the update crossing**: the event keeps the exponentials and the code after it is
the table's region. -/
theorem x_ev {d : D} {pc : Nat} {op : Op} {ivs : List (Nat × Nat)}
    (hpc : (codeS e L g).pc d = pc) (hc : kernel.code[pc]? = some ⟨none, op⟩)
    (hs : d.c.site = .shfl6 ∨ d.c.site = .shfl12 ∨ d.c.site = .waitStO)
    (hz : ∀ ev c', Control.next e L g d.c ev = some (some c') →
      c'.site = .bar20 ∨ c'.site = .waitO ∨ c'.site = .ldO)
    (hu : ∀ t ev u, Fires pc (eventTmpl Assumptions.all L g t op) ev (some u) →
      u.pc = t.pc + 1 ∧ u.sub = t.sub ∧ u.acc = t.acc ∧ ∀ r ∈ xKeys, u.regs r = t.regs r)
    (hscan : tabScan kernel ivs xtKeys xtPost xtSpec = true)
    (hemu : ((pcsOf ivs).all fun pc => !Assumptions.emuSites.contains pc) = true)
    (hnext : (inIvs ivs (pc + 1) || evAtB kernel (pc + 1)) = true) (hne : pc + 1 ≠ 999) :
    DataStep (codeS e L g) (xF e L g) d := by
  intro t ev u d' ins hat hi hc' hf hn
  have hin : inRound d.c.site = true := by rcases hs with h | h | h <;> rw [h] <;> rfl
  have hc2 : kernel.code[(codeS e L g).pc d]? = some ⟨none, op⟩ := by rw [hpc]; exact hc
  obtain rfl := Option.some.inj (hc'.symm.trans hc2)
  have hf2 := hf
  rw [hpc] at hf2
  obtain ⟨hp, hsub, hacc, hk⟩ := hu t ev u hf2
  obtain ⟨hatpc, hatsub, hatacc, -, -⟩ := id hat
  have hn' := hn
  obtain ⟨c', hnc, hd'⟩ := succ_inv hn
  have hx : xV e L g d' = xV e L g d := by
    rw [hd']
    exact xV_cross hs hnc (hz ev c' hnc)
  refine x_cross hat hi hc2 hf hn' hin hscan hemu ?_ (hsub.trans hatsub) (hacc.trans hatacc) hk
    ?_ hx (by rw [hd']; exact hz ev c' hnc)
  · rw [hp, hatpc, hpc]
    exact hnext
  · rw [hp, hatpc, hpc]
    exact hne

/-- **The exponentials' facts after the shuffle of pc 2234.** -/
theorem x_shfl6 {d : D} (hs : d.c.site = .shfl6) : DataStep (codeS e L g) (xF e L g) d :=
  x_ev (pc := 2234) (ivs := [(949, 3), (2235, 4)]) (by change d.c.site.pc = 2234; rw [hs]; rfl)
    Flow.code_shfl_6 (.inl hs)
    (fun ev c' h => by
      simp only [Control.next, hs, Option.some.injEq] at h
      subst h
      split <;> simp)
    (fun _ _ _ hf => shfl_keep hf fun r h => (xKeys_ne r h).1) xt_scan1 (by decide +kernel)
    (by decide +kernel) (by decide)

/-- **The exponentials' facts after the shuffle of pc 2255.** -/
theorem x_shfl12 {d : D} (hs : d.c.site = .shfl12) : DataStep (codeS e L g) (xF e L g) d :=
  x_ev (pc := 2255) (ivs := [(949, 3), (2256, 4)]) (by change d.c.site.pc = 2255; rw [hs]; rfl)
    Flow.code_shfl_12 (.inr (.inl hs))
    (fun ev c' h => by
      obtain ⟨pc0, kind⟩ := ev
      cases kind <;> simp only [Control.next, hs, reduceCtorEq, Option.some.injEq] at h
      subst h
      split <;> simp)
    (fun _ _ _ hf => shfl_keep hf fun r h => (xKeys_ne r h).2) xt_scan2 (by decide +kernel)
    (by decide +kernel) (by decide)

/-- **The exponentials' facts after the wait of pc 2329.** -/
theorem x_waitStO {d : D} (hs : d.c.site = .waitStO) : DataStep (codeS e L g) (xF e L g) d :=
  x_ev (pc := 2329) (ivs := [(949, 3), (2330, 3)]) (by change d.c.site.pc = 2329; rw [hs]; rfl)
    Flow.code_tmemWait_3 (.inr (.inr hs))
    (fun ev c' h => by
      simp only [Control.next, hs, Option.some.injEq] at h
      subst h
      simp)
    (fun t ev u hf => by
      obtain rfl := fires_tcWaitSt_next hf
      exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩)
    xt_scan3 (by decide +kernel) (by decide +kernel) (by decide)

/-- **The pack's words after the barrier of pc 999.** -/
theorem x_bar20 {d : D} (hs : d.c.site = .bar20) : DataStep (codeS e L g) (xF e L g) d := by
  have pc : (codeS e L g).pc d = 999 := by
    change d.c.site.pc = 999
    rw [hs]
    rfl
  intro t ev u d' ins hat hi hc' hf hn
  rw [pc] at hc' hf
  rw [Flow.code_bar_20] at hc'
  obtain rfl := Option.some.inj hc'
  obtain rfl := Option.some.inj hf.2
  have hn' := hn
  obtain ⟨c', hnc, hd'⟩ := succ_inv hn
  have hnc0 := hnc
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  have hsite : d'.c.site = .tmemSt := by rw [hd']
  have hx : xV e L g d' = xV e L g d := by rw [hd']; exact xV_bar20 hs hnc0 rfl
  by_cases hE : ExpIn (xV e L g d)
  · have hE' : ExpIn (xV e L g d') := by rw [hx]; exact hE
    have hpc : (PTX.next t).pc = 1000 := by
      have h1 := hat.1
      simp only [PTX.next]
      omega
    obtain ⟨-, -, -, -, hreg⟩ := id hat
    have hF := atS_xF hreg
    rw [xF_bar20 hs hE] at hF
    refine goal_tabJ (ivs := [(1000, 1), (1008, 2)]) (V1 := vP1 (xE e L g d))
      (V2 := vP2 (vP1 (xE e L g d))) yt_scan (hseg_ivs (by decide +kernel))
      (yt_jump (by decide +kernel) _)
      ⟨by rw [hpc]; decide +kernel, hat.2.1.trans rfl, hat.2.2.1.trans rfl, ?_⟩
      (stops_pc (atS_code hat) hi (by rw [pc]; exact Flow.code_bar_20) (by rw [pc]; exact hf)
        hn') (fun R h => ?_)
    · have e : phi ytKeys ytPost (vP1 (xE e L g d)) (vP2 (vP1 (xE e L g d))) 1000 =
          factsFrom kB20 (vP1 (xE e L g d)) := by simp [phi, ytKeys, ytPost]
      rw [hpc, e]
      exact hF
    · have hq : (code e L g).pc d' = 1009 := by
        change d'.c.site.pc = 1009
        rw [hsite]
        rfl
      rw [hq] at h
      rw [xF_tmemSt hsite hE', show xE e L g d' = xE e L g d by simp only [xE, hx]]
      simpa [phi, ytKeys, ytPost] using h
  · refine .inl fun _ _ _ => ?_
    rw [xF_no (by rw [hx]; exact hE)]
    trivial

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
