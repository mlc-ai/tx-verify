-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmStgC
public import Lemmas.Flow.LoadSharedSize

@[expose] public section

/-! # The sites of the row sum's exchange that only advance (pcs 2241 to 2252)

The named barriers `bar22` (pc 2241) and `bar23` (pc 2251) and the shared store `store10`
(pc 2250) continue at the next instruction, and the machine's next state has the same table. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Classical

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

theorem live_2242_2241 : ∀ r ∈ Flow.live 2242, r ∈ Flow.live 2241 := by decide +kernel
theorem live_2251_2250 : ∀ r ∈ Flow.live 2251, r ∈ Flow.live 2250 := by decide +kernel
theorem live_2252_2251 : ∀ r ∈ Flow.live 2252, r ∈ Flow.live 2251 := by decide +kernel

/-- **The named barrier after the row sum's exchange** (pc 2241). -/
theorem step_bar22 {d : D} {t u : TState} {e : Event} {ins : Instr} (hi : Inv L g d)
    (hs : d.site = .bar22) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2241 := by rw [hs]; rfl
  have hc' : kernel.code[2241]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_bar_22)
  exact step_adv (dn := { d with site := .shfl7 })
    (fun hf' => fires_async_next (show AsyncAdvancesOp (.barSyncN _ _ _) from trivial) hf')
    (by simp [next, hs]) (by rw [hpc]; rfl) rfl (by rw [hpc]; exact live_2242_2241)
    (inv_late hi (by rw [hs]; trivial) (s := .shfl7) trivial (fun h => absurd h (by simp))) h hf

/-- **The named barrier before the load of the minima** (pc 2251). -/
theorem step_bar23 {d : D} {t u : TState} {e : Event} {ins : Instr} (hi : Inv L g d)
    (hs : d.site = .bar23) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2251 := by rw [hs]; rfl
  have hc' : kernel.code[2251]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_bar_23)
  exact step_adv (dn := { d with site := .ldL })
    (fun hf' => fires_async_next (show AsyncAdvancesOp (.barSyncN _ _ _) from trivial) hf')
    (by simp [next, hs]) (by rw [hpc]; rfl) rfl (by rw [hpc]; exact live_2252_2251)
    (inv_late hi (by rw [hs]; trivial) (s := .ldL) trivial (fun h => absurd h (by simp))) h hf

/-- **The shared store of the minimum** (pc 2250). -/
theorem step_store10 {d : D} {t u : TState} {e : Event} {ins : Instr} (hi : Inv L g d)
    (hs : d.site = .store10) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2250 := by rw [hs]; rfl
  have hc' : kernel.code[2250]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_store_10)
  have h' : At t 2250 (factsAt L g 2250 d) := hpc ▸ h
  refine step_adv (dn := { d with site := .bar23 }) (fun hf' => ?_)
    (by simp [next, hs]) (by rw [hpc]; rfl) rfl (by rw [hpc]; exact live_2251_2250)
    (inv_late hi (by rw [hs]; trivial) (s := .bar23) trivial (fun h => absurd h (by simp))) h hf
  obtain ⟨r, bs, -, hu⟩ := fires_st (A := asms) (L := L) (g := g) (a := _) rfl hf'
  have hns : ¬ (t.sub + 1 < ([.reg 1534] : List Opnd).length) := by
    simp only [List.length_cons, List.length_nil]
    omega
  rw [hu]
  show afterStore t [.reg 1534] = PTX.next t
  rw [afterStore_last hns]
  simp [PTX.next, h'.2.1]


/-! ### The shuffles of the rescale test's minima

Each of `shfl7` to `shfl10` and `shfl11` (pcs 2242, 2244, 2246, 2248, 2253) receives the minimum of
another lane, and the next instruction takes the minimum with the thread's own
(`min.f32 dst, a, rv`); the machine records the new minimum in `Stg`. A minimum that has no
outcome faults the thread. -/

theorem valueOf_congrX {d d' : D} (h1 : d'.e = d.e) (h2 : d'.i = d.i) (h3 : d'.m = d.m)
    (h4 : d'.l = d.l) (hw : d'.wd = d.wd) (hv : d'.vd = d.vd) {r : Nat}
    (hX : (valuesX L g d').lookup r = (valuesX L g d).lookup r)
    (hb : d'.stg.bw = d.stg.bw := by rfl):
    valueOf L g d' r = valueOf L g d r := by
  have eS : valuesS L g d' = valuesS L g d := by simp only [valuesS, h1, h3, h4, hb]
  have eP : valuesP L g d' = valuesP L g d := by simp only [valuesP, h1]
  have eQ : valuesQ L g d' = valuesQ L g d := by simp only [valuesQ, h1]
  have eR : valuesR L g d' = valuesR L g d := by simp only [valuesR, D.n, h1, h2]
  have eI : valuesI L g d' = valuesI L g d := by simp only [valuesI, D.n, h1, h2, hb]
  have eW : valuesW d' = valuesW d := by simp only [valuesW, hw, hv]
  simp only [valueOf, values, lookup_append', eI, eS, eP, eQ, eR, eW, hX]

/-- `min.f32 dst, a, b` as a piece with a fault: the facts after it hold the outcome. -/
theorem segD_min {pc a b dst : Nat} {F : List (Nat × Value)} {va vb : Value}
    (hc : kernel.code[pc]? = some ⟨none, minOp dst [a, b]⟩)
    (hemu : Assumptions.emuSites.contains pc = false) (h1 : pc ≠ 2562) (h2 : pc ≠ 600)
    (h3 : pc ≠ 807) (ha : (a, va) ∈ F) (hb : (b, vb) ∈ F) (hd : ∀ p ∈ F, p.1 ≠ dst) :
    SegD kernel asms L g 1 pc F (pc + 1) ((dst, okVal (b32 0) (minE [va, vb])) :: F)
      ((minE [va, vb]).toBool = true) := by
  refine segD_setF (r := dst) (f := id) hc rfl ?_ hd ?_
  · intro t ht
    have hp : t.pc = pc := ht.1
    exact exec_minE2 (idealAtSm (Or.inr (Or.inl rfl)) (by rw [hp]; exact hemu))
      (declineAtSm (Or.inr (Or.inl rfl)) (by rw [hp]; exact hemu) (by rw [hp]; exact h1)
        (by rw [hp]; exact h2) (by rw [hp]; exact h3)) (holds_mem ht.2.2.2.2 ha)
      (holds_mem ht.2.2.2.2 hb)
  · intro x hx
    exact (okVal_of_ok hx).symm


variable {d : D} {t u : TState} {e : Event} {ins : Instr}

/-- **A shuffle of the minima and the minimum that follows it.** -/
theorem step_shflMin {s s' : Site} {pc rv a dst : Nat} {old : Value} {upd : Value → D}
    (hi : Inv L g d) (hs : d.site = s) (hpc : s.pc = pc) (hpc' : s'.pc = pc + 2)
    (hop : ∃ (ty : Option DType) (x y z mask : Opnd),
      ins.op = .warp ⟨.shfl .bfly, ty, [some rv], [x, y, z], some mask⟩)
    (hmin : kernel.code[pc + 1]? = some ⟨none, minOp dst [a, rv]⟩)
    (hemu : Assumptions.emuSites.contains (pc + 1) = false) (h1 : pc + 1 ≠ 2562) (h2 : pc + 1 ≠ 600)
    (h3 : pc + 1 ≠ 807) (hla : a ∈ Flow.live pc) (hold : valueOf L g d a = old)
    (hrv : rv ∉ Flow.live pc) (hdst : dst ∉ Flow.live pc) (hdr : dst ≠ rv)
    (hlive : ∀ r ∈ Flow.live (pc + 2), r = dst ∨ r ∈ Flow.live pc)
    (hn : ∀ av bv cv recv ok, next L g d ⟨pc, .shfl .bfly av bv cv recv ok⟩ =
      (match minE [old, recv] with | .ok v => some (some (upd v)) | .error _ => none))
    (hsite : ∀ v, (upd v).site = s') (hinv : ∀ v, v.bytes = 4 → Inv L g (upd v))
    (hval : ∀ v, valueOf L g (upd v) dst = v)
    (hfr : ∀ v r, r ≠ dst → valueOf L g (upd v) r = valueOf L g d r)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc0 : d.site.pc = pc := by rw [hs]; exact hpc
  obtain ⟨ty, x, y, z, mask, hop'⟩ := hop
  rw [hop'] at hf
  have hf' := hpc0 ▸ hf
  obtain ⟨av, bv, cv, recv, ok, rfl, hu⟩ := fires_shfl (p := none) hf'
  simp only [Option.elim] at hu
  subst hu
  have h' : At t pc (factsAt L g pc d) := hpc0 ▸ h
  have h1' := At.set (r := rv) (v := recv) h' (facts_ne hrv)
  have ha : (a, old) ∈ (rv, recv) :: factsAt L g pc d := by
    refine List.mem_cons_of_mem _ ?_
    have := Flow.mem_factsFrom (val := valueOf L g d) hla
    rwa [hold] at this
  have hb : (rv, recv) ∈ (rv, recv) :: factsAt L g pc d := List.mem_cons_self ..
  have hd : ∀ p ∈ (rv, recv) :: factsAt L g pc d, p.1 ≠ dst := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hdr.symm
    · exact facts_ne hdst p hp
  have hS := segD_min (L := L) (g := g) hmin hemu h1 h2 h3 ha hb hd
  rcases hE : minE [old, recv] with f | x'
  · have hn' : next L g d ⟨pc, .shfl .bfly av bv cv recv ok⟩ = none := by
      rw [hn]; simp [hE]
    exact .inr ⟨hn', (hS _ h1').2 (by simp [hE, Except.toBool])⟩
  · have hn' : next L g d ⟨pc, .shfl .bfly av bv cv recv ok⟩ = some (some (upd x')) := by
      rw [hn]; simp [hE]
    have pA : Seg kernel asms L g 1 (pc + 1) ((rv, recv) :: factsAt L g pc d) (pc + 1 + 1)
        ((dst, okVal (b32 0) (minE [old, recv])) :: (rv, recv) :: factsAt L g pc d) :=
      SegD.seg hS (by simp [hE, Except.toBool])
    rw [okVal_of_ok hE] at pA
    obtain ⟨t', hr, ht'⟩ := pA.rtg h1'
    have e : (upd x').site.pc = pc + 2 := by rw [hsite x']; exact hpc'
    have hat : At t' (upd x').site.pc (facts L g (upd x')) := by
      show At t' _ (factsAt L g (upd x').site.pc (upd x'))
      rw [e]
      refine ⟨ht'.1, ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, holds_of_pointwise fun r hr' => ?_⟩
      rcases hlive r hr' with rfl | hl
      · rw [hval x']
        exact holds_mem ht'.2.2.2.2 (List.mem_cons_self ..)
      · have hne : r ≠ dst := fun he => hdst (he ▸ hl)
        rw [hfr x' r hne]
        exact holds_mem ht'.2.2.2.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (Flow.mem_factsFrom (val := valueOf L g d) hl)))
    exact .inl (.inr ⟨upd x', t', hn', hr, hat, hinv x' (minE_four _ x' hE)⟩)


theorem valueOf_cm1 (d : D) : valueOf L g d 1536 = d.stg.cm1 := by
  rw [valueOf_X d (by unfold XKey; omega)]
  simp [valuesX, List.lookup]

theorem valueOf_cm2 (d : D) : valueOf L g d 1538 = d.stg.cm2 := by
  rw [valueOf_X d (by unfold XKey; omega)]
  simp [valuesX, List.lookup]

theorem valueOf_cm3 (d : D) : valueOf L g d 1540 = d.stg.cm3 := by
  rw [valueOf_X d (by unfold XKey; omega)]
  simp [valuesX, List.lookup]

theorem valueOf_cm4 (d : D) : valueOf L g d 1534 = d.stg.cm4 := by
  rw [valueOf_X d (by unfold XKey; omega)]
  simp [valuesX, List.lookup]

theorem valueOf_ld (d : D) : valueOf L g d 1542 = d.stg.ld := by
  rw [valueOf_X d (by unfold XKey; omega)]
  simp [valuesX, List.lookup]

theorem frame_cm1 (d : D) (s : Site) (v : Value) {r : Nat} (hr : r ≠ 1536) :
    valueOf L g { d with site := s, stg := { d.stg with cm1 := v } } r = valueOf L g d r := by
  have hb : (r == 1536) = false := by simpa using hr
  have hX : (valuesX L g { d with site := s, stg := { d.stg with cm1 := v } }).lookup r =
      (valuesX L g d).lookup r := by
    simp only [valuesX, valuesXt, D.pwV, D.pwE, lookup_append', List.lookup, hb]
  exact valueOf_congrX (d := d) (d' := { d with site := s, stg := { d.stg with cm1 := v } })
    rfl rfl rfl rfl rfl rfl hX

theorem frame_cm2 (d : D) (s : Site) (v : Value) {r : Nat} (hr : r ≠ 1538) :
    valueOf L g { d with site := s, stg := { d.stg with cm2 := v } } r = valueOf L g d r := by
  have hb : (r == 1538) = false := by simpa using hr
  have hX : (valuesX L g { d with site := s, stg := { d.stg with cm2 := v } }).lookup r =
      (valuesX L g d).lookup r := by
    simp only [valuesX, valuesXt, D.pwV, D.pwE, lookup_append', List.lookup, hb]
  exact valueOf_congrX (d := d) (d' := { d with site := s, stg := { d.stg with cm2 := v } })
    rfl rfl rfl rfl rfl rfl hX

theorem frame_cm3 (d : D) (s : Site) (v : Value) {r : Nat} (hr : r ≠ 1540) :
    valueOf L g { d with site := s, stg := { d.stg with cm3 := v } } r = valueOf L g d r := by
  have hb : (r == 1540) = false := by simpa using hr
  have hX : (valuesX L g { d with site := s, stg := { d.stg with cm3 := v } }).lookup r =
      (valuesX L g d).lookup r := by
    simp only [valuesX, valuesXt, D.pwV, D.pwE, lookup_append', List.lookup, hb]
  exact valueOf_congrX (d := d) (d' := { d with site := s, stg := { d.stg with cm3 := v } })
    rfl rfl rfl rfl rfl rfl hX

theorem frame_cm4 (d : D) (s : Site) (v : Value) {r : Nat} (hr : r ≠ 1534) :
    valueOf L g { d with site := s, stg := { d.stg with cm4 := v } } r = valueOf L g d r := by
  have hb : (r == 1534) = false := by simpa using hr
  have hX : (valuesX L g { d with site := s, stg := { d.stg with cm4 := v } }).lookup r =
      (valuesX L g d).lookup r := by
    simp only [valuesX, valuesXt, D.pwV, D.pwE, lookup_append', List.lookup, hb]
  exact valueOf_congrX (d := d) (d' := { d with site := s, stg := { d.stg with cm4 := v } })
    rfl rfl rfl rfl rfl rfl hX

theorem frame_ld (d : D) (s : Site) (v : Value) {r : Nat} (hr : r ≠ 1542) :
    valueOf L g { d with site := s, stg := { d.stg with ld := v } } r = valueOf L g d r := by
  have hb : (r == 1542) = false := by simpa using hr
  have hX : (valuesX L g { d with site := s, stg := { d.stg with ld := v } }).lookup r =
      (valuesX L g d).lookup r := by
    simp only [valuesX, valuesXt, D.pwV, D.pwE, lookup_append', List.lookup, hb]
  exact valueOf_congrX (d := d) (d' := { d with site := s, stg := { d.stg with ld := v } })
    rfl rfl rfl rfl rfl rfl hX

theorem frame_m2 (d : D) (s : Site) (v : Value) {r : Nat} (hr : r ≠ 1544) :
    valueOf L g { d with site := s, stg := { d.stg with m2 := v } } r = valueOf L g d r := by
  have hb : (r == 1544) = false := by simpa using hr
  have hX : (valuesX L g { d with site := s, stg := { d.stg with m2 := v } }).lookup r =
      (valuesX L g d).lookup r := by
    simp only [valuesX, valuesXt, D.pwV, D.pwE, lookup_append', List.lookup, hb]
  exact valueOf_congrX (d := d) (d' := { d with site := s, stg := { d.stg with m2 := v } })
    rfl rfl rfl rfl rfl rfl hX

theorem step_shfl7 (hi : Inv L g d) (hs : d.site = .shfl7) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2242 := by rw [hs]; rfl
  have hc' : kernel.code[2242]? = some ins := hpc ▸ hc
  have hins := Option.some.inj (hc'.symm.trans Flow.code_shfl_7)
  have hlate : LateSite d.site := by rw [hs]; trivial
  refine step_shflMin (s := .shfl7) (s' := .shfl8) (pc := 2242) (rv := 1535) (a := 507)
    (dst := 1536) (old := d.stg.al)
    (upd := fun v => { d with site := .shfl8, stg := { d.stg with cm1 := v } }) hi hs rfl rfl
    (by rw [hins]; exact ⟨_, _, _, _, _, rfl⟩) Flow.code_2243 (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide +kernel) (valueOf_r46 d)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    (fun av bv cv recv ok => by simp only [next, hs]; rfl)
    (fun v => rfl)
    (fun v hv => inv_stg (inv_late hi hlate (s := .shfl8) trivial
      (fun h => absurd h (by simp))) _ _
        (by exact ⟨hi.four.al, hv, hi.four.cm2,
          hi.four.cm3, hi.four.cm4, hi.four.ld, hi.four.m2, hi.four.sw⟩))
    (fun v => valueOf_cm1 { d with site := .shfl8, stg := { d.stg with cm1 := v } })
    (fun v r hr => frame_cm1 d _ v hr) h hc hf

theorem step_shfl8 (hi : Inv L g d) (hs : d.site = .shfl8) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2244 := by rw [hs]; rfl
  have hc' : kernel.code[2244]? = some ins := hpc ▸ hc
  have hins := Option.some.inj (hc'.symm.trans Flow.code_shfl_8)
  have hlate : LateSite d.site := by rw [hs]; trivial
  refine step_shflMin (s := .shfl8) (s' := .shfl9) (pc := 2244) (rv := 1537) (a := 1536)
    (dst := 1538) (old := d.stg.cm1)
    (upd := fun v => { d with site := .shfl9, stg := { d.stg with cm2 := v } }) hi hs rfl rfl
    (by rw [hins]; exact ⟨_, _, _, _, _, rfl⟩) Flow.code_2245 (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide +kernel) (valueOf_cm1 d)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    (fun av bv cv recv ok => by simp only [next, hs]; rfl)
    (fun v => rfl)
    (fun v hv => inv_stg (inv_late hi hlate (s := .shfl9) trivial
      (fun h => absurd h (by simp))) _ _
        (by exact ⟨hi.four.al, hi.four.cm1, hv,
          hi.four.cm3, hi.four.cm4, hi.four.ld, hi.four.m2, hi.four.sw⟩))
    (fun v => valueOf_cm2 { d with site := .shfl9, stg := { d.stg with cm2 := v } })
    (fun v r hr => frame_cm2 d _ v hr) h hc hf

theorem step_shfl9 (hi : Inv L g d) (hs : d.site = .shfl9) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2246 := by rw [hs]; rfl
  have hc' : kernel.code[2246]? = some ins := hpc ▸ hc
  have hins := Option.some.inj (hc'.symm.trans Flow.code_shfl_9)
  have hlate : LateSite d.site := by rw [hs]; trivial
  refine step_shflMin (s := .shfl9) (s' := .shfl10) (pc := 2246) (rv := 1539) (a := 1538)
    (dst := 1540) (old := d.stg.cm2)
    (upd := fun v => { d with site := .shfl10, stg := { d.stg with cm3 := v } }) hi hs rfl rfl
    (by rw [hins]; exact ⟨_, _, _, _, _, rfl⟩) Flow.code_2247 (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide +kernel) (valueOf_cm2 d)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    (fun av bv cv recv ok => by simp only [next, hs]; rfl)
    (fun v => rfl)
    (fun v hv => inv_stg (inv_late hi hlate (s := .shfl10) trivial
      (fun h => absurd h (by simp))) _ _
        (by exact ⟨hi.four.al, hi.four.cm1, hi.four.cm2,
          hv, hi.four.cm4, hi.four.ld, hi.four.m2, hi.four.sw⟩))
    (fun v => valueOf_cm3 { d with site := .shfl10, stg := { d.stg with cm3 := v } })
    (fun v r hr => frame_cm3 d _ v hr) h hc hf

theorem step_shfl10 (hi : Inv L g d) (hs : d.site = .shfl10) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2248 := by rw [hs]; rfl
  have hc' : kernel.code[2248]? = some ins := hpc ▸ hc
  have hins := Option.some.inj (hc'.symm.trans Flow.code_shfl_10)
  have hlate : LateSite d.site := by rw [hs]; trivial
  refine step_shflMin (s := .shfl10) (s' := .store10) (pc := 2248) (rv := 1541) (a := 1540)
    (dst := 1534) (old := d.stg.cm3)
    (upd := fun v => { d with site := .store10, stg := { d.stg with cm4 := v } }) hi hs rfl rfl
    (by rw [hins]; exact ⟨_, _, _, _, _, rfl⟩) Flow.code_2249 (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide +kernel) (valueOf_cm3 d)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    (fun av bv cv recv ok => by simp only [next, hs]; rfl)
    (fun v => rfl)
    (fun v hv => inv_stg (inv_late hi hlate (s := .store10) trivial
      (fun h => absurd h (by simp))) _ _
        (by exact ⟨hi.four.al, hi.four.cm1, hi.four.cm2,
          hi.four.cm3, hv, hi.four.ld, hi.four.m2, hi.four.sw⟩))
    (fun v => valueOf_cm4 { d with site := .store10, stg := { d.stg with cm4 := v } })
    (fun v r hr => frame_cm4 d _ v hr) h hc hf

theorem step_shfl11 (hi : Inv L g d) (hs : d.site = .shfl11) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2253 := by rw [hs]; rfl
  have hc' : kernel.code[2253]? = some ins := hpc ▸ hc
  have hins := Option.some.inj (hc'.symm.trans Flow.code_shfl_11)
  have hlate : LateSite d.site := by rw [hs]; trivial
  refine step_shflMin (s := .shfl11) (s' := .shfl12) (pc := 2253) (rv := 1543) (a := 1542)
    (dst := 1544) (old := d.stg.ld)
    (upd := fun v => { d with site := .shfl12, stg := { d.stg with m2 := v } }) hi hs rfl rfl
    (by rw [hins]; exact ⟨_, _, _, _, _, rfl⟩) Flow.code_2254 (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide +kernel) (valueOf_ld d)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    (fun av bv cv recv ok => by simp only [next, hs]; rfl)
    (fun v => rfl)
    (fun v hv => inv_stg (inv_late hi hlate (s := .shfl12) trivial
      (fun h => absurd h (by simp))) _ _
        (by exact ⟨hi.four.al, hi.four.cm1, hi.four.cm2,
          hi.four.cm3, hi.four.cm4, hi.four.ld, hv, hi.four.sw⟩))
    (fun v => valueOf_r1082 { d with site := .shfl12, stg := { d.stg with m2 := v } })
    (fun v r hr => frame_m2 d _ v hr) h hc hf


/-! ### The shuffle of the half sums (pc 2234) -/

/-- `setp.eq.b64 p, a, 0` of a 64-bit counter. -/
theorem exec_setpEq64 {t : TState} {p a x : Nat} (hx : x < 2 ^ 64)
    (hS : Assumption.SegFreePc asms t.pc) (ha : t.regs a = some (b64 x)) :
    execLocalA asms L g t (.int ⟨.setp .eq none, .int .b 64, false, [some p], [.reg a, .imm 0]⟩) =
      .ok (PTX.next (setReg t p (.pred (decide (x = 0))))) := by
  rw [hS.exec rfl, execLocalRule_of_none (asms_none (by simp) (by simp))]
  simp [execLocal, Op.rule, IntInstr.rule, execInt, DType.width, readReg, readBits, ha, b64,
    PTX.compare, DType.intLanes?, Cmp.intOk, bind, Except.bind, pure, Except.pure]
  have e : (DType.int IType.b 64).kind?.getD IType.b = IType.b := rfl
  have h1 : (truncBits 64 (BitVec.ofNat 64 x)).toNat = x := by
    simp only [truncBits, BitVec.toNat_ofNat]
    omega
  have h2 : (truncBits 64 0#64).toNat = 0 := by decide
  simp [e, h1, h2]

theorem valueOf_i64 (d : D) : valueOf L g d 2446 = b64 d.i := by
  sm_vals

theorem frame_rs (d : D) (s : Site) (v : Value) {r : Nat} (hr : r ≠ 1531) :
    valueOf L g { d with site := s, stg := { d.stg with rs := v } } r = valueOf L g d r := by
  have hb : (r == 1531) = false := by simpa using hr
  have hX : (valuesX L g { d with site := s, stg := { d.stg with rs := v } }).lookup r =
      (valuesX L g d).lookup r := by
    simp only [valuesX, valuesXt, D.pwV, D.pwE, lookup_append', List.lookup, hb]
  exact valueOf_congrX (d := d) (d' := { d with site := s, stg := { d.stg with rs := v } })
    rfl rfl rfl rfl rfl rfl hX

theorem live_s6 : (∀ r ∈ Flow.live 2235, r = 1530 ∨ r ∈ Flow.live 2234) ∧
    (1529 ∈ Flow.live 2235) ∧ (1530 ∈ Flow.live 2235) ∧
    subX (Flow.live 2236) (Flow.live 2235) [1531] = true ∧
    (2446 ∈ Flow.live 2236) ∧ subX (Flow.live 2237) (Flow.live 2236) [169] = true ∧
    (∀ r ∈ Flow.live 2237, r = 1531 ∨ r = 169 ∨ r ∈ Flow.live 2234) ∧
    1530 ∉ Flow.live 2234 ∧ 1531 ∉ Flow.live 2234 ∧ 169 ∉ Flow.live 2234 ∧
    Assumptions.emuSites.contains 2235 = false ∧ Assumptions.emuSites.contains 2236 = false := by
  decide +kernel

/-- The facts at pc 2237 after the half sums' step: the row sum `v`, the received word `recv` and
`%p169`. -/
abbrev Fshfl6 (d : D) (v recv : Value) : List (Nat × Value) :=
  factsFrom (Flow.live 2237) (valueEx (valueOf L g d)
    [(169, .pred (decide (d.i = 0))), (1531, v), (1530, recv)])

theorem live_s6b :
    (∀ r ∈ Flow.live 949, r ∈ Flow.live 2237 ∧ (r = 1531 ∨ r = 169 ∨ r ∈ Flow.live 2234)) ∧
    (∀ r ∈ Flow.live 2239, r = 1532 ∨
      (r ∈ Flow.live 2237 ∧ (r = 1531 ∨ r = 169 ∨ r ∈ Flow.live 2234))) ∧
    1532 ∉ Flow.live 2237 ∧ 504 ∈ Flow.live 2237 ∧ 169 ∈ Flow.live 2237 := by
  decide +kernel

/-- **A fact of the half sums' step is the table's value of the state after it**: a live register
of pc 2237 that is the row sum, `%p169` or live at the shuffle holds the value `valueOf` gives the
state `d.afterSum v`. -/
theorem val_afterSum {d : D} {v recv : Value} {R : Nat → Option Value}
    (h : Holds R (Fshfl6 (L := L) (g := g) d v recv)) {r : Nat} (hr : r ∈ Flow.live 2237)
    (hl : r = 1531 ∨ r = 169 ∨ r ∈ Flow.live 2234) :
    R r = some (valueOf L g (d.afterSum v) r) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, n1, n2, n3, e1, e2⟩ := live_s6
  rw [holds_mem h (Flow.mem_factsFrom (val := valueEx (valueOf L g d)
    [(169, .pred (decide (d.i = 0))), (1531, v), (1530, recv)]) hr)]
  refine congrArg some ?_
  rcases hl with rfl | rfl | hl
  · simp [valueEx, List.lookup]
    exact (valueOf_r1072 (d.afterSum v)).symm
  · simp [valueEx, List.lookup]
    exact (valueOf_p169 (d.afterSum v)).symm
  · have hne1 : r ≠ 1531 := fun he => n2 (he ▸ hl)
    have hne2 : r ≠ 1530 := fun he => n1 (he ▸ hl)
    have hne3 : r ≠ 169 := fun he => n3 (he ▸ hl)
    simp only [valueEx, List.lookup, beq_false_of_ne hne1, beq_false_of_ne hne2,
      beq_false_of_ne hne3, Option.getD_none]
    exact (frame_rs d _ _ hne1).symm

/-- **The shuffle of the half sums** (pc 2234): the thread adds the received word to its own sum
(`D.rsOut`: the outcome of `add.f32` on any received word), sets `%p169` (the first iteration)
and branches on it (pc 2237): in the first iteration the update and the P store's barrier follow;
otherwise the `xor` of pc 2238 computes the parity of the poll of `o_done`, which is next. Where
the `add` faults the thread is dead. -/
theorem step_shfl6 (hi : Inv L g d) (hs : d.site = .shfl6) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2234 := by rw [hs]; rfl
  have hc' : kernel.code[2234]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_shfl_6)
  have h' : At t 2234 (factsAt L g 2234 d) := hpc ▸ h
  have hf' := hpc ▸ hf
  obtain ⟨av, bv, cv, recv, ok, rfl, hu⟩ := fires_shfl (p := none) hf'
  simp only [Option.elim] at hu
  subst hu
  have hlate : LateSite d.site := by rw [hs]; trivial
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, n1, n2, n3, e1, e2⟩ := live_s6
  have h1 := At.set (r := 1530) (v := recv) h' (facts_ne n1)
  have h1' : At (PTX.next (setReg t 1530 recv)) 2235
      (factsFrom (Flow.live 2235) (valueEx (valueOf L g d) [(1530, recv)])) := by
    refine h1.mono (holds_of_pointwise fun r hr => ?_)
    rcases l1 r hr with rfl | hl
    · simpa [valueEx, List.lookup] using holds_mem h1.2.2.2.2 (List.mem_cons_self ..)
    · have hne : r ≠ 1530 := fun he => n1 (he ▸ hl)
      have := holds_mem h1.2.2.2.2 (List.mem_cons_of_mem _
        (Flow.mem_factsFrom (val := valueOf L g d) hl))
      simpa [valueEx, List.lookup, beq_false_of_ne hne] using this
  -- 2235: the row sum, the outcome of `add.f32` on the thread's sum and the received word
  have hEx : ∀ t', At t' 2235
      (factsFrom (Flow.live 2235) (valueEx (valueOf L g d) [(1530, recv)])) →
      execLocalA asms L g t' (addOp 1531 1529 1530) =
        (d.rsOut recv).map fun x => PTX.next (setReg t' 1531 x) := by
    intro t' h2
    have hE : Assumptions.emuSites.contains t'.pc = false := by rw [h2.1]; exact e1
    have ra : t'.regs 1529 = some d.stg.sw :=
      reg_of h2.2.2.2.2 l2 (by simp [valueEx, List.lookup, valueOf_r1070])
    have rb : t'.regs 1530 = some recv :=
      reg_of h2.2.2.2.2 l3 (by simp [valueEx, List.lookup])
    exact exec_addE_at (fz := false) (idealAtSc (L := L) (g := g) (by decide) hE)
      (declineAtSc (L := L) (g := g) (by decide) hE (by rw [h2.1]; decide)
        (by rw [h2.1]; decide) (by rw [h2.1]; decide)) (OpndIs.reg ra) (OpndIs.reg rb)
  rcases hrs : d.rsOut recv with f | v
  · -- the `add` faults: the thread is dead
    refine .inr ⟨by simp [next, hs, hrs], ?_⟩
    have hx := hEx _ h1'
    rw [hrs] at hx
    exact dead_of_error (by rw [h1'.1]; exact Flow.code_2235) rfl h1'.2.2.2.1 hx
  have pA : Seg kernel asms L g 1 2235
      (factsFrom (Flow.live 2235) (valueEx (valueOf L g d) [(1530, recv)])) 2236
      (factsFrom (Flow.live 2236) (valueEx (valueOf L g d) [(1531, v), (1530, recv)])) := by
    refine Seg.set1 (K := kernel) Flow.code_2235 rfl (fun t' h2 => ?_) (subX_sound l4)
    rw [hEx t' h2, hrs]
    rfl
  -- 2236: the first-iteration predicate
  have pB : Seg kernel asms L g 1 2236
      (factsFrom (Flow.live 2236) (valueEx (valueOf L g d) [(1531, v), (1530, recv)])) 2237
      (factsFrom (Flow.live 2237) (valueEx (valueOf L g d)
        [(169, .pred (decide (d.i = 0))), (1531, v), (1530, recv)])) := by
    refine Seg.set1 (K := kernel) Flow.code_2236 rfl (fun t' h2 => ?_) (subX_sound l6)
    have hE : Assumptions.emuSites.contains t'.pc = false := by rw [h2.1]; exact e2
    have ra : t'.regs 2446 = some (b64 d.i) :=
      reg_of h2.2.2.2.2 l5 (by simp [valueEx, List.lookup, valueOf_i64])
    have hlt : d.i < 2 ^ 64 := by
      have := hi.i
      have := hi.ok.r26_lt
      omega
    exact exec_setpEq64 hlt (segFree hE) ra
  obtain ⟨t2, hr2, ht2⟩ := (pA.comp pB).rtg h1'
  -- 2237: `@%p169 bra`, taken in the first iteration
  have m169 : (169, Value.pred (decide (d.i = 0))) ∈ Fshfl6 (L := L) (g := g) d v recv := by
    have := Flow.mem_factsFrom (val := valueEx (valueOf L g d)
      [(169, .pred (decide (d.i = 0))), (1531, v), (1530, recv)])
      (show 169 ∈ Flow.live 2237 by decide +kernel)
    simpa [valueEx, List.lookup] using this
  have pC := Seg.bra (K := kernel) (A := asms) (L := L) (g := g) (pc := 2237) (target := 949)
    (uni := false) (pick := decide (d.i = 0)) (F := Fshfl6 (L := L) (g := g) d v recv)
    Flow.code_2237 m169 (fun _ _ => localRule_bra) (segFree emu_2237)
  obtain ⟨t3, hr3, ht3⟩ := pC.rtg ht2
  have hi' : Inv L g (d.afterSum v) :=
    inv_stg (inv_late hi hlate (s := .waitO) trivial (fun h => absurd h (by simp))) _ _
        (by exact ⟨hi.four.al, hi.four.cm1, hi.four.cm2,
          hi.four.cm3, hi.four.cm4, hi.four.ld, hi.four.m2, hi.four.sw⟩)
  obtain ⟨m949, m2239, n4, m504, -⟩ := live_s6b
  by_cases hi0 : d.i = 0
  · -- the first iteration: the update and the P store's barrier
    rw [if_pos (decide_eq_true hi0)] at ht3
    have h949 : At t3 949 (factsAt L g 949 (d.afterSum v)) :=
      ⟨ht3.1, ht3.2.1, ht3.2.2.1, ht3.2.2.2.1, Flow.holds_of_pointwise fun r hr' =>
        val_afterSum ht3.2.2.2.2 (m949 r hr').1 (m949 r hr').2⟩
    have hn : next L g d ⟨Flow.shfl_6, .shfl .bfly av bv cv recv ok⟩ =
        toBar20 (d.afterSum v) := by
      simp [next, hs, hrs, hi0]
    rcases cont_edge (d := d.afterSum v) hi' (by simp [D.afterSum, LateSite]) h949 with
      ⟨hn', hd⟩ | ⟨d', t'', hd, hr', ha, hinv⟩
    · exact .inr ⟨hn.trans hn', dead_of_rtg (hr2.trans hr3) hd⟩
    · exact .inl (.inr ⟨d', t'', hn.trans hd, (hr2.trans hr3).trans hr', ha, hinv⟩)
  · -- the poll of `o_done`: the `xor` of its parity (pc 2238) is the last step
    rw [if_neg (by simpa using hi0)] at ht3
    have hF : ∀ p ∈ Fshfl6 (L := L) (g := g) d v recv, p.1 ≠ 1532 := by
      intro p hp he
      simp only [Flow.factsFrom, List.mem_map] at hp
      obtain ⟨r, hr, rfl⟩ := hp
      exact n4 (he ▸ hr)
    have h504 : (504, b32 (d.i % 2)) ∈ Fshfl6 (L := L) (g := g) d v recv := by
      have := Flow.mem_factsFrom (val := valueEx (valueOf L g d)
        [(169, .pred (decide (d.i = 0))), (1531, v), (1530, recv)]) m504
      simpa [valueEx, List.lookup, valueOf_r43] using this
    obtain ⟨t4, hr4, ht4⟩ := (seg_2238 d _ hF h504).rtg ht3
    have hat : At t4 (d.afterSum v).site.pc (facts L g (d.afterSum v)) := by
      refine ⟨ht4.1, ht4.2.1, ht4.2.2.1, ht4.2.2.2.1, Flow.holds_of_pointwise fun r hr' => ?_⟩
      rcases m2239 r hr' with rfl | ⟨hr, hl⟩
      · rw [holds_mem ht4.2.2.2.2 (List.mem_cons_self ..)]
        exact congrArg some (valueOf_r1071 (d.afterSum v)).symm
      · exact val_afterSum ht4.2.2.2.2.2 hr hl
    have hn : next L g d ⟨Flow.shfl_6, .shfl .bfly av bv cv recv ok⟩ =
        some (some (d.afterSum v)) := by
      simp [next, hs, hrs, hi0]
    exact .inl (.inr ⟨d.afterSum v, t4, hn, (hr2.trans hr3).trans hr4, hat, hi'⟩)

/-! ### The load of the minima (pc 2252) -/

theorem live_2253_ldL : ∀ r ∈ Flow.live 2253, r = 1542 ∨ r ∈ Flow.live 2252 := by decide +kernel

theorem ldL_not_live : 1542 ∉ Flow.live 2252 := by decide +kernel

/-- A 32-bit shared load at `a + off` returns four bytes. -/
theorem fires_ld_shared_len {A : List Assumption} {t u : TState} {pc : Nat} {e : Event}
    {dst base a off : Nat} {ik : IType} (hr : t.regs base = some (b32 a))
    (ha : a + off < 2 ^ 32) (hs : t.sub = 0)
    (hf : Fires pc (eventTmpl A L g t (.mem
      { kind := .load, space := some (.shared .cta), sem := .weak, elem := .int ik 32,
        addr := ⟨.reg base 32, (off : Int)⟩, dsts := [some dst] })) e (some u)) :
    ∀ ac bs, e.kind = .rd ac bs → bs.length = 4 := by
  intro ac bs hk
  have hz := fires_ld_shared_size hr ha hs hf ac bs hk
  rw [eventTmpl, memTmpl_load (sp := .shared) (base := base) (w := 32) (by cases ik <;> rfl) rfl
    rfl rfl rfl] at hf
  simp only [MemAccess.regs, DType.width, loadTmpl,
    effAddr_b32_off hr ha, bind, Except.bind, elemAcc, hs] at hf
  simp only [Bool.false_eq_true, ↓reduceIte] at hf
  split_ifs at hf
  all_goals first
    | (simp [throw, throwThe, MonadExceptOf.throw, Fires] at hf; done)
    | (exfalso; simp_all; done)
    | (obtain ⟨bs', hl, rfl, -⟩ := hf
       simp only [Kind.rd.injEq] at hk
       rw [← hk.2, hl, hk.1, hz])

/-- **The load of the minima from shared memory** (pc 2252): the word read is recorded; it has
four bytes, since the load reads four. -/
theorem step_ldL (hi : Inv L g d) (hsb : L.sharedBase + 213340 ≤ 2 ^ 18) (hs : d.site = .ldL)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2252 := by rw [hs]; rfl
  have hc' : kernel.code[2252]? = some ins := hpc ▸ hc
  have hins := Option.some.inj (hc'.symm.trans Flow.code_load_202)
  have hf0 : Fires 2252 (eventTmpl asms L g t (.mem
      { kind := .load, space := some (.shared .cta), sem := .weak, elem := .int .b 32,
        addr := ⟨.reg 500 32, ((212992 : Nat) : Int)⟩, dsts := [some 1542] })) e (some u) := by
    have := hpc ▸ hf
    rw [hins] at this
    exact this
  have h500 : t.regs 500 = some (b32 (L.sharedBase + g % L.block % 4 * 4)) := by
    have hm : g % L.block % 4 < 4 := Nat.mod_lt _ (by omega)
    have hmod : (L.sharedBase + g % L.block % 4 * 4) % 2 ^ 32 =
        L.sharedBase + g % L.block % 4 * 4 := Nat.mod_eq_of_lt (by omega)
    rw [holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d)
      (show 500 ∈ Flow.live d.site.pc by rw [hpc]; decide +kernel)), ← hmod]
    sm_vals
  have hlen := fires_ld_shared_len h500
    (by have : g % L.block % 4 < 4 := Nat.mod_lt _ (by omega); omega) h.2.1 hf0
  obtain ⟨a, ha, hk, hnc, hext, hregs⟩ : ∃ a : MemAccess, ins.op = .mem a ∧ a.kind = .load ∧
      a.nc = false ∧ a.ext = .same ∧ a.regs = [1542] := by
    rw [hins]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  rw [ha] at hf
  have hf' := hpc ▸ hf
  obtain ⟨r, bs, rfl, hu⟩ := fires_load hk hnc hf' hext
  obtain rfl : u = afterLoad t [1542] bs := hregs ▸ hu
  have h' : At t 2252 (factsAt L g 2252 d) := hpc ▸ h
  have hlate : LateSite d.site := by rw [hs]; trivial
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [next, hs, hv],
      Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    have hv4 : v.bytes = 4 := rebuild_bytes_of_length hv (hlen r bs rfl)
    refine .inl (.inr ⟨{ d with site := .shfl11, stg := { d.stg with ld := v } }, _,
      by simp [next, hs, hv], .refl, ?_,
      inv_stg (inv_late hi hlate (s := .shfl11) trivial (fun h => absurd h (by simp))) _ _
          (by exact ⟨hi.four.al, hi.four.cm1, hi.four.cm2,
            hi.four.cm3, hi.four.cm4, hv4, hi.four.m2, hi.four.sw⟩)⟩)
    have h1 := At.set (r := 1542) (v := v) h' (facts_ne ldL_not_live)
    have hst : { setReg t 1542 v with pc := t.pc + 1, sub := 0, acc := [] } =
        PTX.next (setReg t 1542 v) := by
      have hs0 := h'.2.1
      have ha0 := h'.2.2.1
      cases t
      simp_all [PTX.next, setReg]
    rw [afterLoad_ok h'.2.1 h'.2.2.1 hv, hst]
    refine h1.mono (holds_of_pointwise fun r hr => ?_)
    rcases live_2253_ldL r hr with rfl | hl
    · rw [holds_mem h1.2.2.2.2 (List.mem_cons_self ..)]
      exact congrArg some
        (valueOf_ld { d with site := .shfl11, stg := { d.stg with ld := v } }).symm
    · have hne : r ≠ 1542 := fun he => ldL_not_live (he ▸ hl)
      rw [frame_ld d _ v hne]
      exact holds_mem h1.2.2.2.2 (List.mem_cons_of_mem _
        (Flow.mem_factsFrom (val := valueOf L g d) hl))


/-! ### The poll of `o_done` (pc 2239) -/

theorem live_2239_p : 2608 ∉ Flow.live 2239 := by decide +kernel
theorem live_2241_2239 : ∀ r ∈ Flow.live 2241, r ∈ Flow.live 2239 := by decide +kernel

/-- **The poll of `o_done`** (pc 2239): a failed poll polls again; a successful one continues to
the named barrier before the minimum of `alpha`. -/
theorem step_waitO (hi : Inv L g d) (hs : d.site = .waitO) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2239 := by rw [hs]; rfl
  have hc' : kernel.code[2239]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_mbarWait_1)
  have h' : At t 2239 (factsAt L g 2239 d) := hpc ▸ h
  have hf' : Fires t.pc (eventTmpl asms L g t (.mbarWait 2608 623 0 (.reg 1532) true .cta)) e
      (some u) := by rw [h'.1]; exact hpc ▸ hf
  obtain ⟨m, par, ok, sc, rfl, rfl⟩ := fires_wait hf'
  have h1 := At.set (r := 2608) (v := .pred ok) h' (facts_ne live_2239_p)
  have hlate : LateSite d.site := by rw [hs]; trivial
  cases ok with
  | false =>
    obtain ⟨w, hr, hw⟩ := run_nbra (L := L) (g := g) Flow.code_2240 false h1
      (holds_mem h1.2.2.2.2 (List.mem_cons_self ..)) (segFree (by decide +kernel))
    simp only [Bool.false_eq_true, ↓reduceIte] at hw
    exact .inl (.inr ⟨d, w, by simp [next, hs], run_rtg hr,
      ⟨by rw [hpc]; exact hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1,
        by show Holds w.regs (factsAt L g d.site.pc d); rw [hpc]; exact hw.2.2.2.2.2⟩, hi⟩)
  | true =>
    obtain ⟨w, hr, hw⟩ := run_nbra (L := L) (g := g) Flow.code_2240 true h1
      (holds_mem h1.2.2.2.2 (List.mem_cons_self ..)) (segFree (by decide +kernel))
    simp only [↓reduceIte] at hw
    have hw' : At w 2241 (factsAt L g 2241 d) :=
      hw.mono (holds_live hw.2.2.2.2.2 rfl live_2241_2239)
    exact .inl (.inr ⟨{ d with site := .bar22 }, w, by simp [next, hs], run_rtg hr,
      hw', inv_late hi hlate (s := .bar22) trivial (fun h => absurd h (by simp))⟩)

/-! ### The last exchange of the rescale test (pcs 2255-2258) -/

theorem add32_ofNat (a b : Nat) :
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 a) + truncBits 32 (BitVec.ofNat 64 b)) =
      BitVec.ofNat 64 ((a + b) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add]
  omega

/-- `add.s32 %r1150, %r45, %r30` (pc 2259): the Tensor Memory address of the rescale. -/
theorem seg_2259 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 1 2259 (factsAt L g 2259 d) 2260 (factsAt L g 2260 d) := by
  intro t h
  sm_seg h [add32_ofNat, r45]

/-- **The last exchange of the rescale test** (pc 2255): the thread computes `%p170`
(`min`, `setp.geu`) and branches on it (pc 2258); where it holds the update and the barrier of the
P store follow, otherwise the address of the rescale (pc 2259) and the load of `O` are next. A
thread whose `min`, `setp` or update faults is dead. -/
theorem step_shfl12 (hi : Inv L g d) (hs : d.site = .shfl12) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2255 := by rw [hs]; rfl
  have hc' : kernel.code[2255]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_shfl_12)
  have h' : At t 2255 (factsAt L g 2255 d) := hpc ▸ h
  have hf' := hpc ▸ hf
  obtain ⟨av, bv, cv, recv, ok, rfl, hu⟩ := fires_shfl (p := none) hf'
  simp only [Option.elim] at hu
  subst hu
  have hlate : LateSite d.site := by rw [hs]; trivial
  obtain ⟨n1, n2, n3⟩ := live_2255_new
  have h1 := At.set (r := 1545) (v := recv) h' (facts_ne n1)
  rcases hE1 : minE [d.stg.m2, recv] with f1 | x1
  · have hn : next L g d ⟨Flow.shfl_12, .shfl .bfly av bv cv recv ok⟩ = none := by
      simp [next, hs, D.p170, Except.bind, hE1]
    exact .inr ⟨hn, (segD_2256 d recv _ h1).2 (by simp [hE1, Except.toBool])⟩
  have pA : Seg kernel asms L g 1 2256 (F2255 (L := L) (g := g) d recv) 2257
      ((1546, okVal (b32 0) (minE [d.stg.m2, recv])) :: F2255 (L := L) (g := g) d recv) :=
    SegD.seg (segD_2256 d recv) (by simp [hE1, Except.toBool])
  rw [okVal_of_ok hE1] at pA
  rcases hE2 : setpE (.unord .ge) false x1 one32 with f2 | b
  · have hn : next L g d ⟨Flow.shfl_12, .shfl .bfly av bv cv recv ok⟩ = none := by
      simp [next, hs, D.p170, Except.bind, hE1, hE2]
    exact .inr ⟨hn, ((SegD.seg_comp pA (segD_2257 d recv x1)) _ h1).2
      (by simp [hE2, Except.toBool])⟩
  have pB : Seg kernel asms L g 1 2257 ((1546, x1) :: F2255 (L := L) (g := g) d recv) 2258
      ((170, .pred (okB (setpE (.unord .ge) false x1 one32))) :: (1546, x1) ::
        F2255 (L := L) (g := g) d recv) :=
    SegD.seg (segD_2257 d recv x1) (by simp [hE2, Except.toBool])
  rw [okB_of_ok hE2] at pB
  have pD := Seg.bra (K := kernel) (A := asms) (L := L) (g := g) (pc := 2258) (target := 949)
    (uni := false) (pick := b)
    (F := (170, Value.pred b) :: (1546, x1) :: F2255 (L := L) (g := g) d recv)
    Flow.code_2258 (List.mem_cons_self ..) (fun _ _ => localRule_bra) (segFree emu_2258)
  obtain ⟨t', hr, ht'⟩ := ((pA.comp pB).comp pD).rtg h1
  by_cases hb : b = true
  · rw [if_pos hb] at ht'
    have h949 : At t' 949 (factsAt L g 949 d) :=
      ht'.mono (Flow.holds_factsFrom_mono (holds_F2255 ht'.2.2.2.2) live_2255_949)
    have hn : next L g d ⟨Flow.shfl_12, .shfl .bfly av bv cv recv ok⟩ = toBar20 d := by
      simp [next, hs, D.p170, Except.bind, hE1, hE2, hb]
    rcases cont_edge hi hlate h949 with ⟨hn', hd⟩ | ⟨d', t'', hd, hr', ha, hinv⟩
    · exact .inr ⟨hn.trans hn', dead_of_rtg hr hd⟩
    · exact .inl (.inr ⟨d', t'', hn.trans hd, hr.trans hr', ha, hinv⟩)
  · rw [if_neg hb] at ht'
    have h2259 : At t' 2259 (factsAt L g 2259 d) :=
      ht'.mono (Flow.holds_factsFrom_mono (holds_F2255 ht'.2.2.2.2) live_2259_2255)
    obtain ⟨t2, hr2, ht2⟩ := (seg_2259 d hi.tid).rtg h2259
    have hn : next L g d ⟨Flow.shfl_12, .shfl .bfly av bv cv recv ok⟩ =
        some (some { d with site := .ldO }) := by
      simp [next, hs, D.p170, Except.bind, hE1, hE2, hb]
    exact .inl (.inr ⟨{ d with site := .ldO }, t2, hn, hr.trans hr2, ht2,
      inv_late hi hlate (s := .ldO) trivial (fun h => absurd h (by simp))⟩)

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
