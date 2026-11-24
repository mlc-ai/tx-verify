-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmStgE

@[expose] public section

/-! # The loop's exit: from the event that ends the loop to pc 2560

The loop leaves the region at the test of pc 1050 (`@%p91 bra 2560`), which an event of the
region reaches through the straight-line code that follows it: the `bar.sync 1` of pc 575 for a
lane whose preloads are masked (`bar0`), the last preload (`pre 63`), and, after the P store of
the previous block, the `bar.sync` of pc 1012 for a thread other than thread 0 (`bar21`) and the
arrival of pc 1013 (`arrive`). For each, the thread runs from the event to pc 1049, the test, and
the taken branch to pc 2560. The registers live at pc 2560 (the bridge's input) are functions of
the entry numbers and of the running maximum and sum, which the four events leave unchanged
(`factsAt_2560`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-! ### The registers live at pc 2560 -/

instance : DecidablePred WordKey := fun r => by unfold WordKey; infer_instance

theorem live_2560_frame : ∀ r ∈ Flow.live 2560,
    ¬ IKey r ∧ ¬ RKey r ∧ ¬ WordKey r ∧ ¬ XKey r ∧ r ≠ 1611 := by decide +kernel

/-- A register of neither the iteration's, the pointers', the bias words' nor the last section
has the same value in two states with the same entry numbers, running maximum and sum. -/
theorem valueOf_frameS {d d' : D} (h1 : d'.e = d.e) (h3 : d'.m = d.m) (h4 : d'.l = d.l) {r : Nat}
    (hI : ¬ IKey r) (hR : ¬ RKey r) (hW : ¬ WordKey r) (hX : ¬ XKey r) (hO : r ≠ 1611) :
    valueOf L g d' r = valueOf L g d r := by
  have b : (r == 1611) = false := by simpa using hO
  have eS : (valuesS L g d').lookup r = (valuesS L g d).lookup r := by
    simp only [valuesS, h1, h3, h4, List.lookup, b]
  have eP : valuesP L g d' = valuesP L g d := by simp only [valuesP, h1]
  have eQ : valuesQ L g d' = valuesQ L g d := by simp only [valuesQ, h1]
  have nR : ∀ x : D, (valuesR L g x).lookup r = none := fun x =>
    lookup_none_of_not_mem _ (fun hm => hR (keys_R x r hm))
  have nW : ∀ x : D, (valuesW x).lookup r = none := fun x =>
    lookup_none_of_not_mem _ (fun hm => hW (keys_words x r hm))
  have nX : ∀ x : D, (valuesX L g x).lookup r = none := fun x =>
    lookup_none_of_not_mem _ (fun hm => hX (keys_X x r hm))
  simp only [valueOf, values, lookup_append', lookup_none_of_not_mem _ (notI d hI),
    lookup_none_of_not_mem _ (notI d' hI), nR, nW, nX, eS, eP, eQ, Option.none_or,
    Option.or_none]

/-- **The facts at pc 2560** depend on the entry numbers, the running maximum and the running sum
only. -/
theorem factsAt_2560 {d d' : D} (h1 : d'.e = d.e) (h3 : d'.m = d.m) (h4 : d'.l = d.l) :
    factsAt L g 2560 d' = factsAt L g 2560 d := by
  unfold factsAt Flow.factsFrom
  refine List.map_congr_left fun r hr => ?_
  obtain ⟨a, b, c, e, f⟩ := live_2560_frame r hr
  rw [valueOf_frameS h1 h3 h4 a b c e f]

/-- The facts at pc 2560 of a state with the same entry numbers, running maximum and sum. -/
theorem factsAt_2560_of {d d' : D} {t : TState} (h : At t 2560 (factsAt L g 2560 d'))
    (h1 : d'.e = d.e := by rfl) (h3 : d'.m = d.m := by rfl) (h4 : d'.l = d.l := by rfl) :
    At t 2560 (factsAt L g 2560 d) := by
  rw [← factsAt_2560 h1 h3 h4]
  exact h

/-! ### The loop test that leaves -/

/-- **The loop test at pc 1049 and its taken branch** (pcs 1049 and 1050): where the counter is
at `num_iters` the thread continues at pc 2560. -/
theorem seg_exit (d : D) (hT : g % L.block < 128) (hok : d.e.Ok) (hi : d.i < 2 ^ 32)
    (heq : d.e.r26 = d.i) :
    Seg kernel asms L g 2 1049 (factsAt L g 1049 d) 2560 (factsAt L g 2560 d) := by
  have h1 := seg_1049 d hT hok hi
  have hv : valueOf L g d 91 = .pred true := by
    sm_vals
    simp [heq]
  have hp : (91, Value.pred true) ∈ factsAt L g 1050 d :=
    hv ▸ Flow.mem_factsFrom (val := valueOf L g d) (show 91 ∈ Flow.live 1050 by decide +kernel)
  have hb := Seg.bra (K := kernel) (A := asms) (L := L) (g := g) Flow.code_1050 hp
    (fun _ _ => localRule_bra) (segFree (by decide +kernel))
  exact Seg.of_len (h1.comp (hb.weaken_end fun R hR =>
    Flow.holds_factsFrom_mono hR (by decide +kernel))) rfl

/-- **From the facts at pc 1049 to pc 2560** of a state whose counter is at `num_iters`. -/
theorem exit_1049 (d1 : D) (hT : g % L.block < 128) (hok : d1.e.Ok) (heq : d1.e.r26 = d1.i)
    {u : TState} (hAt : At u 1049 (factsAt L g 1049 d1)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ At t' 2560 (factsAt L g 2560 d1) := by
  have := hok.r26_lt
  obtain ⟨t', hr, ht'⟩ := (seg_exit d1 hT hok (by omega) heq).rtg hAt
  exact ⟨t', hr, ht'⟩

/-- **From the facts at pc 807 to pc 2560**: the setup after the preloads, the loop test and the
taken branch. -/
theorem exit_807 (d1 : D) (hT : g % L.block < 128) (hok : d1.e.Ok)
    (hwb : ∀ k, (d1.w k).bytes = 2) (hi0 : d1.i = 0) (hm : d1.m = b32 4286578688)
    (hl : d1.l = b32 0) (heq : d1.e.r26 = d1.i) {u : TState}
    (hAt : At u 807 (factsAt L g 807 d1)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ At t' 2560 (factsAt L g 2560 d1) := by
  obtain ⟨t1, hr1, ht1⟩ := (seg_setupB d1 hT hok hwb hi0 hm hl).rtg hAt
  obtain ⟨t2, hr2, ht2⟩ := exit_1049 d1 hT hok heq ht1
  exact ⟨t2, hr1.trans hr2, ht2⟩

/-! ### The four events that end the loop -/

/-- **The barrier before the preloads, for a lane whose preloads are masked, with no block**
(`num_iters = 0`): the thread reaches pc 2560. -/
theorem exit_bar0 {d : D} {t u : TState} {e : Event} {ins : Instr} (hi : Inv L g d)
    (hs : d.site = .bar0) (ha : act0 d.e (g % L.block) = false) (heq : d.e.r26 = d.i)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ At t' 2560 (factsAt L g 2560 d) := by
  have hpc : d.site.pc = 575 := by rw [hs]; rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_19)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSync (.imm 1) false) from trivial) hf
  obtain ⟨hi0, hm, hl, hcw, hcv⟩ := hi.loop.2 hs
  have h1 : At (PTX.next t) 576 (factsAt L g 576 d) := by
    have hh : Holds t.regs (factsAt L g 575 d) := hpc ▸ h.2.2.2.2
    refine ⟨by simp [PTX.next, h.1, hpc], h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
    exact Flow.holds_factsFrom_mono hh (by decide +kernel)
  obtain ⟨t', hr', ht'⟩ := (seg_setupA d hi.tid hi.ok hcw).rtg h1
  have h85 : valueOf L g d 85 = .pred false := by rw [valueOf_p85, ha]
  obtain ⟨t2, hr2, ht2⟩ := (seg_skipPre d h85 hcw).rtg ht'
  have hAt : At t2 807 (factsAt L g 807 { d with cw := 64, w := fun _ => z16 }) := by
    rw [factsAt_congr (valueOf_skipPre d hcw)]
    exact ht2
  obtain ⟨t3, hr3, ht3⟩ := exit_807 (L := L) (g := g) { d with cw := 64, w := fun _ => z16 }
    hi.tid hi.ok (fun k => rfl) hi0 hm hl heq hAt
  exact ⟨t3, (hr'.trans hr2).trans hr3, factsAt_2560_of ht3⟩

/-- **After the last preload wrote its destination `x`, with no block** (`num_iters = 0`): the
thread reaches pc 2560. -/
theorem exit_pre_last (hi : Inv L g d) {j : Fin 64} (hs : d.site = .pre j)
    (hj : ¬ j.val + 1 < 64) (heq : d.e.r26 = d.i)
    (h : At t d.site.pc (facts L g d)) {x : Value} (hxb : x.bytes = 2) {u1 : TState}
    (hpc : u1.pc = t.pc + 1) (hsub : u1.sub = 0) (hacc : u1.acc = []) (hfl : u1.fault = none)
    (hreg : ∀ r, r ≠ 263 + j.val → u1.regs r = t.regs r) (hx : u1.regs (263 + j.val) = some x) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u1 t' ∧
      At t' 2560 (factsAt L g 2560 d) := by
  have hpc0 : d.site.pc = 680 + 2 * j.val := by rw [hs]; rfl
  have hj63 : j.val = 63 := by omega
  obtain ⟨hcw, hact⟩ := hi.cwPre j hs
  obtain ⟨hi0, hcv, hm, hl⟩ := hi.loop.1 j hs
  have hd1 := holds_afterLoad (R := u1.regs) hi hs (x := x) (fun r hr hne => by
    have := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d)
      (show r ∈ Flow.live d.site.pc by rw [hpc0]; exact hr))
    rw [hreg r hne]
    exact this) hx
  rw [show 681 + 2 * j.val = 807 by omega] at hd1
  have hv : valueOf L g { d with cw := 64, w := setW d.w j.val x } =
      valueOf L g (d.afterPre j.val x) :=
    funext (valueOf_congr (L := L) (g := g) (d := d.afterPre j.val x)
      (d' := { d with cw := 64, w := setW d.w j.val x }) rfl rfl rfl rfl
      (by funext k; simp [D.wd, D.afterPre, hj63]) rfl rfl rfl rfl)
  have hAt : At u1 807 (factsAt L g 807 { d with cw := 64, w := setW d.w j.val x }) := by
    rw [factsAt_congr hv]
    exact ⟨by rw [hpc, h.1, hpc0]; omega, hsub, hacc, hfl, hd1⟩
  have hwb : ∀ k, (setW d.w j.val x k).bytes = 2 := by
    intro k
    by_cases hk : k = j.val
    · subst hk; simpa [setW] using hxb
    · simpa [setW, Function.update_of_ne hk] using hi.wb k
  obtain ⟨t3, hr3, ht3⟩ := exit_807 (L := L) (g := g) { d with cw := 64, w := setW d.w j.val x }
    hi.tid hi.ok hwb hi0 hm hl heq hAt
  exact ⟨t3, hr3, factsAt_2560_of ht3⟩

/-- **The last preload, with no block** (`num_iters = 0`): the load's event returns a `bf16`
number and the thread reaches pc 2560. -/
theorem exit_pre {d : D} {t u : TState} {e : Event} {ins : Instr} (hi : Inv L g d) {j : Fin 64}
    (hs : d.site = .pre j) (hj : ¬ j.val + 1 < 64) (heq : d.e.r26 = d.i)
    (hbf : ∀ r bs, e.kind = .rd r bs → ∃ x, rebuild 3 bs = .ok x ∧ isBf16 x = true)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ At t' 2560 (factsAt L g 2560 d) := by
  have hpc : d.site.pc = 680 + 2 * j.val := by rw [hs]; rfl
  obtain ⟨a, hca, hk, hnc, hext, hregs, -⟩ := loadAt_spec (loadAt_pre j.val j.isLt)
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hca)
  obtain ⟨r, bs, rfl, rfl⟩ := fires_load hk hnc hf hext
  rw [hregs]
  obtain ⟨x, hv, hb⟩ := hbf r bs rfl
  rw [afterLoad_ok h.2.1 h.2.2.1 hv]
  exact exit_pre_last hi hs hj heq h (isBf16_bytes hb)
    (u1 := have __src := setReg t (263 + j.val) x
      { pc := t.pc + 1, regs := __src.regs, cf := __src.cf, fault := __src.fault : TState })
    rfl rfl rfl h.2.2.2.1 (fun r hr => by simp [setReg, Function.update_of_ne hr])
    (by simp [setReg])

/-- **After the arrival**, from the facts at pc 1014 of a late state whose next iteration is
past `num_iters`: the packs, the loop test and the taken branch. -/
theorem exit_top (hi : Inv L g d) (hl : LateSite d.site) (heq : d.e.r26 = d.i + 1)
    (hAt : At u 1014 (factsAt L g 1014 d)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ At t' 2560 (factsAt L g 2560 d) := by
  obtain ⟨hcw, hcv, hlt⟩ := hi.late hl
  obtain ⟨t', hr, ht'⟩ := (seg_top d hi.ok hlt hcw hcv hi.vb).rtg hAt
  obtain ⟨t'', hr', ht''⟩ := exit_1049 d.top hi.tid hi.ok (show d.e.r26 = d.i + 1 from heq) ht'
  exact ⟨t'', hr.trans hr', factsAt_2560_of ht''⟩

/-- **The barrier before the arrival, for a thread other than thread 0, with no block left**: the
arrival is skipped and the thread reaches pc 2560. -/
theorem exit_bar21 (hi : Inv L g d) (hs : d.site = .bar21) (hT : g % L.block ≠ 0)
    (heq : d.e.r26 = d.i + 1) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ At t' 2560 (factsAt L g 2560 d) := by
  have hpc : d.site.pc = 1012 := by rw [hs]; rfl
  have hc' : kernel.code[1012]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_bar_21)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSyncN _ _ _) from trivial) hf
  have hlate : LateSite d.site := by rw [hs]; trivial
  have h1 : At (PTX.next t) 1013 (factsAt L g 1013 d) :=
    at_next_live (pc := 1012) (pc' := 1013) (hpc ▸ h) rfl rfl live_1012
  have h178 : valueOf L g d 177 = .pred false := by
    have : g % L.block % 128 ≠ 0 := by
      rw [Nat.mod_eq_of_lt hi.tid]; exact hT
    sm_vals
    simp [this]
  have hm : (177, Value.pred false) ∈ factsAt L g 1013 d := by
    have := Flow.mem_factsFrom (val := valueOf L g d) (show 177 ∈ Flow.live 1013 by
      decide +kernel)
    rwa [h178] at this
  obtain ⟨t', hr', ht'⟩ := (seg_off Flow.code_mbarArrive_3 hm).rtg h1
  have ht'' : At t' 1014 (factsAt L g 1014 d) :=
    ht'.mono (holds_live ht'.2.2.2.2 rfl (by decide +kernel))
  obtain ⟨t'', hr'', ht'''⟩ := exit_top hi hlate heq ht''
  exact ⟨t'', hr'.trans hr'', ht'''⟩

/-- **The arrival on `p_ready`, with no block left**: the thread reaches pc 2560. -/
theorem exit_arrive (hi : Inv L g d) (hs : d.site = .arrive) (heq : d.e.r26 = d.i + 1)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ At t' 2560 (factsAt L g 2560 d) := by
  have hpc : d.site.pc = 1013 := by rw [hs]; rfl
  have hc' : kernel.code[1013]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_mbarArrive_3)
  have hf' := hpc ▸ hf
  obtain ⟨hu, m, tx', c, rel, sc, hk, -⟩ := fires_arrive_state hf'
  have hu' : u = PTX.next t := by simpa [mbarStateDest] using hu
  subst hu'
  have hlate : LateSite d.site := by rw [hs]; trivial
  have h1 : At (PTX.next t) 1014 (factsAt L g 1014 d) :=
    at_next_live (pc := 1013) (pc' := 1014) (hpc ▸ h) rfl rfl live_1013
  exact exit_top hi hlate heq h1

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
