-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmS
public import Kernels.InklingRelDecode.Proof.Thread.SmArr
public import Kernels.InklingRelDecode.Proof.Thread.SmPst

@[expose] public section

/-! # The running maximum and sum, and the edges into the P store (pcs 949-950)

The loop's tail updates the running maximum and sum before the P store (pc 949,
`selp.f32 %r1453, %r1453, %r1061, %p168`; pc 950, `fma.rn.f32 %r1454, %r1454, %r46, %r1070`), then
unpacks and converts the probabilities (pcs 951-998, `SmPst.seg_pqs`) and reaches the named
barrier of the P store (`bar20`, pc 999). Three places jump to pc 949: the branch `@%p169 bra` at
pc 2237, taken in the first iteration (`i = 0`, no `o_done` wait and no rescale), the branch
`@%p170 bra` at pc 2258, taken when every alpha of the CTA is at least 1, and the `bra.uni` at
pc 2330 after the O rescale. The new running maximum is the old one where the rescale is lazy
(`%p168`) and `%r1061` otherwise; the new running sum is `fma(l, alpha, row sum)`.

This file proves the update (`seg_upd`), the segments of the edge from the O rescale and the
pieces of the rescale test (the `xor` of the poll's parity at pc 2238, the `min` and the `setp`
of pcs 2256-2257); the steps of the sites that leave for pc 949 (`shfl6`, `shfl12`) are in
`SmStgD`, and `waitStO` (pc 2329, then the branch of pc 2330 and the update) is here. A thread
whose update faults (a selected maximum that is no four-byte word, an fma without an outcome, the
`min` or the `setp` of the test without an outcome) is dead, and the machine's `next` is `none`
there. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-! ### The table's registers of the score stage -/

theorem valueOf_p168 (d : D) : valueOf L g d 168 = .pred d.stg.kp := by
  rw [valueOf_X d (by unfold XKey; omega)]
  simp [valuesX, List.lookup]

theorem valueOf_r46 (d : D) : valueOf L g d 507 = d.stg.al := by
  rw [valueOf_X d (by unfold XKey; omega)]
  simp [valuesX, List.lookup]

theorem valueOf_r1063 (d : D) : valueOf L g d 1522 = d.stg.mn := by
  rw [valueOf_X d (by unfold XKey; omega)]
  simp [valuesX, List.lookup]

theorem valueOf_r1072 (d : D) : valueOf L g d 1531 = d.stg.rs := by
  rw [valueOf_X d (by unfold XKey; omega)]
  simp [valuesX, List.lookup]

theorem valueOf_r1082 (d : D) : valueOf L g d 1544 = d.stg.m2 := by
  rw [valueOf_X d (by unfold XKey; omega)]
  simp [valuesX, List.lookup]

theorem valueOf_m (d : D) : valueOf L g d 1914 = d.m := by
  sm_vals

theorem valueOf_l (d : D) : valueOf L g d 1915 = d.l := by
  sm_vals

theorem valueOf_p169 (d : D) : valueOf L g d 169 = .pred (decide (d.i = 0)) := by
  sm_vals

theorem valueOf_r1071 (d : D) : valueOf L g d 1532 = b32 ((d.i + 1) % 2) := by
  sm_vals

/-! ### Two states that differ in the running maximum or the running sum only -/

/-- A register other than the running maximum has the same value in two states that agree on
everything but the running maximum. -/
theorem valueOf_frameM {d d' : D} (h1 : d'.e = d.e) (h2 : d'.i = d.i) (h4 : d'.l = d.l)
    (hw : d'.wd = d.wd) (hv : d'.vd = d.vd) (h5 : d'.sv = d.sv) (h6 : d'.pf = d.pf)
    (hx : d'.stg = d.stg) {r : Nat} (hr : r ≠ 1914) : valueOf L g d' r = valueOf L g d r := by
  have b : (r == 1914) = false := by simpa using hr
  have eS : (valuesS L g d').lookup r = (valuesS L g d).lookup r := by
    simp only [valuesS, h1, h4, hx, List.lookup, b]
  have eP : valuesP L g d' = valuesP L g d := by simp only [valuesP, h1]
  have eQ : valuesQ L g d' = valuesQ L g d := by simp only [valuesQ, h1]
  have eR : valuesR L g d' = valuesR L g d := by simp only [valuesR, D.n, h1, h2]
  have eI : valuesI L g d' = valuesI L g d := by simp only [valuesI, D.n, h1, h2, hx]
  have eW : valuesW d' = valuesW d := by simp only [valuesW, hw, hv]
  have eX : valuesX L g d' = valuesX L g d := by
    simp only [valuesX, valuesXt, D.pwV, D.pwE, h5, hx]
  simp only [valueOf, values, lookup_append', eI, eS, eP, eQ, eR, eW, eX]

/-- A register other than the running sum has the same value in two states that agree on
everything but the running sum. -/
theorem valueOf_frameL {d d' : D} (h1 : d'.e = d.e) (h2 : d'.i = d.i) (h3 : d'.m = d.m)
    (hw : d'.wd = d.wd) (hv : d'.vd = d.vd) (h5 : d'.sv = d.sv) (h6 : d'.pf = d.pf)
    (hx : d'.stg = d.stg) {r : Nat} (hr : r ≠ 1915) : valueOf L g d' r = valueOf L g d r := by
  have b : (r == 1915) = false := by simpa using hr
  have eS : (valuesS L g d').lookup r = (valuesS L g d).lookup r := by
    simp only [valuesS, h1, h3, hx, List.lookup, b]
  have eP : valuesP L g d' = valuesP L g d := by simp only [valuesP, h1]
  have eQ : valuesQ L g d' = valuesQ L g d := by simp only [valuesQ, h1]
  have eR : valuesR L g d' = valuesR L g d := by simp only [valuesR, D.n, h1, h2]
  have eI : valuesI L g d' = valuesI L g d := by simp only [valuesI, D.n, h1, h2, hx]
  have eW : valuesW d' = valuesW d := by simp only [valuesW, hw, hv]
  have eX : valuesX L g d' = valuesX L g d := by
    simp only [valuesX, valuesXt, D.pwV, D.pwE, h5, hx]
  simp only [valueOf, values, lookup_append', eI, eS, eP, eQ, eR, eW, eX]

/-- The invariant at a late site of the data `d` with another running maximum and sum. -/
theorem inv_ml (hi : Inv L g d) (hl : LateSite d.site) {s : Site} (hs : LateSite s)
    (hlead : s = .arrive → g % L.block = 0) (m l : Value) (hlb : l.bytes = 4)
    (hm : d.stg.re = true → ScoreWord m) :
    Inv L g { d with site := s, m := m, l := l } := by
  obtain ⟨hcw, hcv, hlt⟩ := hi.late hl
  refine ⟨hi.tid, hi.ok, hi.i, fun k hk => ?_, fun k hk => ?_, ⟨fun k hk => ?_, fun hk => ?_⟩,
    hi.wb, hi.vb, fun hk => ?_, fun _ => ⟨hcw, hcv, hlt⟩, hlead,
    fun hr => { hi.re hr with m := hm hr }, hlb, hi.four, hi.bw, hi.wf, hi.vf⟩
  · have : s = .pre k := hk
    subst this
    exact absurd hs (by simp [LateSite])
  · have : s = .nxt k := hk
    subst this
    exact absurd hs (by simp [LateSite])
  · have : s = .pre k := hk
    subst this
    exact absurd hs (by simp [LateSite])
  · have : s = .bar0 := hk
    subst this
    exact absurd hs (by simp [LateSite])
  · have : s = .setMaxReg := hk
    subst this
    exact absurd hs (by simp [LateSite])

/-! ### Pieces whose end facts are another state's -/

/-- **One instruction that writes `r` with the outcome `E`, between the facts of two states**:
the thread continues when `E` does not fault and is dead otherwise. The facts after the
instruction are those of `d'`, which agrees with `d` outside `r`. -/
theorem segD_one2 {pc r : Nat} {op : Op} {d d' : D} {E : Exec Value}
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ t, At t pc (factsAt L g pc d) →
      execLocalA asms L g t op = E.map fun x => PTX.next (setReg t r x))
    (hv : ∀ x, E = .ok x → valueOf L g d' r = x)
    (hlive : ∀ r' ∈ Flow.live (pc + 1), r' = r ∨
      (r' ≠ r ∧ r' ∈ Flow.live pc ∧ valueOf L g d' r' = valueOf L g d r')) :
    SegD kernel asms L g 1 pc (factsAt L g pc d) (pc + 1) (factsAt L g (pc + 1) d')
      (E.toBool = true) := by
  intro t ht
  have he := hex t ht
  refine ⟨fun hok => ?_, fun hno => ?_⟩
  · rcases hE : E with e | x
    · rw [hE] at hok; cases hok
    rw [hE] at he
    refine ⟨_, run_local hc hl ht he, by simp [PTX.next, setReg, ht.1], ht.2.1, ht.2.2.1,
      ht.2.2.2.1, Flow.holds_of_pointwise fun r' hr' => ?_⟩
    rcases hlive r' hr' with rfl | ⟨hne, hrS, hval⟩
    · simp [PTX.next, setReg, hv x hE]
    · simp only [PTX.next, setReg, Function.update_of_ne hne]
      rw [hval]
      exact holds_mem ht.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d) hrS)
  · rcases hE : E with e | x
    · rw [hE] at he
      exact dead_of_error (hc.symm ▸ by rw [ht.1]) hl ht.2.2.2.1 he
    · rw [hE] at hno; exact absurd rfl hno

/-! ### The assumptions at these pcs -/

/-- At a pc outside the software `exp2` instances `fma.f32`, `min.f32` and `setp.f32` are read as
exact. -/
theorem idealAtSm {f : Assumption.FloatForm} (hf : f = .fma .f32 ∨ f = .min .f32 ∨ f = .setp .f32)
    {t : TState} (h : Assumptions.emuSites.contains t.pc = false) :
    Assumption.IdealAt asms f L g t := by
  show Assumption.IdealAt (Assumption.idealReal _ _ _ :: _) f L g t
  exact Assumption.idealAt_head (by rcases hf with rfl | rfl | rfl <;> decide) (segFree h).tail

/-- The assumptions after the first two have no local rule for an operation that is no conversion
at a pc that is none of the single-instruction readings' sites. -/
theorem asms_tail_none' {t : TState} {op : Op} (h1 : t.pc ≠ 2562) (h2 : t.pc ≠ 600)
    (h3 : t.pc ≠ 807) (hc : ∀ c, op ≠ .cvt c) :
    ∀ a ∈ asms.drop 2, a.localRule L g t op = none := by
  have hl : Assumptions.lg2Sites.contains t.pc = false := by
    simp [Assumptions.lg2Sites]; omega
  have hd : Assumptions.divFullSites.contains t.pc = false := by
    simp [Assumptions.divFullSites]; omega
  have hn : Assumptions.negSites.contains t.pc = false := by
    simp [Assumptions.negSites]; omega
  intro a ha
  simp only [asms, Assumptions.all, List.drop_succ_cons, List.drop_zero, List.mem_cons,
    List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · rfl
  · simp only [Assumptions.lg2Exact, hl]; simp
  · simp only [Assumptions.divFullExact, hd]; simp
  · simp only [Assumptions.negExact, hn]; simp
  · simp only [Assumptions.bf16Exact]
  · rfl
  · rfl
  · rfl

/-- An `fma.f32`, `min.f32` or `setp.f32` that the ideal rule declines takes the Core rule, at a
pc that is no software `exp2` instance and no single-instruction reading's site. -/
theorem declineAtSm {f : Assumption.FloatForm}
    (hfs : f = .fma .f32 ∨ f = .min .f32 ∨ f = .setp .f32) {t : TState}
    (h : Assumptions.emuSites.contains t.pc = false) (h1 : t.pc ≠ 2562) (h2 : t.pc ≠ 600)
    (h3 : t.pc ≠ 807) : DeclineAt asms f L g t := by
  intro op hf hn
  rw [(segFree h).exec rfl, execLocalRule_of_none]
  intro a ha
  by_cases hd : a ∈ asms.drop 2
  · refine asms_tail_none' h1 h2 h3 (fun c hc => ?_) a hd
    subst hc
    rcases hfs with rfl | rfl | rfl <;>
    · simp only [Assumption.FloatForm.ofOp] at hf
      split_ifs at hf <;> simp at hf
  · simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false,
      List.drop_succ_cons, List.drop_zero] at ha hd
    rcases ha with rfl | rfl | ha'
    · simp only [Assumptions.idealArith, Assumption.idealReal, hf]
      split_ifs
      · exact hn
      · rfl
    · exact Assumption.approxExact_localRule_none fun f' h' => by
        rw [Flow.approxForm_none_of_float hf] at h'; cases h'
    · exact absurd ha' hd

/-- **The local step of `fma.rn.f32`** at a state where the ideal rule is in force and its
declines take the Core rule: it writes the outcome `floatE` or faults. -/
theorem exec_fmaE {t : TState} (hA : IdealAt asms (.fma .f32) L g t)
    (hD : DeclineAt asms (.fma .f32) L g t) {rnd : FloatRound} {fz : Bool} {d : Nat}
    {a b c : Opnd} {va vb vc : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) (hc : OpndIs L g t c vc) :
    execLocalA asms L g t (.float { fmaI rnd fz with dsts := [some d], srcs := [a, b, c] }) =
      (floatE (fmaI rnd fz) [va, vb, vc]).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { fmaI rnd fz with dsts := [some d], srcs := [a, b, c] }) =
      some (.fma .f32) := by simp [FloatForm.ofOp]
  have hI : execIdealFloat L g t (.float { fmaI rnd fz with dsts := [some d], srcs := [a, b, c] })
      = (idealVal (fmaI rnd fz) [va, vb, vc]).map
        (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealVal, ha.2, hb.2, hc.2, bindRead_map, Option.map_map,
      Function.comp_def, Except.map, pure, Except.pure]
  unfold floatE
  cases hv : idealVal (fmaI rnd fz) [va, vb, vc] with
  | none => rw [hD _ hf (by rw [hI, hv]; rfl), execLocal_fma_core ha hb hc]
  | some r => rw [hA _ hf _ (by rw [hI, hv]; rfl)]

/-! ### Pcs 949 and 950 -/

/-- `selp.f32 d, a, b, p` of two registers that hold values and a predicate. -/
theorem exec_selpF {t : TState} {dst a b p : Nat} {va vb : Value} {pick : Bool}
    (hS : Assumption.SegFreePc asms t.pc) (hp : t.regs p = some (.pred pick))
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocalA asms L g t (.int ⟨.selp, .float .f32, false, [some dst], [.reg a, .reg b, .reg p]⟩) =
      (if (if pick then va else vb).bytes = 4 then
        (Except.ok (PTX.next (setReg t dst (if pick then va else vb))) : Exec TState)
      else .error .typeMismatch) := by
  rw [hS.exec rfl, execLocalRule_of_none (asms_none (by simp) (by simp))]
  cases pick <;>
  simp [execLocal, Op.rule, IntInstr.rule, execMove, DType.width, readValue, readReg, hp, ha, hb,
    bind, Except.bind, pure, Except.pure] <;>
  split_ifs <;> simp_all [throw, throwThe, MonadExceptOf.throw]

theorem live_949_950 : ∀ r ∈ Flow.live 950, r = 1914 ∨ r ∈ Flow.live 949 := by decide +kernel
theorem live_950_951 : ∀ r ∈ Flow.live 951, r = 1915 ∨ r ∈ Flow.live 950 := by decide +kernel
theorem emu_949 : Assumptions.emuSites.contains 949 = false := by decide +kernel
theorem emu_950 : Assumptions.emuSites.contains 950 = false := by decide +kernel

/-- **The new running maximum** (pc 949): the old one where the rescale is lazy, else `%r1061`. -/
theorem segD_949 (d : D) :
    SegD kernel asms L g 1 949 (factsAt L g 949 d) 950 (factsAt L g 950 { d with m := d.mNew })
      (d.mNew.bytes = 4) := by
  refine (segD_one2 (r := 1914) (d' := { d with m := d.mNew })
    (E := if d.mNew.bytes = 4 then (.ok d.mNew : Exec Value) else .error .typeMismatch)
    Flow.code_949 rfl ?_ ?_ ?_).iff ?_
  · intro t ht
    have hp := holds_mem ht.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d)
      (show 168 ∈ Flow.live 949 by decide +kernel))
    have ha := holds_mem ht.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d)
      (show 1914 ∈ Flow.live 949 by decide +kernel))
    have hb := holds_mem ht.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d)
      (show 1522 ∈ Flow.live 949 by decide +kernel))
    rw [valueOf_p168] at hp
    rw [valueOf_m] at ha
    rw [valueOf_r1063] at hb
    have hS : Assumption.SegFreePc asms t.pc := by rw [ht.1]; exact segFree emu_949
    rw [exec_selpF hS hp ha hb]
    unfold D.mNew
    split_ifs <;> rfl
  · intro x hx
    split_ifs at hx with h
    cases hx
    rw [valueOf_m]
  · intro r hr
    by_cases h1 : r = 1914
    · exact Or.inl h1
    · rcases live_949_950 r hr with h | h
      · exact absurd h h1
      · exact Or.inr ⟨h1, h, valueOf_frameM (d := d) (d' := { d with m := d.mNew }) rfl rfl rfl
          rfl rfl rfl rfl rfl h1⟩
  · by_cases h : d.mNew.bytes = 4 <;> simp [h, Except.toBool]

/-- **The new running sum** (pc 950): `fma.rn.f32 %r1454, %r1454, %r46, %r1070`. -/
theorem segD_950 (d : D) :
    SegD kernel asms L g 1 950 (factsAt L g 950 { d with m := d.mNew }) 951 (factsAt L g 951 d.upd)
      (d.lOut.toBool = true) := by
  refine segD_one2 (r := 1915) (d := { d with m := d.mNew }) (d' := d.upd) (E := d.lOut)
    Flow.code_950 rfl ?_ ?_ ?_
  · intro t ht
    have hl := holds_mem ht.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g { d with m := d.mNew })
      (show 1915 ∈ Flow.live 950 by decide +kernel))
    have ha := holds_mem ht.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g { d with m := d.mNew })
      (show 507 ∈ Flow.live 950 by decide +kernel))
    have hb := holds_mem ht.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g { d with m := d.mNew })
      (show 1531 ∈ Flow.live 950 by decide +kernel))
    rw [valueOf_l] at hl
    rw [valueOf_r46] at ha
    rw [valueOf_r1072] at hb
    exact exec_fmaE (idealAtSm (Or.inl rfl) (by rw [ht.1]; exact emu_950))
      (declineAtSm (Or.inl rfl) (by rw [ht.1]; exact emu_950) (by rw [ht.1]; decide)
        (by rw [ht.1]; decide) (by rw [ht.1]; decide))
      (OpndIs.reg hl) (OpndIs.reg ha) (OpndIs.reg hb)
  · intro x hx
    rw [valueOf_l]
    exact okVal_of_ok hx
  · intro r hr
    by_cases h1 : r = 1915
    · exact Or.inl h1
    · rcases live_950_951 r hr with h | h
      · exact absurd h h1
      · exact Or.inr ⟨h1, h, valueOf_frameL (d := { d with m := d.mNew }) (d' := d.upd) rfl rfl
          rfl rfl rfl rfl rfl rfl h1⟩

/-- **The update and the unpacks** (pcs 949 to 998): from the facts at pc 949 to the facts at the
barrier of the P store with the new running maximum and sum; the thread is dead where the update
faults. -/
theorem segD_edge (d : D) :
    SegD kernel asms L g 50 949 (factsAt L g 949 d) 999 (factsAt L g 999 d.upd)
      (d.updOk = true) :=
  SegD.of_len ((((segD_949 d).comp (segD_950 d)).comp (seg_pqs d.upd 24 (le_refl 24))).iff
    (by
      simp only [D.updOk, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, b⟩, c⟩⟩)) rfl

/-! ### The edge from the O rescale (pc 2329 and the `bra.uni` of pc 2330) -/

theorem live_2329 : ∀ r ∈ Flow.live 2330, r ∈ Flow.live 2329 := by decide +kernel
theorem live_949_2330 : ∀ r ∈ Flow.live 949, r ∈ Flow.live 2330 := by decide +kernel
theorem emu_2330 : Assumptions.emuSites.contains 2330 = false := by decide +kernel

/-- `bra.uni` of pc 2330 to the update, between the table's facts. -/
theorem seg_2330 (d : D) :
    Seg kernel asms L g 1 2330 (factsAt L g 2330 d) 949 (factsAt L g 949 d) :=
  (seg_goto (L := L) (g := g) Flow.code_2330 emu_2330).weaken_end fun _ hR =>
    Flow.holds_factsFrom_mono hR live_949_2330

/-- The machine's edge into the P store, from a thread that reached the update: its successor is
the state after the update, or none where the update faults. -/
theorem toBar20_ok (hc : d.updOk = true) :
    toBar20 d = some (some { d.upd with site := .bar20 }) := by
  simp [toBar20, hc]

theorem toBar20_none (hc : ¬ d.updOk = true) : toBar20 d = none := by
  simp [toBar20, hc]

/-- **The edge into the P store from the update**: a thread at pc 949 with the facts of a late
state is, after the update and the unpacks, at the barrier of the P store, or dead. -/
theorem cont_edge (hi : Inv L g d) (hl : LateSite d.site) {u : TState}
    (hAt : At u 949 (factsAt L g 949 d)) :
    (toBar20 d = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u) ∨
      ∃ d' t', toBar20 d = some (some d') ∧ Relation.ReflTransGen (Tau kernel asms L g) u t' ∧
        At t' d'.site.pc (facts L g d') ∧ Inv L g d' := by
  by_cases hc : d.updOk = true
  · obtain ⟨t', hr, ht'⟩ := ((segD_edge d) u hAt).1 hc
    exact .inr ⟨{ d.upd with site := .bar20 }, t', toBar20_ok hc, run_rtg hr, ht',
      inv_ml hi hl (s := .bar20) trivial (fun h => absurd h (by simp)) _ _
        (okVal_bytes (floatE_fma_four _ _ _)) (fun hr => by
          show ScoreWord d.mNew
          unfold D.mNew
          split
          · exact (hi.re hr).m
          · exact (hi.re hr).mn)⟩
  · exact .inl ⟨toBar20_none hc, ((segD_edge d) u hAt).2 hc⟩

/-- **`tcgen05.wait::st` after the O rescale's store** (pc 2329): the branch of pc 2330, the
update and the unpacks follow; a thread whose update faults is dead. -/
theorem step_waitStO (hi : Inv L g d) (hs : d.site = .waitStO) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2329 := by rw [hs]; rfl
  have hc' : kernel.code[2329]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_tmemWait_3)
  obtain rfl := (fires_tcWaitSt (hpc ▸ hf)).1
  have hlate : LateSite d.site := by rw [hs]; trivial
  have h1 : At (PTX.next t) 2330 (factsAt L g 2330 d) :=
    at_next_live (pc := 2329) (pc' := 2330) (hpc ▸ h) rfl rfl live_2329
  obtain ⟨t', hr', ht'⟩ := (seg_2330 d).rtg h1
  have hn : next L g d e = toBar20 d := by simp [next, hs]
  rcases cont_edge hi hlate ht' with ⟨hn', hd⟩ | ⟨d', t'', hd, hr, ha, hinv⟩
  · exact .inr ⟨hn.trans hn', dead_of_rtg hr' hd⟩
  · exact .inl (.inr ⟨d', t'', hn.trans hd, hr'.trans hr, ha, hinv⟩)

/-! ### Pieces with explicit facts, and the `xor` of the poll's parity -/

/-- **One instruction that writes `r` with the outcome `E`, onto explicit facts**: the facts
after it are the facts before, with `r` valued `v`; the thread is dead where `E` faults. -/
theorem segD_setF {pc r : Nat} {op : Op} {F : List (Nat × Value)} {α : Type} {E : Exec α}
    {f : α → Value} {v : Value}
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ t, At t pc F →
      execLocalA asms L g t op = E.map fun x => PTX.next (setReg t r (f x)))
    (hd : ∀ p ∈ F, p.1 ≠ r) (hv : ∀ x, E = .ok x → f x = v) :
    SegD kernel asms L g 1 pc F (pc + 1) ((r, v) :: F) (E.toBool = true) := by
  intro t ht
  have he := hex t ht
  refine ⟨fun hok => ?_, fun hno => ?_⟩
  · rcases hE : E with e | x
    · rw [hE] at hok; cases hok
    rw [hE] at he
    obtain rfl := hv x hE
    exact ⟨_, run_local hc hl ht he, At.set ht hd⟩
  · rcases hE : E with e | x
    · rw [hE] at he
      exact dead_of_error (hc.symm ▸ by rw [ht.1]) hl ht.2.2.2.1 he
    · rw [hE] at hno; exact absurd rfl hno

/-- `xor.b32 d, a, 1` of a word below `2 ^ 32`. -/
theorem exec_xor1 {t : TState} {dst a x : Nat}
    (hS : Assumption.SegFreePc asms t.pc) (ha : t.regs a = some (b32 x)) (hx : x < 2 ^ 32) :
    execLocalA asms L g t (.int ⟨.xor, .int .b 32, false, [some dst], [.reg a, .imm 1]⟩) =
      .ok (PTX.next (setReg t dst (b32 (x ^^^ 1)))) := by
  rw [hS.exec rfl, execLocalRule_of_none (asms_none (by simp) (by simp))]
  simp [execLocal, Op.rule, IntInstr.rule, execInt, DType.width, readReg, readBits, ha,
    b32, bind, Except.bind, pure, Except.pure]
  have h1 : truncBits 32 (BitVec.ofNat 64 x) = BitVec.ofNat 64 x := by
    apply BitVec.eq_of_toNat_eq
    simp only [truncBits, BitVec.toNat_ofNat]
    omega
  have h2 : truncBits 32 (1#64) = 1#64 := by decide
  rw [h1, h2]

/-! ### The first-iteration branch, the poll's parity and the rescale test -/

theorem okB_of_ok {E : Exec Bool} {b : Bool} (h : E = .ok b) : okB E = b := by
  rw [h]; rfl

/-- `1.0`, the immediate of the test. -/
abbrev one32 : Value := b32 1065353216

theorem live_2255_new : 1545 ∉ Flow.live 2255 ∧ 1546 ∉ Flow.live 2255 ∧ 170 ∉ Flow.live 2255 := by
  decide +kernel
theorem live_2255_old : 1544 ∈ Flow.live 2255 := by decide +kernel
theorem live_2255_949 : ∀ r ∈ Flow.live 949, r ∈ Flow.live 2255 := by decide +kernel
theorem live_2259_2255 : ∀ r ∈ Flow.live 2259, r ∈ Flow.live 2255 := by decide +kernel
theorem emu_2237 : Assumptions.emuSites.contains 2237 = false := by decide +kernel
theorem emu_2238 : Assumptions.emuSites.contains 2238 = false := by decide +kernel
theorem emu_2256 : Assumptions.emuSites.contains 2256 = false := by decide +kernel
theorem emu_2257 : Assumptions.emuSites.contains 2257 = false := by decide +kernel
theorem emu_2258 : Assumptions.emuSites.contains 2258 = false := by decide +kernel

theorem xor1_mod (i : Nat) : (i % 2) ^^^ 1 = (i + 1) % 2 := by
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h] <;> omega

/-- `xor.b32 %r1071, %r43, 1` (pc 2238), after the branch of pc 2237 that is not taken: the
parity of the `o_done` poll. -/
theorem seg_2238 (d : D) (F : List (Nat × Value)) (hF : ∀ p ∈ F, p.1 ≠ 1532)
    (h504 : (504, b32 (d.i % 2)) ∈ F) :
    Seg kernel asms L g 1 2238 F 2239 ((1532, b32 ((d.i + 1) % 2)) :: F) := by
  refine SegD.seg (segD_setF (r := 1532)
    (E := (.ok (b32 (d.i % 2 ^^^ 1)) : Exec Value)) (f := id) Flow.code_2238 rfl ?_ hF ?_) rfl
  · intro t ht
    have ha := holds_mem ht.2.2.2.2 h504
    exact exec_xor1 (by rw [ht.1]; exact segFree emu_2238) ha (by omega)
  · intro x hx
    cases hx
    simp only [id, xor1_mod]

theorem valueOf_r43 (d : D) : valueOf L g d 504 = b32 (d.i % 2) := by
  sm_vals

/-- The facts after the exchange: `%r1084` holds the received word. -/
abbrev F2255 (d : D) (recv : Value) : List (Nat × Value) :=
  (1545, recv) :: factsAt L g 2255 d

/-- `min.f32 %r1085, %r1083, %r1084` (pc 2256). -/
theorem segD_2256 (d : D) (recv : Value) :
    SegD kernel asms L g 1 2256 (F2255 (L := L) (g := g) d recv) 2257
      ((1546, okVal (b32 0) (minE [d.stg.m2, recv])) :: F2255 (L := L) (g := g) d recv)
      ((minE [d.stg.m2, recv]).toBool = true) := by
  obtain ⟨n1, n2, n3⟩ := live_2255_new
  refine segD_setF (r := 1546) (f := id) Flow.code_2256 rfl ?_ ?_ ?_
  · intro t ht
    have ha := holds_mem ht.2.2.2.2 (List.mem_cons_of_mem _ (Flow.mem_factsFrom
      (val := valueOf L g d) live_2255_old))
    have hb := holds_mem ht.2.2.2.2 (List.mem_cons_self ..)
    rw [valueOf_r1082] at ha
    exact exec_minE2 (idealAtSm (Or.inr (Or.inl rfl)) (by rw [ht.1]; exact emu_2256))
      (declineAtSm (Or.inr (Or.inl rfl)) (by rw [ht.1]; exact emu_2256) (by rw [ht.1]; decide)
        (by rw [ht.1]; decide) (by rw [ht.1]; decide)) ha hb
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp
    · exact facts_ne n2 p hp
  · intro x hx
    exact (okVal_of_ok hx).symm

/-- `setp.geu.f32 %p170, %r1085, 1.0` (pc 2257). -/
theorem segD_2257 (d : D) (recv v1 : Value) :
    SegD kernel asms L g 1 2257 ((1546, v1) :: F2255 (L := L) (g := g) d recv) 2258
      ((170, .pred (okB (setpE (.unord .ge) false v1 one32))) :: (1546, v1) ::
        F2255 (L := L) (g := g) d recv)
      ((setpE (.unord .ge) false v1 one32).toBool = true) := by
  obtain ⟨n1, n2, n3⟩ := live_2255_new
  refine segD_setF (r := 170) (f := Value.pred) Flow.code_2257 rfl ?_ ?_ ?_
  · intro t ht
    have ha := holds_mem ht.2.2.2.2 (List.mem_cons_self ..)
    exact exec_setpE (idealAtSm (Or.inr (Or.inr rfl)) (by rw [ht.1]; exact emu_2257))
      (declineAtSm (Or.inr (Or.inr rfl)) (by rw [ht.1]; exact emu_2257) (by rw [ht.1]; decide)
        (by rw [ht.1]; decide) (by rw [ht.1]; decide)) (Or.inr rfl) rfl rfl (OpndIs.reg ha)
      OpndIs.imm
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp
    · rcases List.mem_cons.mp hp with rfl | hp
      · simp
      · exact facts_ne n3 p hp
  · intro x hx
    rw [okB_of_ok hx]

/-- The facts of the state after the exchange, at the next pcs, only grow. -/
theorem holds_F2255 {R : Nat → Option Value} {recv : Value} {v1 : Value} {b : Bool}
    (h : Holds R ((170, .pred b) :: (1546, v1) :: F2255 (L := L) (g := g) d recv)) :
    Holds R (factsAt L g 2255 d) := h.2.2.2

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
