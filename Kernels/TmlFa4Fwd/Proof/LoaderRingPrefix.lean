-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRingTail
public import Kernels.TmlFa4Fwd.Proof.LoaderRingFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

structure RingCounterSite where
  head : Nat
  increment : Nat
  branch : Nat
  counter : Nat
  predicate : Nat

def ringCounterSite : Fin 2 → RingCounterSite
  | 0 => ⟨917, 1348, 1352, 7174, 199⟩
  | 1 => ⟨1396, 1741, 1743, 7181, 230⟩

def counterLimit : Fin 2 → Nat → Nat
  | 0 => fun trips => min trips 9
  | 1 => id

private theorem ringSiteBounds (j : Fin 2) :
    let site := ringCounterSite j
    917 ≤ site.head ∧ site.head < site.increment ∧ site.increment < site.branch ∧
      site.branch < 1744 ∧ site.counter ≠ 1091 := by
  fin_cases j <;> decide

private theorem ringCounterBranch (j : Fin 2) :
    let site := ringCounterSite j
    kernel.code[site.branch]? = some ⟨some (site.predicate, false), .bra site.head false⟩ := by
  fin_cases j
  · exact Flow.code_1352
  · exact Flow.code_1743

private theorem ringCounterBranchRun (j : Fin 2) {l : Launch} {g : Nat} {s : TState}
    {k trips : Nat} {pick : Bool}
    (hs : At s (ringCounterSite j).branch
      [((ringCounterSite j).predicate, .pred pick),
       ((ringCounterSite j).counter, b32 k), (1091, b32 trips)]) :
    ∃ u, run kernel Assumptions.all l g 1 s = some u ∧
      At u (if pick then (ringCounterSite j).head else (ringCounterSite j).branch + 1)
        [((ringCounterSite j).counter, b32 k), (1091, b32 trips)] := by
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    (ringCounterBranch j) pick hs hs.2.2.2.2.1 (by simp)
  have hB := ringSiteBounds j
  have hb := hs.1
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by omega) (by omega)
    hb (by simp) rfl hu
  exact ⟨u, huA, hU.mono hU.2.2.2.2.2⟩

private theorem counterTailSlice (j : Fin 2) :
    let site := ringCounterSite j
    let span := site.branch - site.increment
    ((kernel.code.drop site.increment).take span).all
      (fun i => !([1091] : List Nat).any (fun r => (writesRegs i.op).contains r)) = true ∧
    ((kernel.code.drop site.increment).take (span - 1)).all
      (fun i => Epilogue.schedulerFallsThrough i.op) = true := by
  fin_cases j <;> constructor <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem counterTailCore (j : Fin 2) (l : Launch) (g : Nat) {k trips : Nat}
    (ht : trips < 2 ^ 31) (hk : k < counterLimit j trips) :
    let site := ringCounterSite j
    Seg kernel [] l g (site.branch - site.increment) site.increment
      [(site.counter, b32 k), (1091, b32 trips)] site.branch
      [(site.predicate, .pred (decide (k + 1 < counterLimit j trips))),
       (site.counter, b32 (k + 1))] := by
  fin_cases j
  · exact warmRingCondition l g (i := k) (trips := trips) ht hk
  · exact steadyRingCondition l g (i := k) (trips := trips) ht hk

private theorem counterTailRun (j : Fin 2) {l : Launch} {g k trips : Nat} {s : TState}
    (ht : trips < 2 ^ 31) (hk : k < counterLimit j trips)
    (hs : At s (ringCounterSite j).increment
      [((ringCounterSite j).counter, b32 k), (1091, b32 trips)]) :
    let site := ringCounterSite j
    let running := decide (k + 1 < counterLimit j trips)
    ∃ u, run kernel Assumptions.all l g (site.branch + 1 - site.increment) s = some u ∧
      At u (if running then site.head else site.branch + 1)
        [(site.counter, b32 (k + 1)), (1091, b32 trips)] := by
  dsimp only
  let site := ringCounterSite j
  let rest := site.branch - site.increment
  obtain ⟨v, hv, hvAt⟩ := counterTailCore j l g ht hk s hs
  have hB : 917 ≤ site.head ∧ site.head < site.increment ∧
      site.increment < site.branch ∧ site.branch < 1744 ∧ site.counter ≠ 1091 :=
    ringSiteBounds j
  have hPc : s.pc = site.increment := hs.1
  have hFrameCode : ((kernel.code.drop site.increment).take rest).all
      (fun i => ([1091] : List Nat).all (fun r => !(writesRegs i.op).contains r)) = true := by
    simpa using (counterTailSlice j).1
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := [1091]) (by omega) (by omega)
    hPc hFrameCode (counterTailSlice j).2 hv
  have hReg : v.regs 1091 = some (b32 trips) :=
    (hvFrame 1091 (by simp)).trans hs.2.2.2.2.2.1
  have hvIn := hvAt.mono (G :=
    [(site.predicate, .pred (decide (k + 1 < counterLimit j trips))),
      (site.counter, b32 (k + 1)), (1091, b32 trips)])
    ⟨hvAt.2.2.2.2.1, hvAt.2.2.2.2.2.1, hReg, trivial⟩
  obtain ⟨u, hu, hU⟩ := ringCounterBranchRun j (l := l) (g := g) hvIn
  have hStep := run_comp hvA hu
  have hN : rest + 1 = site.branch + 1 - site.increment := by
    have hLt : site.increment < site.branch := hB.2.2.1
    dsimp only [rest]
    omega
  exact ⟨u, hN ▸ hStep, hU⟩

/-- A known local run cuts an actual walk without consuming events, unless the walk
ends before that run finishes. -/
theorem loaderLocalWalkCut {l : Launch} {g n : Nat} {s u : TState}
    {es : List Event} {vs : List Visit}
    (hr : run kernel Assumptions.all l g n s = some u)
    (hw : Walk kernel Assumptions.all l g s es vs) :
    vs.length < n ∨ ∃ pre tail, vs = pre ++ tail ∧ pre.length = n ∧
      Walk kernel Assumptions.all l g u es tail := by
  induction n generalizing s es vs with
  | zero =>
    obtain rfl := Option.some.inj hr
    exact .inr ⟨[], vs, rfl, rfl, hw⟩
  | succ n ih =>
    simp only [run] at hr
    cases ht : tauStep kernel Assumptions.all l g s with
    | none => simp [ht] at hr
    | some v =>
      rw [ht, Option.bind_some] at hr
      have ht' := tauStep_iff.mp ht
      cases hw with
      | stop => exact .inl (Nat.zero_lt_succ _)
      | tau ht2 hh =>
        have hSame := Option.some.inj ((tauStep_iff.mpr ht2).symm.trans ht)
        subst v
        rcases ih hr hh with hShort | ⟨pre, tail, hEq, hLen, hTail⟩
        · exact .inl (by simp [hShort])
        · exact .inr ⟨_ :: pre, tail, by rw [hEq]; rfl, by simp [hLen], hTail⟩
      | ev he _ =>
        obtain ⟨_, ho, _⟩ := he
        unfold Tau at ht'
        rw [ho] at ht'
        cases ht'
      | last he =>
        obtain ⟨_, ho, _⟩ := he
        unfold Tau at ht'
        rw [ho] at ht'
        cases ht'

private def ringEarlyOp (site : RingCounterSite) (ins : Instr) : Bool :=
  !(loaderRingWrites ins.op).contains site.counter &&
    !(loaderRingWrites ins.op).contains 1091 &&
    (match ins.op with
    | .bra target _ => site.head ≤ target &&
        (target ≤ site.increment || site.branch < target)
    | .brx .. => false
    | _ => true)

private theorem ringEarlyCode (j : Fin 2) :
    let site := ringCounterSite j
    ((kernel.code.drop site.head).take (site.increment - site.head)).all
      (ringEarlyOp site) = true := by
  fin_cases j <;> set_option maxRecDepth 100000 in decide +kernel

private theorem ringEarlyInstr (j : Fin 2) {pc : Nat} {ins : Instr}
    (hl : (ringCounterSite j).head ≤ pc) (hh : pc < (ringCounterSite j).increment)
    (hc : kernel.code[pc]? = some ins) : ringEarlyOp (ringCounterSite j) ins = true := by
  let site := ringCounterSite j
  have hGet : ((kernel.code.drop site.head).take (site.increment - site.head))[pc - site.head]? =
      some ins := by
    have hLo : site.head ≤ pc := hl
    have hHi : pc < site.increment := hh
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
    exact hc
  exact List.all_eq_true.mp (ringEarlyCode j) ins (List.mem_of_getElem? hGet)

private theorem earlyLanding {site : RingCounterSite} {op : Op} {pc : Nat}
    (hC : (match op with
      | .bra target _ => site.head ≤ target && (target ≤ site.increment || site.branch < target)
      | .brx .. => false
      | _ => true) = true) :
    (∀ p, ¬ BrxTarget op p) ∧
      (nextPc op pc = pc + 1 ∨ (site.head ≤ nextPc op pc ∧
        (nextPc op pc ≤ site.increment ∨ site.branch < nextPc op pc))) := by
  cases op <;> simp only [Bool.false_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hC
  case bra target uni => exact ⟨by simp [BrxTarget], .inr hC⟩
  all_goals exact ⟨by simp [BrxTarget], .inl rfl⟩

private theorem ringEarlyStep (j : Fin 2) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hl : (ringCounterSite j).head ≤ s.pc)
    (hh : s.pc < (ringCounterSite j).increment) (hs : RingShape s)
    (h : WStep kernel Assumptions.all l g s e u) :
    let site := ringCounterSite j
    RingShape u ∧
      u.regs site.counter = s.regs site.counter ∧
      u.regs 1091 = s.regs 1091 ∧
      site.head ≤ u.pc ∧ (u.pc ≤ site.increment ∨ site.branch < u.pc) := by
  let site := ringCounterSite j
  have hLo : site.head ≤ s.pc := hl
  have hHi : s.pc < site.increment := hh
  have hBounds : 917 ≤ site.head ∧ site.head < site.increment ∧
      site.increment < site.branch ∧ site.branch < 1744 ∧ site.counter ≠ 1091 := ringSiteBounds j
  have hLo' : 917 ≤ s.pc := by omega
  have hHi' : s.pc < 1744 := by omega
  have hCounter : ∀ ins, kernel.code[s.pc]? = some ins →
      site.counter ∉ loaderRingWrites ins.op := by
    intro ins hC
    have hCheck := ringEarlyInstr j hl hh hC
    simpa [ringEarlyOp, site] using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hCheck).1).1
  have hTrips : ∀ ins, kernel.code[s.pc]? = some ins → 1091 ∉ loaderRingWrites ins.op := by
    intro ins hC
    have hCheck := ringEarlyInstr j hl hh hC
    simpa [ringEarlyOp, site] using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hCheck).1).2
  refine ⟨ringStepShape hLo' hHi' hs h, ringStepRegs hLo' hHi' hCounter h,
    ringStepRegs hLo' hHi' hTrips h, ?_⟩
  change site.head ≤ u.pc ∧ (u.pc ≤ site.increment ∨ site.branch < u.pc)
  rcases h with ⟨-, ht⟩ | ⟨ev, -, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore (by omega) (by omega)]
    obtain ⟨ins, hc⟩ := tau_core_has_code ht'
    have hCheck := ringEarlyInstr j hl hh hc
    obtain ⟨hNoBrx, hN⟩ := earlyLanding (Bool.and_eq_true_iff.mp hCheck).2 (pc := s.pc)
    rcases tau_core_frame hc ht' with rfl | hf
    · change site.head ≤ s.pc + 1 ∧ (s.pc + 1 ≤ site.increment ∨ site.branch < s.pc + 1)
      omega
    · have hPc := hf.pc.resolve_right (hNoBrx _)
      rw [hPc]
      rcases hN with hLanding | hLanding
      · rw [hLanding]
        omega
      · exact hLanding
  · have he' : EStep kernel [] l g s ev (some u) := by
      obtain ⟨tmpl, ht, hf⟩ := he
      exact ⟨tmpl, by rwa [← loaderOutCore (by omega) (by omega)], hf⟩
    rcases (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2 with hp | hp <;> omega

def ringBranchVisits (j : Fin 2) (visits : List Visit) : Nat :=
  let site := ringCounterSite j
  (visits.takeWhile fun v => decide (site.head ≤ v.pc ∧ v.pc ≤ site.branch)).countP
    (fun v => v.pc == site.branch)

private theorem ringVisitsOutside (j : Fin 2) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hout : ¬ ((ringCounterSite j).head ≤ s.pc ∧ s.pc ≤ (ringCounterSite j).branch)) :
    ringBranchVisits j vs = 0 := by
  cases hw <;> simp only [ringBranchVisits, List.takeWhile_nil, List.takeWhile_cons,
    visit_pc, List.countP_nil]
  all_goals
    split
    · rename_i h
      exact (hout (of_decide_eq_true h)).elim
    · rfl

private theorem ringVisitsBefore (j : Fin 2) {l : Launch} {g : Nat} {s : TState}
    (hs : (ringCounterSite j).head ≤ s.pc ∧ s.pc < (ringCounterSite j).branch)
    (e : Option Event) (vs : List Visit) :
    ringBranchVisits j (visit kernel l g s e :: vs) = ringBranchVisits j vs := by
  simp only [ringBranchVisits, List.takeWhile_cons, visit_pc]
  split
  · rw [List.countP_cons, visit_pc]
    simp [hs.2.ne]
  · rename_i h
    exact (h (decide_eq_true ⟨hs.1, hs.2.le⟩)).elim

private theorem ringFindIncrement (j : Fin 2) {l : Launch} {g k trips : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hp : (ringCounterSite j).head ≤ s.pc ∧ s.pc ≤ (ringCounterSite j).increment)
    (hs : RingShape s)
    (hK : s.regs (ringCounterSite j).counter = some (b32 k))
    (hTrip : s.regs 1091 = some (b32 trips)) :
    ringBranchVisits j vs = 0 ∨ ∃ u rest tail, ringBranchVisits j vs = ringBranchVisits j tail ∧
      u.pc = (ringCounterSite j).increment ∧ RingShape u ∧
      u.regs (ringCounterSite j).counter = some (b32 k) ∧ u.regs 1091 = some (b32 trips) ∧
      Walk kernel Assumptions.all l g u rest tail := by
  let site := ringCounterSite j
  have hBounds : 917 ≤ site.head ∧ site.head < site.increment ∧ site.increment < site.branch ∧
      site.branch < 1744 ∧ site.counter ≠ 1091 := ringSiteBounds j
  have extend {t u : TState} {e : Option Event} {rest : List Event} {tail : List Visit}
      (hW : Walk kernel Assumptions.all l g u rest tail)
      (hP : site.head ≤ t.pc ∧ t.pc ≤ site.increment)
      (hShape : RingShape t)
      (hI : t.regs site.counter = some (b32 k)) (hT : t.regs 1091 = some (b32 trips))
      (hStep : WStep kernel Assumptions.all l g t e u)
      (hw0 : Walk kernel Assumptions.all l g t (e.toList ++ rest)
        (visit kernel l g t e :: tail))
      (ih : (site.head ≤ u.pc ∧ u.pc ≤ site.increment) →
        RingShape u → u.regs site.counter = some (b32 k) → u.regs 1091 = some (b32 trips) →
        ringBranchVisits j tail = 0 ∨ ∃ v after suffix,
          ringBranchVisits j tail = ringBranchVisits j suffix ∧
          v.pc = site.increment ∧ RingShape v ∧ v.regs site.counter = some (b32 k) ∧
          v.regs 1091 = some (b32 trips) ∧ Walk kernel Assumptions.all l g v after suffix) :
      ringBranchVisits j (visit kernel l g t e :: tail) = 0 ∨ ∃ v after suffix,
        ringBranchVisits j (visit kernel l g t e :: tail) = ringBranchVisits j suffix ∧
        v.pc = site.increment ∧ RingShape v ∧ v.regs site.counter = some (b32 k) ∧
        v.regs 1091 = some (b32 trips) ∧ Walk kernel Assumptions.all l g v after suffix := by
    by_cases hPc : t.pc = site.increment
    · exact .inr ⟨t, _, _, rfl, hPc, hShape, hI, hT, hw0⟩
    have hlt : t.pc < site.increment := by omega
    rw [ringVisitsBefore j ⟨hP.1, by change t.pc < site.branch; omega⟩]
    obtain ⟨hNext, hIdx, hLim, hl, hh | hh⟩ := ringEarlyStep j hP.1 hlt hShape hStep
    · exact ih ⟨hl, hh⟩ hNext (hIdx.trans hI) (hLim.trans hT)
    · exact .inl (ringVisitsOutside j hW (by
        change ¬ (site.head ≤ u.pc ∧ u.pc ≤ site.branch)
        change site.branch < u.pc at hh
        omega))
  induction hw with
  | stop => exact .inl rfl
  | tau ht hh ih => exact extend hh hp hs hK hTrip (.inl ⟨rfl, ht⟩) (.tau ht hh) ih
  | ev he hh ih => exact extend hh hp hs hK hTrip (.inr ⟨_, rfl, he⟩) (.ev he hh) ih
  | @last s e he =>
    have hPc : s.pc ≤ site.increment := hp.2
    rw [ringVisitsBefore j ⟨hp.1, by change s.pc < site.branch; omega⟩]
    exact .inl rfl

private theorem ringVisitsLength (j : Fin 2) (vs : List Visit) :
    ringBranchVisits j vs ≤ vs.length := by
  apply (List.countP_le_length (p := _)).trans
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [List.takeWhile_cons]
    split
    · exact Nat.succ_le_succ ih
    · exact Nat.zero_le _

private theorem ringVisitsAppend (j : Fin 2) (pre tail : List Visit) :
    ringBranchVisits j (pre ++ tail) ≤ pre.length + ringBranchVisits j tail := by
  induction pre with
  | nil => simp
  | cons v pre ih =>
    unfold ringBranchVisits at ih ⊢
    dsimp only at ih ⊢
    simp only [List.cons_append, List.takeWhile_cons, List.length_cons]
    split
    · rw [List.countP_cons]
      split <;> omega
    · simp

private theorem ringFaultAtIncrement (j : Fin 2) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hp : s.pc = (ringCounterSite j).increment) (hf : s.fault ≠ none) :
    ringBranchVisits j vs = 0 := by
  cases h : s.fault
  · exact (hf h).elim
  case some f =>
    have hb := ringSiteBounds j
    cases hw with
    | stop => rfl
    | tau ht _ => simp [Tau, out, h] at ht
    | ev hr _ =>
      obtain ⟨tmpl, ht, hf⟩ := hr
      simp only [out, h, Out.ev.injEq] at ht
      subst tmpl
      cases hf.2
    | last _ =>
      rw [ringVisitsBefore j ⟨by omega, by omega⟩]
      rfl

private theorem incrementSubZero (j : Fin 2) {s : TState}
    (hp : s.pc = (ringCounterSite j).increment) (hs : RingShape s) : s.sub = 0 := by
  by_contra hPos
  obtain ⟨op, hi, _, hl⟩ := hs.1.2 (by have := hs.1.1; omega)
  rw [hp] at hi
  fin_cases j
  · change kernel.code[1348]? = _ at hi
    rw [Flow.code_1348] at hi
    have ho := congrArg Instr.op (Option.some.inj hi)
    dsimp only at ho
    rw [← ho] at hl
    cases hl
  · change kernel.code[1741]? = _ at hi
    rw [Flow.code_1741] at hi
    have ho := congrArg Instr.op (Option.some.inj hi)
    dsimp only at ho
    rw [← ho] at hl
    cases hl

private theorem ringCounterBound (j : Fin 2) {l : Launch} {g trips : Nat}
    (hTrip : trips < 2 ^ 31) (n : Nat)
    {s : TState} {es : List Event} {vs : List Visit} {k : Nat}
    (hN : counterLimit j trips - k = n) (hk : k < counterLimit j trips)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hp : (ringCounterSite j).head ≤ s.pc ∧ s.pc ≤ (ringCounterSite j).increment)
    (hs : RingShape s)
    (hkReg : s.regs (ringCounterSite j).counter = some (b32 k))
    (ht : s.regs 1091 = some (b32 trips)) :
    ringBranchVisits j vs ≤ 5 * (n + 1) := by
  induction n using Nat.strong_induction_on generalizing s es vs k with
  | h n ih =>
    let site := ringCounterSite j
    have hBounds : 917 ≤ site.head ∧ site.head < site.increment ∧
        site.increment < site.branch ∧ site.branch < 1744 ∧ site.counter ≠ 1091 := ringSiteBounds j
    have hSpan : site.branch + 1 - site.increment ≤ 5 := by fin_cases j <;> decide
    rcases ringFindIncrement j hw hp hs hkReg ht with hZero |
      ⟨t, rest, tail, hCount, hpc, hShape, hK, hT, hwTail⟩
    · rw [hZero]
      exact Nat.zero_le _
    rw [hCount]
    by_cases hf : t.fault = none
    swap
    · rw [ringFaultAtIncrement j hwTail hpc hf]
      exact Nat.zero_le _
    have hZ := incrementSubZero j hpc hShape
    have hAt : At t site.increment [(site.counter, b32 k), (1091, b32 trips)] :=
      ⟨hpc, hZ, hShape.2 hZ, hf, hK, hT, trivial⟩
    obtain ⟨u, hu, hU⟩ := counterTailRun j hTrip hk hAt
    rcases loaderLocalWalkCut hu hwTail with hShort | ⟨pre, suffix, hTrace, hPre, hSuffix⟩
    · have hSize := ringVisitsLength j tail
      change tail.length < site.branch + 1 - site.increment at hShort
      omega
    rw [hTrace]
    change pre.length = site.branch + 1 - site.increment at hPre
    have hSplit := ringVisitsAppend j pre suffix
    by_cases hMore : k + 1 < counterLimit j trips
    · have hNext : At u site.head [(site.counter, b32 (k + 1)), (1091, b32 trips)] := by
        simpa [hMore] using hU
      have hf' : RingShape u := by
        exact ⟨⟨by rw [hNext.2.1]; decide,
          fun h => (Nat.zero_ne_one (hNext.2.1.symm.trans h)).elim⟩,
          fun _ => hNext.2.2.1⟩
      have hN' : counterLimit j trips - (k + 1) < n := by omega
      have hPc := hNext.1
      have hIp : (ringCounterSite j).head ≤ u.pc ∧ u.pc ≤ (ringCounterSite j).increment := by
        exact ⟨hPc.ge, hPc.trans_le hBounds.2.1.le⟩
      have hBound := ih _ hN' rfl hMore hSuffix hIp hf'
        hNext.2.2.2.2.1 hNext.2.2.2.2.2.1
      omega
    · have hEnd : u.pc = site.branch + 1 := by simpa [hMore] using hU.1
      have hNone := ringVisitsOutside j hSuffix (by
        change ¬ (site.head ≤ u.pc ∧ u.pc ≤ site.branch)
        omega)
      omega

/-- From either ring entry, every finite actual prefix has a branch-visit bound
in terms of the decoded remaining trip counter. -/
theorem ringVisitsFromEntry (j : Fin 2) {l : Launch} {g k trips : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hTrip : trips < 2 ^ 31) (hk : k < counterLimit j trips)
    (hs : At s (ringCounterSite j).head
      [((ringCounterSite j).counter, b32 k), (1091, b32 trips)]) :
    ringBranchVisits j vs ≤ 5 * (counterLimit j trips - k + 1) := by
  have hP : (ringCounterSite j).head ≤ s.pc ∧ s.pc ≤ (ringCounterSite j).increment :=
    ⟨hs.1.ge, hs.1.trans_le (ringSiteBounds j).2.1.le⟩
  have hShape : RingShape s :=
    ⟨⟨by rw [hs.2.1]; decide, fun h => (Nat.zero_ne_one (hs.2.1.symm.trans h)).elim⟩,
      fun _ => hs.2.2.1⟩
  exact ringCounterBound j hTrip _ rfl hk hw hP hShape hs.2.2.2.2.1 hs.2.2.2.2.2.1

/-- A transition inside the warm ring preserves the visible trip bound and iteration word. -/
theorem warmBodyStep {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 917 ≤ s.pc) (hHi : s.pc < 1348) (hs : RingShape s)
    (hStep : WStep kernel Assumptions.all l g s e u) :
    RingShape u ∧ u.regs 7174 = s.regs 7174 ∧ u.regs 1091 = s.regs 1091 ∧
      917 ≤ u.pc ∧ (u.pc ≤ 1348 ∨ 1352 < u.pc) :=
  ringEarlyStep 0 hLo hHi hs hStep

/-- At the warm ring increment, the decoded counter and branch advance exactly one round. -/
theorem warmCounterStep {l : Launch} {g k trips : Nat} {s : TState}
    (hTrip : trips < 2^31) (hk : k < min trips 9) (hp : s.pc = 1348) (hs : RingShape s)
    (hf : s.fault = none) (hK : s.regs 7174 = some (b32 k))
    (hT : s.regs 1091 = some (b32 trips)) :
    ∃ u, run kernel Assumptions.all l g 5 s = some u ∧
      At u (if k+1 < min trips 9 then 917 else 1353)
        [(7174,b32 (k+1)), (1091,b32 trips)] := by
  have hz := incrementSubZero 0 hp hs
  have ha : At s 1348 [(7174,b32 k),(1091,b32 trips)] :=
    ⟨hp,hz,hs.2 hz,hf,hK,hT,trivial⟩
  simpa [ringCounterSite,counterLimit] using counterTailRun 0 (l := l) (g := g) hTrip hk ha

end
end PTX.Kernels.TmlFa4Fwd.Loader
