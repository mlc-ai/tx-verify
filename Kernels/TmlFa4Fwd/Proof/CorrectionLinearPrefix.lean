-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionPrefixEvents

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Mma Softmax

noncomputable section

/-- The intervals between correction loop backedges and acquire spins. -/
def correctionLinearRegion : Fin 10 → Mma.RoleRegion
  | 0 => ⟨7746, 7807, [7807, 7864]⟩
  | 1 => ⟨7864, 7989, [7989, 9201]⟩
  | 2 => ⟨7989, 8005, [8005, 8447]⟩
  | 3 => ⟨8006, 8444, [8444]⟩
  | 4 => ⟨8447, 8473, [8473]⟩
  | 5 => ⟨8479, 8769, [8769]⟩
  | 6 => ⟨8775, 9083, [9083]⟩
  | 7 => ⟨9083, 9130, [9130, 9187]⟩
  | 8 => ⟨9187, 9201, [9201]⟩
  | 9 => ⟨9204, 9206, [9206]⟩

def correctionLinearProtected (region : Fin 10) : Nat :=
  if region = 3 then 7278 else 0

private def correctionRet : Op → Bool
  | .ret => true
  | _ => false

private def correctionLinearCode (i : Fin 10) (pair : Instr × Nat) : Bool :=
  let region := correctionLinearRegion i
  let r := correctionLinearProtected i
  let ins := pair.1
  let pc := pair.2
  (ins.op.isLocal || correctionReturningOp ins.op || correctionRet ins.op) &&
    !(Assumptions.swExp2Sites.contains pc) && !(scoreEventWrites ins.op).contains r &&
    !(writesRegs ins.op).contains r &&
    (match ins.op with
      | .bra dest _ => pc < dest && (dest < region.hi || region.exits.contains dest)
      | .brx .. => false
      | _ => true)

private theorem correctionCodeAt (i : Fin 10) {pc : Nat} {ins : Instr}
    (hLo : (correctionLinearRegion i).lo ≤ pc) (hHi : pc < (correctionLinearRegion i).hi)
    (hc : kernel.code[pc]? = some ins) : correctionLinearCode i (ins, pc) = true := by
  let site := correctionLinearRegion i
  let code := ((kernel.code.drop site.lo).take (site.hi - site.lo)).zipIdx site.lo
  have hAll : code.all (correctionLinearCode i) = true := by
    fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl
  have hm : (ins, pc) ∈ code := by
    apply List.mem_of_getElem? (i := pc - site.lo)
    have hp : site.lo ≤ pc := hLo
    have hUpper : pc < site.hi := hHi
    dsimp only [code]
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hp, hc]
    rfl
  exact List.all_eq_true.mp hAll _ hm

private theorem correctionForwardIn (i : Fin 10) {pc : Nat}
    (hLo : (correctionLinearRegion i).lo ≤ pc) (hHi : pc < (correctionLinearRegion i).hi) :
    (correctionLinearRegion i).lo ≤ pc + 1 ∧
      (pc + 1 < (correctionLinearRegion i).hi ∨ pc + 1 ∈ (correctionLinearRegion i).exits) := by
  refine ⟨by omega, ?_⟩
  by_cases h : pc + 1 < (correctionLinearRegion i).hi
  · exact .inl h
  · have he : pc + 1 = (correctionLinearRegion i).hi := by omega
    rw [he]
    fin_cases i <;> decide

private theorem eventAtHealthy {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (he : EStep kernel Assumptions.all l g s e (some u)) : s.fault = none := by
  cases h : s.fault
  · rfl
  · obtain ⟨m, hm, hf⟩ := he
    simp only [out, h, Out.ev.injEq] at hm
    subst m
    cases hf.2

structure CorrectionLinearProgress (s u : TState) : Prop where
  sub : u.sub ≤ 3
  pc : s.pc < u.pc ∧ u.fault = s.fault ∨
    u.pc = s.pc ∧ (u.sub = s.sub + 1 ∨ u.fault.isSome)

/-- A returning transition in a linear correction interval advances its PC, advances
inside one instruction, or records a fault. The protected counter survives. -/
theorem correctionLinearStep (i : Fin 10) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hLo : (correctionLinearRegion i).lo ≤ s.pc)
    (hHi : s.pc < (correctionLinearRegion i).hi) (hSub : s.sub ≤ 3)
    (hStep : WStep kernel Assumptions.all l g s e u) :
    CorrectionLinearProgress s u ∧
      ((correctionLinearRegion i).lo ≤ u.pc ∧ u.pc < (correctionLinearRegion i).hi ∨
        u.pc ∈ (correctionLinearRegion i).exits ∧ u.fault = none) ∧
      u.regs (correctionLinearProtected i) = s.regs (correctionLinearProtected i) := by
  let site := correctionLinearRegion i
  have hNext := correctionForwardIn i hLo hHi
  have advance (hPc : u.pc = s.pc + 1) (hf : u.fault = none) :
      site.lo ≤ u.pc ∧ u.pc < site.hi ∨ u.pc ∈ site.exits ∧ u.fault = none := by
    rw [hPc]
    exact hNext.2.elim (fun hh => .inl ⟨hNext.1, hh⟩) (fun he => .inr ⟨he, hf⟩)
  rcases hStep with ⟨_, ht⟩ | ⟨ev, _, he⟩
  · have hPc := (correctionTauFrame (l := l) (g := g) (s := s) (u := u))
    have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      have hl : 7746 ≤ s.pc := by fin_cases i <;> simp [correctionLinearRegion] at hLo <;> omega
      omega
    obtain ⟨ins, hc, hFault, ⟨rfl, _⟩ | ⟨_, _, hF⟩⟩ := hPc hOff ht
    · exact ⟨⟨by simp [skip], .inl ⟨Nat.lt_succ_self _, rfl⟩⟩, advance rfl hFault, rfl⟩
    have hC := correctionCodeAt i hLo hHi hc
    simp only [correctionLinearCode, Bool.and_eq_true, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at hC
    have hKeep := hF.regs _ hC.1.2
    have hf := hF.fault.trans hFault
    have hSubU := hF.sub ▸ hSub
    have hp := hF.pc
    cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hp
    case bra dest aligned =>
      have hBranch : s.pc < dest ∧ (dest < site.hi ∨ dest ∈ site.exits) := by
        simpa only [ho, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] using hC.2
      have hL : site.lo ≤ dest ∧ dest < site.hi ∨ dest ∈ site.exits ∧ u.fault = none :=
        hBranch.2.elim (fun h => .inl ⟨le_trans hLo hBranch.1.le, h⟩) (fun h => .inr ⟨h, hf⟩)
      exact ⟨⟨hSubU, .inl ⟨by omega, hF.fault⟩⟩, by rwa [hp], hKeep⟩
    case brx => simp [ho] at hC
    all_goals exact ⟨⟨hSubU, .inl ⟨by omega, hF.fault⟩⟩, advance hp hf, hKeep⟩
  · obtain ⟨ins, hc, hLoc, hFire⟩ := estep_event_source he
    have hC := correctionCodeAt i hLo hHi hc
    simp only [correctionLinearCode, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, hLoc,
      Bool.false_eq_true, false_or] at hC
    rcases hC.1.1.1.1 with hOp | hRet
    · obtain ⟨hP, hR⟩ := correctionEventProgress hc hOp hSub hC.1.1.2 he
      rcases hP.pc with ⟨hp, hf⟩ | ⟨hp, hSubstep⟩
      · exact ⟨⟨hP.sub, .inl ⟨by omega, hf⟩⟩,
          advance hp (hf.trans (eventAtHealthy he)), hR⟩
      · exact ⟨⟨hP.sub, .inr ⟨hp, hSubstep⟩⟩, .inl ⟨hp ▸ hLo, hp ▸ hHi⟩, hR⟩
    · have hRet' : ins.op = .ret := by cases ho : ins.op <;> simp_all [correctionRet]
      rw [hRet'] at hFire
      cases hFire.2

private def forwardFuel (hi : Nat) (s : TState) : Nat :=
  if s.fault.isSome then 1 else 5 * (hi - s.pc) + (3 - s.sub) + 1

private theorem fuelDecreases {hi : Nat} {s u : TState}
    (hS : s.pc < hi) (hU : u.pc < hi) (hSub : s.sub ≤ 3)
    (hH : s.fault = none) (hStep : CorrectionLinearProgress s u) :
    forwardFuel hi u + 1 ≤ forwardFuel hi s := by
  have hSubU := hStep.sub
  unfold forwardFuel
  rw [hH]
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rcases hStep.pc with ⟨hp, hf⟩ | ⟨hp, hx | hx⟩
  · rw [hf, hH]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    omega
  · rw [hp, hx]
    split <;> omega
  · rw [hp]
    simp only [hx, ↓reduceIte]
    omega

theorem countedCorrectionCons {l : Launch} {g cutoff : Nat} {s : TState}
    {vs : List Visit} (h : s.pc < cutoff) (e : Option Event) :
    countedUntil cutoff (visit kernel l g s e :: vs) =
      countedUntil cutoff vs + (if (e.map Event.counts).getD false then 1 else 0) := by
  cases e <;> simp [countedUntil, visit_pc, visit_ev, h, List.filterMap_cons, List.countP_cons]

theorem countedPastCut {l : Launch} {g cutoff : Nat} {s : TState}
    {events : List Event} {visits : List Visit} (h : ¬ s.pc < cutoff)
    (hw : Walk kernel Assumptions.all l g s events visits) : countedUntil cutoff visits = 0 := by
  cases hw <;> simp [countedUntil, visit_pc, h]

private theorem exitingCorrectionRegion (i : Fin 10) {pc : Nat}
    (h : pc ∈ (correctionLinearRegion i).exits) : ¬ pc < (correctionLinearRegion i).hi := by
  fin_cases i <;> simp [correctionLinearRegion] at h ⊢ <;> omega

/-- Count all events on a linear interval up to its first exit, including arbitrary
prefixes and a terminal fault. A vector store or an implicit load wait takes sub-steps. -/
theorem correctionLinearBound (i : Fin 10) {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hLo : (correctionLinearRegion i).lo ≤ s.pc) (hHi : s.pc < (correctionLinearRegion i).hi)
    (hSub : s.sub ≤ 3) :
    countedUntil (correctionLinearRegion i).hi visits ≤
      5 * ((correctionLinearRegion i).hi - s.pc) + 4 := by
  have hCount : countedUntil (correctionLinearRegion i).hi visits ≤
      forwardFuel (correctionLinearRegion i).hi s := by
    induction hw with
    | stop => simp [countedUntil]
    | @tau s u events visits ht hw ih =>
      have hs : WStep kernel Assumptions.all l g s none u := .inl ⟨rfl, ht⟩
      obtain ⟨hP, hRange, _⟩ := correctionLinearStep i hLo hHi hSub hs
      have hHealthy : s.fault = none := by
        cases h : s.fault
        · rfl
        · simp [Tau, out, h] at ht
      have hE := countedCorrectionCons (l := l) (g := g) (vs := visits) hHi none
      simp only [Option.map_none, Option.getD_none, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero] at hE
      rw [hE]
      rcases hRange with ⟨hl, hh⟩ | ⟨he, _⟩
      · exact (ih hl hh hP.sub).trans ((Nat.le_succ _).trans
          (fuelDecreases hHi hh hSub hHealthy hP))
      · rw [countedPastCut (exitingCorrectionRegion i he) hw]
        exact Nat.zero_le _
    | @ev s u e events visits he hw ih =>
      have hs : WStep kernel Assumptions.all l g s (some e) u := .inr ⟨e, rfl, he⟩
      obtain ⟨hP, hRange, _⟩ := correctionLinearStep i hLo hHi hSub hs
      rw [countedCorrectionCons hHi (some e)]
      rcases hRange with ⟨hl, hh⟩ | ⟨hExit, _⟩
      · have hTail := ih hl hh hP.sub
        have hFuel := fuelDecreases hHi hh hSub (eventAtHealthy he) hP
        split <;> omega
      · rw [countedPastCut (exitingCorrectionRegion i hExit) hw]
        have hOne : 1 ≤ forwardFuel (correctionLinearRegion i).hi s := by
          unfold forwardFuel
          split <;> omega
        split <;> omega
    | @last t e he =>
      rw [countedCorrectionCons hHi (some _)]
      have hOne : 1 ≤ forwardFuel (correctionLinearRegion i).hi t := by
        unfold forwardFuel
        split <;> omega
      simp only [countedUntil, List.takeWhile_nil, List.filterMap_nil, List.countP_nil,
        Nat.zero_add]
      split <;> omega
  unfold forwardFuel at hCount
  split at hCount <;> omega


/-- Split a correction interval while retaining its counter and sub-step bound. -/
theorem cutCorrectionLinear (i : Fin 10) {l : Launch} {g cutoff : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hp : s.pc = (correctionLinearRegion i).lo) (hSub : s.sub ≤ 3)
    (hCut : (correctionLinearRegion i).hi ≤ cutoff)
    (hw : Walk kernel Assumptions.all l g s events visits) :
    let site := correctionLinearRegion i
    let budget := 5 * (site.hi - site.lo) + 4
    countedUntil cutoff visits ≤ budget ∨
      ∃ u rest tail, u.pc ∈ site.exits ∧ u.fault = none ∧ u.sub ≤ 3 ∧
        u.regs (correctionLinearProtected i) = s.regs (correctionLinearProtected i) ∧
        Walk kernel Assumptions.all l g u rest tail ∧
        countedUntil cutoff visits ≤ budget + countedUntil cutoff tail := by
  dsimp only
  have hHi : s.pc < (correctionLinearRegion i).hi := by
    rw [hp]
    fin_cases i <;> decide
  have hB := correctionLinearBound i hw hp.ge hHi hSub
  rw [hp] at hB
  rcases cutWalkInterval (P := fun u => u.sub ≤ 3 ∧
      u.regs (correctionLinearProtected i) = s.regs (correctionLinearProtected i))
      hw hp.ge hHi ⟨hSub, rfl⟩ hCut (fun hl hh he hu => by
        obtain ⟨hP, hR, hKeep⟩ := correctionLinearStep i hl hh hu.1 he
        exact ⟨hR, hP.sub, hKeep.trans hu.2⟩) with h | ⟨u, rest, tail, hpc, hf, h, hw, hb⟩
  · exact .inl (h.trans hB)
  · exact .inr ⟨u, rest, tail, hpc, hf, h.1, h.2, hw, hb.trans (Nat.add_le_add_right hB _)⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
