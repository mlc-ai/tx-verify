-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderEventProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

/-- The loader's polling backedges retry a single CTA acquire. Other backward
branches advance a scheduler, page-lookup, or ring counter. -/
def loaderPollSites : List (Nat × Nat) :=
  [(517, 9606), (679, 9607), (704, 9608), (730, 9609), (756, 9610), (782, 9611),
   (960, 9612), (1146, 9613), (1175, 9614), (1206, 9615), (1361, 9616), (1430, 9617),
   (1611, 9618), (1866, 9619), (1877, 9620), (1888, 9621), (1893, 9622)]

def loaderCycleSite (pc : Nat) : Bool :=
  [287, 401, 514, 537, 802, 956, 980, 1226, 1352, 1426, 1450, 1631, 1743, 1847].contains pc

private def loaderCheck (pc : Nat) : Option (Nat × Nat) :=
  loaderPollSites.find? (fun x => x.1 + 1 == pc)

private def loaderRetry (pc : Nat) : Option (Nat × Nat) :=
  loaderPollSites.find? (fun x => x.1 + 2 == pc)

private def loaderFloor (pc : Nat) : Nat :=
  ((loaderCheck pc).map Prod.fst).getD (((loaderRetry pc).map Prod.fst).getD pc)

private def acquired (s : TState) (r : Nat) : Bool :=
  match s.regs r with
  | some (.pred ok) => ok
  | _ => false

private def loaderScore (s : TState) : Nat :=
  3 * loaderFloor s.pc + (((loaderCheck s.pc).map (acquired s ∘ Prod.snd)).getD false).toNat +
    s.sub

private theorem checkPc {pc base r : Nat} (h : loaderCheck pc = some (base, r)) :
    pc = base + 1 := by
  have hh := List.find?_some h
  simp only [beq_iff_eq] at hh
  exact hh.symm

private theorem retryPc {pc base r : Nat} (h : loaderRetry pc = some (base, r)) :
    pc = base + 2 := by
  have hh := List.find?_some h
  simp only [beq_iff_eq] at hh
  exact hh.symm

private theorem floorLe (pc : Nat) : loaderFloor pc ≤ pc := by
  cases hc : loaderCheck pc with
  | some a =>
    obtain ⟨base, r⟩ := a
    have ht := checkPc hc
    simp only [loaderFloor, hc, Option.map_some, Option.getD_some]
    omega
  | none =>
    cases hr : loaderRetry pc with
    | none => simp [loaderFloor, hc, hr]
    | some a =>
      obtain ⟨base, r⟩ := a
      have ht := retryPc hr
      simp only [loaderFloor, hc, hr, Option.map_none, Option.map_some, Option.getD_none,
        Option.getD_some]
      omega

private theorem scoreFloor (s : TState) : 3 * loaderFloor s.pc ≤ loaderScore s := by
  unfold loaderScore
  omega

private theorem scorePc (s : TState) (hs : s.sub ≤ 1) : loaderScore s ≤ 3 * s.pc + 2 := by
  have hFloor := floorLe s.pc
  have hBool : (((loaderCheck s.pc).map (acquired s ∘ Prod.snd)).getD false).toNat ≤ 1 := by
    cases ((loaderCheck s.pc).map (acquired s ∘ Prod.snd)).getD false <;> decide
  unfold loaderScore
  omega

private theorem scoreOrdinary {s : TState} (hc : loaderCheck s.pc = none)
    (hr : loaderRetry s.pc = none) : loaderScore s = 3 * s.pc + s.sub := by
  simp [loaderScore, loaderFloor, hc, hr]

private def loaderRankInstruction (ins : Instr) (pc : Nat) : Bool :=
  match loaderCheck pc, loaderRetry pc with
  | some (base, reg), _ =>
    ins.guard == some (reg, false) &&
      (match ins.op with | .bra target _ => target == base + 3 | _ => false) &&
      loaderFloor (pc + 1) == base && base < loaderFloor (base + 3)
  | none, some (base, _) =>
    ins.guard.isNone && (match ins.op with | .bra target _ => target == base | _ => false) &&
      loaderFloor base == base
  | none, none =>
    match ins.op with
    | .mbarWait dst .. => ins.guard.isNone && loaderCheck (pc + 1) == some (pc, dst)
    | .brx .. => false
    | _ => pc < loaderFloor (pc + 1) &&
        (loaderCycleSite pc || pc ≤ loaderFloor (nextPc ins.op pc))

private theorem loaderRankCode :
    (((kernel.code.drop 174).take (1906 - 174)).zipIdx 174).all
      (fun (i, pc) => loaderRankInstruction i pc) = true := by
  set_option maxRecDepth 100000 in decide +kernel

private theorem rankInstruction {s : TState} {ins : Instr}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906) (hc : kernel.code[s.pc]? = some ins) :
    loaderRankInstruction ins s.pc = true := by
  have hm : (ins, s.pc) ∈ ((kernel.code.drop 174).take (1906 - 174)).zipIdx 174 := by
    apply List.mem_of_getElem? (i := s.pc - 174)
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hLo, hc]
    rfl
  exact List.all_eq_true.mp loaderRankCode _ hm

private theorem branchOp {op : Op} {dest : Nat}
    (h : (match op with | .bra target _ => target == dest | _ => false) = true) :
    ∃ uni, op = .bra dest uni := by
  cases op <;> simp only [Bool.false_eq_true, beq_iff_eq] at h
  case bra target uni => exact ⟨uni, by rw [h]⟩

private theorem ordinaryCode {ins : Instr} {pc : Nat}
    (hp : loaderCheck pc = none) (hr : loaderRetry pc = none)
    (h : loaderRankInstruction ins pc = true) :
    (∃ dst base off par acq scope, ins.op = .mbarWait dst base off par acq scope ∧
      ins.guard = none ∧ loaderCheck (pc + 1) = some (pc, dst)) ∨
    (∀ p, ¬ BrxTarget ins.op p) ∧ pc < loaderFloor (pc + 1) ∧
      (loaderCycleSite pc = true ∨ pc ≤ loaderFloor (nextPc ins.op pc)) := by
  have h' : (match ins.op with
    | .mbarWait dst .. => ins.guard.isNone && loaderCheck (pc + 1) == some (pc, dst)
    | .brx .. => false
    | _ => pc < loaderFloor (pc + 1) &&
      (loaderCycleSite pc || pc ≤ loaderFloor (nextPc ins.op pc))) = true := by
    simpa only [loaderRankInstruction, hp, hr] using h
  generalize ho : ins.op = op at h' ⊢
  cases op <;> simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq,
    Bool.or_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h'
  case mbarWait dst base off par acq scope =>
    exact .inl ⟨dst, base, off, par, acq, scope, rfl, h'.1, h'.2⟩
  all_goals exact .inr ⟨by simp [BrxTarget], h'.1, h'.2⟩

private theorem takenBranch {l : Launch} {g target : Nat} {uni : Bool} {s u : TState}
    {guard : Option (Nat × Bool)}
    (hc : kernel.code[s.pc]? = some ⟨guard, .bra target uni⟩)
    (hGuard : guardHolds s guard = .ok true) (ht : Tau kernel [] l g s u) :
    u.pc = target := by
  have hFault : s.fault = none := by
    cases hf : s.fault
    · rfl
    · simp [Tau, out, hf] at ht
  unfold Tau at ht
  simp [out, hFault, hc, hGuard, execLocalA, execLocalRule, execLocal,
    Op.isLocal, Op.rule, execBranch, pure, Except.pure] at ht
  obtain rfl := ht.symm
  rfl

private theorem acquireGuard {s : TState} {dst : Nat} (hTrue : acquired s dst = true) :
    guardHolds s (some (dst, false)) = .ok true := by
  have hReg : s.regs dst = some (.pred true) := by
    unfold acquired at hTrue
    split at hTrue
    · simp_all
    · cases hTrue
  simp [guardHolds, readReg, hReg, bind, Except.bind, pure, Except.pure]

private theorem tauRank {l : Launch} {g : Nat} {s u : TState}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906) (hs : loaderSubShape s)
    (ht : Tau kernel Assumptions.all l g s u) :
    loaderSubShape u ∧ (loaderCycleSite s.pc = true ∨ loaderScore s ≤ loaderScore u) := by
  have ht' : Tau kernel [] l g s u := by
    unfold Tau at ht ⊢
    rwa [← loaderOutCore hLo hHi]
  obtain ⟨ins, hc⟩ := tau_core_has_code ht'
  have hCode := rankInstruction hLo hHi hc
  have hFrame := tau_core_frame hc ht'
  have hZero : s.sub = 0 := by
    by_contra hNot
    obtain ⟨_, he, _, hLocal⟩ := hs.2 (by have := hs.1; omega)
    exact tau_core_not_event he hLocal ht'
  have hU : u.sub = 0 := by
    rcases hFrame with rfl | h
    · rfl
    · exact h.sub.trans hZero
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  by_cases hCycle : loaderCycleSite s.pc = true
  · exact .inl hCycle
  right
  have hFloor := scoreFloor u
  cases hp : loaderCheck s.pc with
  | some site =>
    obtain ⟨base, dst⟩ := site
    have hC : ins.guard = some (dst, false) ∧
        (match ins.op with | .bra target _ => target == base + 3 | _ => false) = true ∧
        loaderFloor (s.pc + 1) = base ∧ base < loaderFloor (base + 3) := by
      simpa only [loaderRankInstruction, hp, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        and_assoc] using hCode
    obtain ⟨uni, hBra⟩ := branchOp hC.2.1
    have hBranchCode : kernel.code[s.pc]? = some ⟨some (dst, false), .bra (base + 3) uni⟩ := by
      rw [hc]
      cases ins
      simp_all
    have hS : loaderScore s = 3 * base + (acquired s dst).toNat := by
      simp [loaderScore, loaderFloor, hp, Function.comp_apply, hZero]
    rw [hS]
    cases hOk : acquired s dst
    · simp only [Bool.toNat_false, Nat.add_zero]
      rcases hFrame with rfl | h
      · change 3 * loaderFloor (s.pc + 1) ≤ _ at hFloor
        omega
      · have hPc := h.pc
        simp only [hBra, BrxTarget, nextPc, or_false] at hPc
        rw [hPc] at hFloor
        omega
    · rw [takenBranch hBranchCode (acquireGuard hOk) ht'] at hFloor
      simp only [Bool.toNat_true]
      omega
  | none =>
    cases hr : loaderRetry s.pc with
    | some site =>
      obtain ⟨base, dst⟩ := site
      have hC : ins.guard = none ∧
          (match ins.op with | .bra target _ => target == base | _ => false) = true ∧
          loaderFloor base = base := by
        simpa only [loaderRankInstruction, hp, hr, Bool.and_eq_true, beq_iff_eq,
          Option.isNone_iff_eq_none, and_assoc] using hCode
      rw [show loaderScore s = 3 * base by simp [loaderScore, loaderFloor, hp, hr, hZero]]
      obtain ⟨uni, hBra⟩ := branchOp hC.2.1
      have hBranchCode : kernel.code[s.pc]? = some ⟨none, .bra base uni⟩ := by
        rw [hc]
        cases ins
        simp_all
      rw [takenBranch hBranchCode rfl ht', hC.2.2] at hFloor
      exact hFloor
    | none =>
      rw [scoreOrdinary hp hr, hZero, Nat.add_zero]
      rcases ordinaryCode hp hr hCode with
        ⟨dst, base, off, par, acq, scope, hop, hGuard, _⟩ | ⟨hNoBrx, hFall, hBranch⟩
      ·
        have hEvent : kernel.code[s.pc]? =
            some ⟨none, .mbarWait dst base off par acq scope⟩ := by
          rw [hc]
          cases ins
          simp_all
        exact (tau_core_not_event hEvent rfl ht').elim
      · have hLand := hBranch.resolve_left hCycle
        rcases hFrame with rfl | h
        · change 3 * loaderFloor (s.pc + 1) ≤ _ at hFloor
          omega
        · rw [h.pc.resolve_right (hNoBrx _)] at hFloor
          omega

private theorem eventRank {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906) (hSub : loaderSubShape s)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    loaderSubShape u ∧
      (loaderScore s + (if e.counts then 1 else 0) ≤ loaderScore u ∨ u.fault.isSome) := by
  obtain ⟨hU, hNext | ⟨hPc, hGrow | hFault⟩⟩ := loaderEventProgress hLo hHi hSub he
  case inr.inr => exact ⟨hU, .inr hFault⟩
  all_goals (
    refine ⟨hU, .inl ?_⟩
    obtain ⟨ins, hc, hLocal, hf⟩ := estep_event_source he
    have hInst := rankInstruction hLo hHi hc
    have hOff : loaderCheck s.pc = none ∧ loaderRetry s.pc = none := by
      cases hh : loaderCheck s.pc with
      | some site =>
        obtain ⟨base, r⟩ := site
        have hB : (match ins.op with
          | .bra target _ => target == base + 3 | _ => false) = true := by
          simp only [loaderRankInstruction, hh, Bool.and_eq_true, and_assoc] at hInst
          exact hInst.2.1
        obtain ⟨uni, hBra⟩ := branchOp hB
        simp [hBra, Op.isLocal] at hLocal
      | none =>
        cases hr : loaderRetry s.pc with
        | none => exact ⟨rfl, rfl⟩
        | some site =>
          obtain ⟨base, r⟩ := site
          have hB : (match ins.op with
            | .bra target _ => target == base | _ => false) = true := by
            simp only [loaderRankInstruction, hh, hr, Bool.and_eq_true, and_assoc] at hInst
            exact hInst.2.1
          obtain ⟨uni, hBra⟩ := branchOp hB
          simp [hBra, Op.isLocal] at hLocal
    have hS := scoreOrdinary hOff.1 hOff.2
    have hCharge : (if e.counts then 1 else 0) ≤ 1 := by split <;> decide)
  · have hFloor := scoreFloor u
    have hSubOne := hSub.1
    rcases ordinaryCode hOff.1 hOff.2 hInst with
      ⟨dst, base, off, par, acq, scope, ho, _, hShape⟩ | ⟨_, hF, _⟩
    ·
      rw [ho] at hf
      obtain ⟨loc, phase, ok, effective, rfl, rfl⟩ := fires_wait hf
      rw [hS]
      cases ok <;>
        simp [loaderScore, loaderFloor, hShape, next, acquired, setReg, Event.counts,
          Function.comp_apply]
    ·
      rw [hNext] at hFloor
      omega
  · have huC : loaderCheck u.pc = none := by rw [hPc]; exact hOff.1
    have huR : loaderRetry u.pc = none := by rw [hPc]; exact hOff.2
    rw [hS, scoreOrdinary huC huR, hPc]
    omega

def loaderVisits (visits : List Visit) : List Visit :=
  visits.takeWhile (fun v => decide (174 ≤ v.pc ∧ v.pc < 1906))

def loaderEventCount (visits : List Visit) : Nat :=
  ((loaderVisits visits).filterMap Visit.ev).countP Event.counts

def loaderCycleCount (visits : List Visit) : Nat :=
  (loaderVisits visits).countP (fun v => loaderCycleSite v.pc)

theorem eventCountCons {l : Launch} {g : Nat} {s : TState}
    (hs : 174 ≤ s.pc ∧ s.pc < 1906) (e : Option Event) (vs : List Visit) :
    loaderEventCount (visit kernel l g s e :: vs) =
      loaderEventCount vs + ((e.map fun x => if x.counts then 1 else 0).getD 0) := by
  cases e <;> simp [loaderEventCount, loaderVisits, visit, hs, List.countP_cons]

private theorem cycleCountCons {l : Launch} {g : Nat} {s : TState}
    (hs : 174 ≤ s.pc ∧ s.pc < 1906) (e : Option Event) (vs : List Visit) :
    loaderCycleCount (visit kernel l g s e :: vs) =
      loaderCycleCount vs + (if loaderCycleSite s.pc then 1 else 0) := by
  cases hc : loaderCycleSite s.pc <;>
    simp [loaderCycleCount, loaderVisits, visit_pc, hs, hc]

variable {l : Launch} {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs)
include hw

private theorem pointOutside (hout : ¬ (174 ≤ s.pc ∧ s.pc < 1906)) :
    loaderEventCount vs = 0 := by
  cases hw <;> simp only [loaderEventCount, loaderVisits, List.takeWhile_nil,
    List.takeWhile_cons, visit_pc, List.filterMap_nil, List.countP_nil]
  all_goals
    split
    · rename_i hi
      exact (hout (of_decide_eq_true hi)).elim
    · rfl

omit hw in
private theorem singletonCount (v : Visit) : loaderEventCount [v] ≤ 1 := by
  unfold loaderEventCount loaderVisits
  by_cases h : 174 ≤ v.pc ∧ v.pc < 1906 <;>
    cases he : v.ev <;> simp [h, he, List.countP_cons]
  split <;> decide

private theorem pendingFaultCount (hf : s.fault.isSome) : loaderEventCount vs ≤ 1 := by
  cases h : s.fault
  · simp [h] at hf
  case some f =>
    cases hw with
    | stop => simp [loaderEventCount, loaderVisits]
    | tau ht _ => simp [Tau, out, h] at ht
    | ev hr _ =>
      obtain ⟨tmpl, ht, hf⟩ := hr
      simp only [out, h, Out.ev.injEq] at ht
      subst tmpl
      cases hf.2
    | last _ => exact singletonCount _

private theorem prefixScoreBound (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906) (hSub : loaderSubShape s) :
    loaderEventCount vs + loaderScore s ≤ 5720 * (loaderCycleCount vs + 1) + 2 := by
  induction hw with
  | stop s =>
    have hScore := scorePc s hSub.1
    simp [loaderEventCount, loaderCycleCount, loaderVisits]
    omega
  | @tau s u es vs ht hw ih =>
    obtain ⟨hu, hCut⟩ := tauRank hLo hHi hSub ht
    rw [eventCountCons ⟨hLo, hHi⟩, cycleCountCons ⟨hLo, hHi⟩]
    simp only [Option.map_none, Option.getD_none, Nat.add_zero]
    have hScore := scorePc s hSub.1
    by_cases hInside : 174 ≤ u.pc ∧ u.pc < 1906
    · have hTail := ih hInside.1 hInside.2 hu
      rcases hCut with hc | hr
      · rw [ite_eq_left hc]
        omega
      · split <;> omega
    · rw [pointOutside hw hInside]
      split <;> omega
  | @ev s u e es vs he hw ih =>
    obtain ⟨hu, hr | hf⟩ := eventRank hLo hHi hSub he
    all_goals
      rw [eventCountCons ⟨hLo, hHi⟩, cycleCountCons ⟨hLo, hHi⟩]
      simp only [Option.map_some, Option.getD_some]
      have hCharge : (if e.counts then 1 else 0) ≤ 1 := by split <;> decide
      have hScore := scorePc s hSub.1
    · by_cases hInside : 174 ≤ u.pc ∧ u.pc < 1906
      · have hTail := ih hInside.1 hInside.2 hu
        have hIncl : loaderEventCount vs + (if e.counts then 1 else 0) + loaderScore s ≤
            loaderEventCount vs + loaderScore u := by
          rw [Nat.add_assoc, Nat.add_comm (if e.counts then 1 else 0)]
          exact Nat.add_le_add_left hr _
        exact hIncl.trans (hTail.trans (by omega))
      · have hZero := pointOutside hw hInside
        split <;> omega
    · have hTail := pendingFaultCount hw hf
      split <;> omega
  | @last s e he =>
    have hCount := singletonCount (visit kernel l g s (some e))
    have hScore := scorePc s hSub.1
    omega

/-- The number of productive events in any actual loader prefix is bounded by the
number of visits to its computation backedges. Failed acquire retries cost no fuel.
The bound allows a final, potentially faulting, partial instruction. -/
theorem loaderPrefixFromCycles (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906) (hSub : s.sub = 0) :
    loaderEventCount vs ≤ 5720 * (loaderCycleCount vs + 1) + 2 := by
  have h := prefixScoreBound hw hLo hHi (by constructor <;> omega)
  omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
