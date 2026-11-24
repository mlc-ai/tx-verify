-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueLinearEvents
public import Kernels.TmlFa4Fwd.Proof.MmaLoopRank
public import Kernels.TmlFa4Fwd.Proof.MmaScanBody
public import Kernels.TmlFa4Fwd.Proof.MmaPoll
public import Lemmas.Flow.WaitLoopPcs

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue

noncomputable section

/-- Straight MMA and epilogue regions between the real scheduler and trip loops. -/
def linearRegionBounds : Fin 8 → Nat × Nat
  | 0 => (1904, 1988)
  | 1 => (2042, 2291)
  | 2 => (2534, 2696)
  | 3 => (2750, 2768)
  | 4 => (2768, 2824)
  | 5 => (2878, 3032)
  | 6 => (3086, 3101)
  | 7 => (7742, 7745)

def linearRoleOp (op : Op) : Bool := linearEventOp op || epilogueExtraOp op

private theorem linearRoleProgress {l : Launch} {g : Nat} {s u : TState} {e : Event} {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) (hOp : linearRoleOp ins.op = true)
    (hSub : s.sub ≤ 1) (hAcc : s.acc = [])
    (h : EStep kernel Assumptions.all l g s e (some u)) :
    u.sub ≤ 1 ∧ u.acc = [] ∧
      (u.pc = s.pc + 1 ∨ u.pc = s.pc ∧ s.sub = 0 ∧ u.sub = 1 ∧ allocationOp ins.op ∨
        u.pc = s.pc ∧ u.fault.isSome) := by
  simp only [linearRoleOp, Bool.or_eq_true] at hOp
  rcases hOp with hM | hE
  · exact linearEventProgress hc hM hSub hAcc h
  · obtain ⟨hPc, hs, ha, _⟩ := epilogueExtraProgress hc hE h
    exact ⟨hs ▸ hSub, ha.trans hAcc, .inl hPc⟩

private def linearPoll (pc : Nat) : Option (Nat × Nat) :=
  match pc with
  | 2142 => some (2141, 9634)
  | 2146 => some (2145, 9635)
  | 2211 => some (2210, 9652)
  | 2546 => some (2545, 9725)
  | 2549 => some (2548, 9726)
  | 2587 => some (2586, 9736)
  | 2596 => some (2595, 9737)
  | 2627 => some (2626, 9747)
  | 2959 => some (2958, 9748)
  | 2973 => some (2972, 9749)
  | _ => none

private def linearRetry (pc : Nat) : Option Nat :=
  match pc with
  | 2143 => some 2141
  | 2147 => some 2145
  | 2212 => some 2210
  | 2547 => some 2545
  | 2550 => some 2548
  | 2588 => some 2586
  | 2597 => some 2595
  | 2628 => some 2626
  | 2960 => some 2958
  | 2974 => some 2972
  | _ => none

private def linearFloor (pc : Nat) : Nat :=
  ((linearPoll pc).map Prod.fst).getD ((linearRetry pc).getD pc)

private def pollSuccess (s : TState) (reg : Nat) : Bool :=
  match s.regs reg with
  | some (.pred ok) => ok
  | _ => false

private def linearScore (s : TState) : Nat :=
  let pending := ((linearPoll s.pc).map (fun site => pollSuccess s site.2)).getD false
  2 * linearFloor s.pc + pending.toNat + if s.pc = 1909 then s.sub else 0

private theorem scoreFloor (s : TState) : 2 * linearFloor s.pc ≤ linearScore s := by
  dsimp only [linearScore]
  omega

private theorem scorePc (s : TState) (hSub : s.sub ≤ 1) : linearScore s ≤ 2 * s.pc + 1 := by
  have hSubPart : (if s.pc = 1909 then s.sub else 0) ≤ 1 := by split <;> omega
  unfold linearScore linearFloor linearPoll linearRetry
  split <;> simp_all [Bool.toNat] <;> (try split) <;>
    (try simp only [Option.getD]) <;> omega

private def linearCodeOk (lo : Nat) (ins : Instr) (pc : Nat) : Bool :=
  (lo ≤ linearFloor pc) &&
  (if allocationOp ins.op then pc == 1909 else true) &&
  (match ins.op with
    | .mbarWait dest .. => ins.guard.isNone && linearPoll (pc + 1) == some (pc, dest) &&
        linearPoll pc == none && linearRetry pc == none
    | .brx .. => false
    | _ => if (linearPoll pc).isSome || (linearRetry pc).isSome then ins.op.isLocal
      else if ins.op.isLocal then pc ≤ linearFloor (pc + 1) && pc ≤ linearFloor (nextPc ins.op pc)
      else linearRoleOp ins.op && pc < linearFloor (pc + 1))

private theorem linearCode (region : Fin 8) {pc : Nat} {ins : Instr}
    (hlo : (linearRegionBounds region).1 ≤ pc) (hhi : pc < (linearRegionBounds region).2)
    (hc : kernel.code[pc]? = some ins) :
    linearCodeOk (linearRegionBounds region).1 ins pc = true := by
  let lo := (linearRegionBounds region).1
  let hi := (linearRegionBounds region).2
  have hall : (((kernel.code.drop lo).take (hi - lo)).zipIdx lo).all
      (fun pair => linearCodeOk lo pair.1 pair.2) = true := by
    fin_cases region <;> set_option maxRecDepth 100000 in kernel_rfl
  have hs : (ins, pc) ∈ ((kernel.code.drop lo).take (hi - lo)).zipIdx lo := by
    apply List.mem_of_getElem? (i := pc - lo)
    have hL : lo ≤ pc := hlo
    have hH : pc < hi := hhi
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hL, hc]
    rfl
  exact List.all_eq_true.mp hall (ins, pc) hs

private theorem linearCodeFacts (region : Fin 8) {pc : Nat} {ins : Instr}
    (hlo : (linearRegionBounds region).1 ≤ pc) (hhi : pc < (linearRegionBounds region).2)
    (hc : kernel.code[pc]? = some ins) :
    (linearRegionBounds region).1 ≤ linearFloor pc ∧
      (allocationOp ins.op = true → pc = 1909) ∧
    (match ins.op with
      | .mbarWait dest .. => ins.guard = none ∧ linearPoll (pc + 1) = some (pc, dest) ∧
          linearPoll pc = none ∧ linearRetry pc = none
      | .brx .. => False
      | _ => if (linearPoll pc).isSome || (linearRetry pc).isSome then ins.op.isLocal = true
        else if ins.op.isLocal then pc ≤ linearFloor (pc + 1) ∧ pc ≤ linearFloor (nextPc ins.op pc)
        else linearRoleOp ins.op = true ∧ pc < linearFloor (pc + 1)) := by
  have hall := linearCode region hlo hhi hc
  simp only [linearCodeOk, Bool.and_eq_true, decide_eq_true_eq] at hall
  refine ⟨hall.1.1, ?_, ?_⟩
  · intro hA
    simpa [hA] using hall.1.2
  · have hb := hall.2
    cases hop : ins.op <;> simp only [hop] at hb ⊢
    case mbarWait => simpa [and_assoc] using hb
    case brx => cases hb
    all_goals
      split <;> rename_i hBranch
      · simpa [hBranch] using hb
      · split <;> rename_i hLocal <;> simpa [hBranch, hLocal] using hb

set_option maxRecDepth 100000 in
private theorem linearPollCode {pc base dst : Nat} (hp : linearPoll pc = some (base, dst)) :
    pc ≠ 1909 ∧ (∃ uni, kernel.code[pc]? = some ⟨some (dst, false), .bra (base + 3) uni⟩) ∧
      linearFloor (pc + 1) = base ∧ linearFloor (base + 3) = base + 3 := by
  unfold linearPoll at hp
  split at hp
  all_goals simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]
  all_goals obtain ⟨rfl, rfl⟩ := hp
  · exact ⟨by decide, ⟨_, Flow.code_2142⟩, rfl, rfl⟩
  · exact ⟨by decide, ⟨_, Flow.code_2146⟩, rfl, rfl⟩
  · exact ⟨by decide, ⟨_, Flow.code_2211⟩, rfl, rfl⟩
  · exact ⟨by decide, ⟨_, Flow.code_2546⟩, rfl, rfl⟩
  · exact ⟨by decide, ⟨_, Flow.code_2549⟩, rfl, rfl⟩
  · exact ⟨by decide, ⟨_, Flow.code_2587⟩, rfl, rfl⟩
  · exact ⟨by decide, ⟨_, Flow.code_2596⟩, rfl, rfl⟩
  · exact ⟨by decide, ⟨_, Flow.code_2627⟩, rfl, rfl⟩
  · exact ⟨by decide, ⟨_, Flow.code_2959⟩, rfl, rfl⟩
  · exact ⟨by decide, ⟨_, Flow.code_2973⟩, rfl, rfl⟩

set_option maxRecDepth 100000 in
private theorem linearRetryCode {pc base : Nat} (hp : linearRetry pc = some base) :
    pc ≠ 1909 ∧ (∃ uni, kernel.code[pc]? = some ⟨none, .bra base uni⟩) ∧
      linearFloor base = base ∧ base ≤ linearFloor (pc + 1) := by
  unfold linearRetry at hp
  split at hp
  all_goals simp_all only [Option.some.injEq, reduceCtorEq]
  all_goals subst base
  · exact ⟨by decide, ⟨_, Flow.code_2143⟩, rfl, by decide⟩
  · exact ⟨by decide, ⟨_, Flow.code_2147⟩, rfl, by decide⟩
  · exact ⟨by decide, ⟨_, Flow.code_2212⟩, rfl, by decide⟩
  · exact ⟨by decide, ⟨_, Flow.code_2547⟩, rfl, by decide⟩
  · exact ⟨by decide, ⟨_, Flow.code_2550⟩, rfl, by decide⟩
  · exact ⟨by decide, ⟨_, Flow.code_2588⟩, rfl, by decide⟩
  · exact ⟨by decide, ⟨_, Flow.code_2597⟩, rfl, by decide⟩
  · exact ⟨by decide, ⟨_, Flow.code_2628⟩, rfl, by decide⟩
  · exact ⟨by decide, ⟨_, Flow.code_2960⟩, rfl, by decide⟩
  · exact ⟨by decide, ⟨_, Flow.code_2974⟩, rfl, by decide⟩

private theorem noAllocationTau {l : Launch} {g : Nat} {s u : TState} (hp : s.pc = 1909)
    (ht : Tau kernel [] l g s u) : False := by
  have hc := Flow.code_1909
  rw [← hp] at hc
  exact tau_core_not_event hc rfl ht

private theorem allocationOnly {pc : Nat} {ins : Instr} (hp : pc = 1909)
    (hc : kernel.code[pc]? = some ins) : allocationOp ins.op = true := by
  rw [hp, Flow.code_1909] at hc
  obtain rfl := Option.some.inj hc
  rfl


private theorem scoreAtOrdinary {s : TState} (hPoll : linearPoll s.pc = none)
    (hRetry : linearRetry s.pc = none) :
    linearScore s = 2 * s.pc + (if s.pc = 1909 then s.sub else 0) := by
  simp [linearScore, linearFloor, hPoll, hRetry]

private theorem takenLinearBranch {l : Launch} {g dest target : Nat} {uni : Bool} {s u : TState}
    (hc : kernel.code[s.pc]? = some ⟨some (dest, false), .bra target uni⟩)
    (hTrue : pollSuccess s dest = true) (ht : Tau kernel [] l g s u) :
    u.pc = target := by
  have hReg : s.regs dest = some (.pred true) := by
    unfold pollSuccess at hTrue
    split at hTrue
    · simp_all
    · cases hTrue
  have hGuard : guardHolds s (some (dest, false)) = .ok true := by
    simp [guardHolds, readReg, hReg, bind, Except.bind, pure, Except.pure]
  have hFault : s.fault = none := by
    cases hf : s.fault
    · rfl
    · simp [Tau, out, hf] at ht
  unfold Tau at ht
  simp [out, hFault, hc, hGuard, execLocalA, execLocalRule, execLocal,
    Op.isLocal, Op.rule, execBranch, pure, Except.pure] at ht
  obtain rfl := ht.symm
  rfl

private theorem linearTauRank (region : Fin 8) {l : Launch} {g : Nat} {s u : TState}
    (hlo : (linearRegionBounds region).1 ≤ s.pc) (hhi : s.pc < (linearRegionBounds region).2)
    (hSub : s.sub ≤ 1) (hAcc : s.acc = []) (ht : Tau kernel Assumptions.all l g s u) :
    u.sub ≤ 1 ∧ u.acc = [] ∧ (linearRegionBounds region).1 ≤ u.pc ∧
      linearScore s ≤ linearScore u := by
  have hModel : out kernel Assumptions.all l g s = out kernel [] l g s := by
    fin_cases region <;> simp only [linearRegionBounds] at hlo hhi
    · exact out_eq_core (by omega) (by omega)
    · exact out_eq_core (by omega) (by omega)
    · exact out_eq_core (by omega) (by omega)
    · exact out_eq_core (by omega) hhi
    · exact epilogue_out_all_eq_nil (.inl ⟨hlo, by omega⟩)
    · exact epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩)
    · exact epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩)
    · exact epilogue_out_all_eq_nil (.inr (.inl ⟨hlo, by omega⟩))
  have ht' : Tau kernel [] l g s u := by
    unfold Tau at ht ⊢
    rwa [← hModel]
  obtain ⟨ins, hc⟩ := tau_core_has_code ht'
  have hC := linearCodeFacts region hlo hhi hc
  have hStruct : u.sub ≤ 1 ∧ u.acc = [] := by
    rcases tau_core_frame hc ht' with rfl | h
    · exact ⟨Nat.zero_le 1, rfl⟩
    · exact ⟨h.sub ▸ hSub, h.acc.trans hAcc⟩
  have hFloor := scoreFloor u
  have hRank : linearScore s ≤ linearScore u := by
    cases hp : linearPoll s.pc with
    | some pair =>
      obtain ⟨base, dest⟩ := pair
      obtain ⟨hNotAlloc, ⟨uni, hCode⟩, hFall, hTarget⟩ := linearPollCode hp
      have hStart : linearScore s = 2 * base + (pollSuccess s dest).toNat := by
        simp [linearScore, linearFloor, hp, hNotAlloc]
      rw [hStart]
      cases hB : pollSuccess s dest
      · have hLanding : u.pc = s.pc + 1 ∨ u.pc = base + 3 := by
          rcases tau_core_frame hCode ht' with rfl | h
          · exact .inl rfl
          · exact .inr (h.pc.resolve_right id)
        rcases hLanding with h | h <;> rw [h] at hFloor <;>
          simp only [hFall, hTarget] at hFloor <;> simp only [Bool.toNat_false, Nat.add_zero] <;>
          omega
      · have h := takenLinearBranch hCode hB ht'
        rw [h, hTarget] at hFloor
        simp only [Bool.toNat_true]
        omega
    | none =>
      cases hr : linearRetry s.pc with
      | some base =>
        obtain ⟨hNotAlloc, ⟨uni, hCode⟩, hTarget, hFall⟩ := linearRetryCode hr
        have hStart : linearScore s = 2 * base := by
          simp [linearScore, linearFloor, hp, hr, hNotAlloc]
        rw [hStart]
        rcases tau_core_frame hCode ht' with rfl | h
        · change 2 * linearFloor (s.pc + 1) ≤ _ at hFloor
          omega
        · have hPc : u.pc = base := h.pc.resolve_right id
          rw [hPc, hTarget] at hFloor
          exact hFloor
      | none =>
        have hNotAlloc : s.pc ≠ 1909 := fun h => noAllocationTau h ht'
        simp only [scoreAtOrdinary hp hr, ite_eq_right hNotAlloc, Nat.add_zero]
        have hCode := hC.2.2
        cases hop : ins.op with
        | mbarWait dst base off par acq scope =>
          have hUn : ins.guard = none := by
            simp only [hop] at hCode
            exact hCode.1
          obtain ⟨guard, op⟩ := ins
          simp only at hop hUn
          subst guard op
          exact (tau_core_not_event hc rfl ht').elim
        | brx => simp only [hop] at hCode
        | _ =>
          have hWalkable : s.pc ≤ linearFloor (s.pc + 1) ∧
              s.pc ≤ linearFloor (nextPc ins.op s.pc) := by
            cases hLoc : ins.op.isLocal <;> rw [hop] at hLoc ⊢
            · simp [hop, hp, hr, hLoc] at hCode
              refine ⟨hCode.2.le, ?_⟩
              first | exact hCode.2.le | exact (Bool.noConfusion hLoc)
            · simpa [hop, hp, hr, hLoc] using hCode
          rcases tau_core_frame hc ht' with rfl | h
          · change 2 * linearFloor (s.pc + 1) ≤ _ at hFloor
            have := hWalkable.1
            omega
          · rcases h.pc with hPc | hBrx
            · rw [hPc] at hFloor
              have := hWalkable.2
              omega
            · simp only [hop, BrxTarget] at hBrx
  have hTwo : 2 * (linearRegionBounds region).1 ≤ linearScore s := by
    have hMin := hC.1
    have hBound := scoreFloor s
    omega
  have hUpper := scorePc u hStruct.1
  exact ⟨hStruct.1, hStruct.2, by omega, hRank⟩


private theorem linearOrdinaryOp {region : Fin 8} {pc : Nat} {ins : Instr}
    (hlo : (linearRegionBounds region).1 ≤ pc) (hhi : pc < (linearRegionBounds region).2)
    (hc : kernel.code[pc]? = some ins) (hn : pollOp ins.op = false)
    (hLocal : ins.op.isLocal = false) :
    linearPoll pc = none ∧ linearRetry pc = none ∧
      linearRoleOp ins.op = true ∧ pc < linearFloor (pc + 1) := by
  have hC := (linearCodeFacts region hlo hhi hc).2.2
  cases hp : linearPoll pc <;> cases hr : linearRetry pc
  all_goals
    cases ho : ins.op <;> simp only [ho] at hC hLocal hn
    all_goals simp_all [pollOp]

private theorem linearPollOp {op : Op} (h : pollOp op = true) :
    ∃ dest base off par acq scope, op = .mbarWait dest base off par acq scope := by
  cases op <;> simp_all [pollOp]

private theorem linearEventRank (region : Fin 8) {l : Launch} {g : Nat} {s u : TState}
    {e : Event} (hlo : (linearRegionBounds region).1 ≤ s.pc)
    (hhi : s.pc < (linearRegionBounds region).2)
    (hSub : s.sub ≤ 1) (hAcc : s.acc = [])
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.sub ≤ 1 ∧ u.acc = [] ∧
      ((linearRegionBounds region).1 ≤ u.pc ∧
        linearScore s + (if e.counts then 1 else 0) ≤ linearScore u
        ∨ u.fault.isSome) := by
  obtain ⟨ins, hc, hLocal, hf⟩ := estep_event_source he
  have hC := linearCodeFacts region hlo hhi hc
  cases hp : pollOp ins.op
  · obtain ⟨hP, hR, hOp, hLand⟩ := linearOrdinaryOp hlo hhi hc hp hLocal
    obtain ⟨hUSub, hUAcc, hAdvance | hAlloc | hFault⟩ :=
      linearRoleProgress hc hOp hSub hAcc he
    · have hLow := scoreFloor u
      rw [hAdvance] at hLow
      have hSubCost : (if s.pc = 1909 then s.sub else 0) ≤ 1 := by split <;> omega
      refine ⟨hUSub, hUAcc, .inl ⟨by omega, ?_⟩⟩
      rw [scoreAtOrdinary hP hR]
      have hCharge : (if e.counts then 1 else 0) ≤ 1 := by split <;> decide
      omega
    · obtain ⟨hPc, hZero, hOne, hFlag⟩ := hAlloc
      have hAllocPc := hC.2.1 hFlag
      have hAllocPc' := hPc.trans hAllocPc
      have huP : linearPoll u.pc = none := by rw [hPc]; exact hP
      have huR : linearRetry u.pc = none := by rw [hPc]; exact hR
      refine ⟨hUSub, hUAcc, .inl ⟨by omega, ?_⟩⟩
      rw [scoreAtOrdinary hP hR, scoreAtOrdinary huP huR, ite_eq_left hAllocPc,
        ite_eq_left hAllocPc', hZero, hOne, hPc]
      split <;> omega
    · exact ⟨hUSub, hUAcc, .inr hFault.2⟩
  · obtain ⟨dst, base, off, par, acq, scope, hop⟩ := linearPollOp hp
    have hNotAlloc : s.pc ≠ 1909 := by
      intro hP
      have hp' := allocationOnly hP hc
      rw [hop] at hp'
      cases hp'
    have hShape : ins.guard = none ∧ linearPoll (s.pc + 1) = some (s.pc, dst) ∧
        linearPoll s.pc = none ∧ linearRetry s.pc = none := by
      simpa only [hop] using hC.2.2
    rw [hop] at hf
    obtain ⟨loc, phase, ok, effective, rfl, rfl⟩ := fires_wait hf
    refine ⟨hSub, hAcc, .inl ⟨by change (linearRegionBounds region).1 ≤ s.pc + 1; omega, ?_⟩⟩
    rw [scoreAtOrdinary hShape.2.2.1 hShape.2.2.2, ite_eq_right hNotAlloc, Nat.add_zero]
    cases ok <;>
      simp [linearScore, linearFloor, next, hShape.2.1, pollSuccess, setReg, Event.counts]

private theorem linearExitCount {l : Launch} {g stop : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs) (hPc : stop ≤ s.pc) :
    countedUntil stop vs = 0 := by
  cases hw <;> simp [countedUntil, visit_pc, Nat.not_lt.mpr hPc]

private theorem linearCount (region : Fin 8) {l : Launch} {g : Nat}
    {s : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hlo : (linearRegionBounds region).1 ≤ s.pc) (hSub : s.sub ≤ 1) (hAcc : s.acc = []) :
    countedUntil (linearRegionBounds region).2 vs ≤
      2 * (linearRegionBounds region).2 + 2 - linearScore s := by
  induction hw with
  | stop => simp [countedUntil]
  | @tau s u es vs ht hw ih =>
    by_cases hHi : s.pc < (linearRegionBounds region).2
    · obtain ⟨hUSub, hUAcc, hLo, hR⟩ := linearTauRank region hlo hHi hSub hAcc ht
      have hCount := ih hLo hUSub hUAcc
      have hMon := Nat.sub_le_sub_left hR (2 * (linearRegionBounds region).2 + 2)
      simpa [countedUntil, hHi, visit_pc, visit_ev, List.filterMap_cons] using hCount.trans hMon
    · simp [countedUntil, hHi, visit_pc]
  | @ev s u e es vs he hw ih =>
    by_cases hHi : s.pc < (linearRegionBounds region).2
    · have hCharge : (if e.counts then 1 else 0) ≤ 1 := by split <;> decide
      obtain ⟨hUSub, hUAcc, hProgress | hFault⟩ := linearEventRank region hlo hHi hSub hAcc he
      · have hCount := ih hProgress.1 hUSub hUAcc
        have hTest := decide_eq_true (show (visit kernel l g s (some e)).pc <
          (linearRegionBounds region).2 from hHi)
        rw [countedUntil, List.takeWhile_cons, ite_eq_left hTest]
        simp only [List.filterMap_cons, visit_ev, List.countP_cons]
        change countedUntil (linearRegionBounds region).2 vs + (if e.counts then 1 else 0) ≤ _
        by_cases hU : (linearRegionBounds region).2 ≤ u.pc
        · rw [linearExitCount hw hU]
          have hOld := scorePc s hSub
          omega
        · have hNew := scorePc u hUSub
          have hR := hProgress.2
          omega
      · have hCount : countedUntil (linearRegionBounds region).2 vs ≤ 1 :=
          countFaultedScan hFault hw
        have hTest := decide_eq_true (show (visit kernel l g s (some e)).pc <
          (linearRegionBounds region).2 from hHi)
        rw [countedUntil, List.takeWhile_cons, ite_eq_left hTest]
        simp only [List.filterMap_cons, visit_ev, List.countP_cons]
        change countedUntil (linearRegionBounds region).2 vs + (if e.counts then 1 else 0) ≤ _
        have hOld := scorePc s hSub
        omega
    · simp [countedUntil, hHi, visit_pc]
  | @last s e he =>
    by_cases hHi : s.pc < (linearRegionBounds region).2
    · have hPC := scorePc s hSub
      have hBound : 1 ≤ 2 * (linearRegionBounds region).2 + 2 - linearScore s := by omega
      simpa [countedUntil, hHi, visit_pc, visit_ev] using
        (List.countP_le_length (p := Event.counts) (l := [e])).trans hBound
    · simp [countedUntil, hHi, visit_pc]

/-- Every straight region contributes a linear number of counted events, including the allocation
store sub-step, the first and final waits, and a possible terminal fault. -/
theorem linearRolePrefixBound (region : Fin 8) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hPc : (linearRegionBounds region).1 ≤ s.pc) (hSub : s.sub ≤ 1) (hAcc : s.acc = []) :
    countedUntil (linearRegionBounds region).2 vs ≤
      2 * ((linearRegionBounds region).2 - (linearRegionBounds region).1) + 2 := by
  by_cases hhi : s.pc < (linearRegionBounds region).2
  · have hLen : s.pc < kernel.code.length := by
      have hg : kernel.code.length = 9206 := by
        set_option maxRecDepth 100000 in kernel_rfl
      rw [hg]
      fin_cases region <;> simp only [linearRegionBounds] at hhi <;> omega
    have hc := List.getElem?_eq_getElem (l := kernel.code) hLen
    have hC := (linearCodeFacts region hPc hhi hc).1
    have hCount := linearCount region hw hPc hSub hAcc
    have hScore := scoreFloor s
    omega
  · rw [linearExitCount hw (Nat.le_of_not_lt hhi)]
    exact Nat.zero_le _

/-- The four original MMA regions, in PTX order. -/
def linearBounds (region : Fin 4) : Nat × Nat :=
  linearRegionBounds ⟨region.val, by omega⟩

theorem mmaLinearPrefixBound (region : Fin 4) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hPc : (linearBounds region).1 ≤ s.pc) (hSub : s.sub ≤ 1) (hAcc : s.acc = []) :
    countedUntil (linearBounds region).2 vs ≤
      2 * ((linearBounds region).2 - (linearBounds region).1) + 2 :=
  linearRolePrefixBound ⟨region.val, by omega⟩ hw hPc hSub hAcc

end
end PTX.Kernels.TmlFa4Fwd.Mma
