-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseFootprint
public import Lemmas.Flow.TraceReach
public import Kernels.TmlFa4Fwd.Proof.CorrectionPrefixAccumulator
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Lemmas.Flow.Final

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Mma Softmax Epilogue

noncomputable section

private def lseAddressRegs : List Nat := [1635, 5967, 1613, 1634, 9605, 7501, 7500]

private def lseReadyCode (i : Instr) : Bool :=
  (i.op.isLocal || correctionReturningOp i.op) &&
    lseAddressRegs.all (fun r => !(writesRegs i.op).contains r &&
      !(scoreEventWrites i.op).contains r) &&
    (match i.op with
      | .mem a => a.kind != .load || a.regs.length ≤ 1
      | _ => true) &&
    (match i.op with
      | .bra dst _ => 7985 ≤ dst && dst < 9054
      | .brx .. => false
      | _ => true)

private theorem lseReadyAtCode {pc : Nat} {i : Instr} (hl : 7985 ≤ pc) (hh : pc < 9057)
    (hc : kernel.code[pc]? = some i) : lseReadyCode i = true := by
  have hall : ((kernel.code.drop 7985).take (9057 - 7985)).all lseReadyCode = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hall i
  apply List.mem_of_getElem? (i := pc - 7985)
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hl, hc]

private theorem lseLastVectorSub {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hs : 9053 ≤ s.pc) (ht : s.pc < 9057) (hNext : 9054 ≤ u.pc)
    (hSub : 9054 ≤ s.pc → s.sub = 0)
    (he : EStep kernel Assumptions.all l g s e (some u)) : u.sub = 0 := by
  obtain ⟨i, hc, _, hf⟩ := estep_event_source he
  have hp : s.pc = 9053 ∨ s.pc = 9054 ∨ s.pc = 9055 ∨ s.pc = 9056 := by omega
  rcases hp with hp | hp | hp | hp
  · rw [hp, Flow.code_9053] at hc
    obtain rfl := Option.some.inj hc
    rw [correctionStoreState (by decide) hf] at hNext ⊢
    simp only [afterStore, List.length_cons, List.length_nil, Nat.reduceAdd] at hNext ⊢
    by_cases h : s.sub + 1 < 4
    · rw [ite_eq_left h] at hNext
      change 9054 ≤ s.pc at hNext
      omega
    · rw [ite_eq_right h]
  · rw [hp, Flow.code_9054] at hc
    obtain rfl := Option.some.inj hc
    obtain rfl := fires_next (op := .fence _) trivial hf
    exact hSub (by omega)
  · rw [hp, Flow.code_9055] at hc
    obtain rfl := Option.some.inj hc
    obtain ⟨rfl, _⟩ := fires_arrive_state hf
    exact hSub (by omega)
  · rw [hp, Flow.code_9056] at hc
    obtain rfl := Option.some.inj hc
    obtain ⟨rfl, _⟩ := fires_arrive_state hf
    exact hSub (by omega)

private theorem advanceLseReady {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    {F : List (Nat × Value)} (hl : 7985 ≤ s.pc) (hh : s.pc < 9057)
    (hs : s.sub ≤ 3) (ha : s.acc = []) (hr : Holds s.regs F)
    (hF : ∀ rv ∈ F, rv.1 ∈ lseAddressRegs)
    (hTailSub : 9054 ≤ s.pc → s.sub = 0)
    (he : WStep kernel Assumptions.all l g s e u) :
    (7985 ≤ u.pc ∧ u.pc ≤ 9057) ∧ u.sub ≤ 3 ∧ u.acc = [] ∧
      Holds u.regs F ∧ (9054 ≤ u.pc → u.pc ≤ 9057 → u.sub = 0) := by
  rcases he with ⟨_, ht⟩ | ⟨e, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, _, hTau⟩ := correctionTauFrame hOff ht
    have hCode := lseReadyAtCode hl hh hc
    simp only [lseReadyCode, Bool.and_eq_true, Bool.or_eq_true, List.contains_eq_mem] at hCode
    rcases hTau with ⟨rfl, _⟩ | ⟨_, hIsLocal, hLocal⟩
    · exact ⟨⟨by change 7985 ≤ s.pc + 1; omega, by change s.pc + 1 ≤ 9057; omega⟩,
        Nat.zero_le _, rfl, hr, fun _ _ => rfl⟩
    have hKeep (r : Nat) (hR : r ∈ lseAddressRegs) : u.regs r = s.regs r := by
      apply hLocal.regs
      have h : r ∉ writesRegs i.op ∧ r ∉ scoreEventWrites i.op := by
        simpa using (List.all_eq_true.mp hCode.1.1.2 r hR)
      exact h.1
    have hReg := holdsSchedulerFrame hr hKeep hF
    have hp := hLocal.pc
    have hfPc : s.pc ≠ 9053 := by
      intro he
      rw [he, Flow.code_9053] at hc
      obtain rfl := Option.some.inj hc
      cases hIsLocal
    refine ⟨?_, hLocal.sub ▸ hs, hLocal.acc.trans ha, hReg, ?_⟩
    · cases hop : i.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hp
      case bra d uni =>
        have hDst : 7985 ≤ d ∧ d < 9054 := by simpa [hop] using hCode.2
        rw [hp]
        exact ⟨hDst.1, by omega⟩
      case brx => simp [hop] at hCode
      all_goals exact ⟨by omega, by omega⟩
    · intro hLo hHi
      cases hop : i.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hp
      case bra d uni =>
        have hDst : 7985 ≤ d ∧ d < 9054 := by simpa [hop] using hCode.2
        omega
      case brx => simp [hop] at hCode
      all_goals exact hLocal.sub.trans (hTailSub (by omega))
  · obtain ⟨i, hc, hNonlocal, _⟩ := estep_event_source he
    have hCode := lseReadyAtCode hl hh hc
    simp only [lseReadyCode, Bool.and_eq_true, hNonlocal, Bool.false_or] at hCode
    have hPlan := hCode.1.1.1
    have hScalar : match i.op with | .mem a => a.kind = .load → a.regs.length ≤ 1 | _ => True := by
      cases hop : i.op <;> simp_all
      case mem a => exact hCode.2.elim (fun h hn => (h hn).elim) (fun h _ => h)
    have hAcc := correctionEventAccumulator hc hPlan hScalar ha he
    have hKeep (r : Nat) (hR : r ∈ lseAddressRegs) :
        ScoreEventProgress s u ∧ u.regs r = s.regs r := by
      have hw := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hCode.1.1.2 r hR)
      exact correctionEventProgress hc hPlan hs (by simpa using hw.2) he
    have hP := (hKeep 1635 (by decide)).1
    have hW := holdsSchedulerFrame hr (fun r hm => (hKeep r hm).2) hF
    refine ⟨?_, hP.sub, hAcc, hW, ?_⟩
    · rcases hP.pc with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    · intro hLo _
      have hLo' : 9053 ≤ s.pc := by
        rcases hP.pc with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      exact lseLastVectorSub hLo' hh hLo hTailSub he

/-- The address registers survive the actual rescale, final statistics and normalization.
Partial vector stores do not count as reaching the LSE entry. -/
theorem cutLseReadyFromLateEvent {p : Params} {l : Launch} {g batch head tile : Nat}
    {s : TState} {target : Event} {es : List Event} {visits : List Visit}
    (hPc : 9057 < target.pc) (hAt : At s 7985 (lseFootprintEntryFacts p l g batch head tile))
    (hw : Walk kernel Assumptions.all l g s es visits) (hm : target ∈ es) :
    ∃ u rest tail, At u 9057 (lseFootprintEntryFacts p l g batch head tile) ∧
      Walk kernel Assumptions.all l g u rest tail ∧ target ∈ rest ∧
      ∃ consumed, es = consumed ++ rest ∧ TraceReach kernel Assumptions.all l g s consumed u := by
  let F := lseFootprintEntryFacts p l g batch head tile
  have hF : ∀ rv ∈ F, rv.1 ∈ lseAddressRegs := by
    intro rv h
    have hMem := List.mem_map_of_mem (f := Prod.fst) h
    simpa [F, lseFootprintEntryFacts, lseAddressRegs] using hMem
  have go {s : TState} {es : List Event} {vs : List Visit}
      (hWalk : Walk kernel Assumptions.all l g s es vs) (he : target ∈ es)
      (hLow : 7985 ≤ s.pc) (hHi : s.pc ≤ 9057) (hSub : s.sub ≤ 3)
      (hFlt : 9054 ≤ s.pc → s.sub = 0) (hAcc : s.acc = []) (hReg : Holds s.regs F) :
      ∃ u rest tail, At u 9057 F ∧
        Walk kernel Assumptions.all l g u rest tail ∧ target ∈ rest ∧
      ∃ consumed, es = consumed ++ rest ∧ TraceReach kernel Assumptions.all l g s consumed u := by
    have runStep {t u : TState} {e : Option Event}
        (hLow : 7985 ≤ t.pc) (hUp : t.pc < 9057) (hSub : t.sub ≤ 3)
        (hFlt : 9054 ≤ t.pc → t.sub = 0) (hAcc : t.acc = []) (hReg : Holds t.regs F)
        (hStep : WStep kernel Assumptions.all l g t e u) :=
      advanceLseReady hLow hUp hSub hAcc hReg hF hFlt hStep
    induction hWalk with
    | stop => simp at he
    | @tau t u es vs ht hW ih =>
      by_cases hEq : t.pc = 9057
      · have hf : t.fault = none := by
          cases hh : t.fault
          · rfl
          · simp [Tau, out, hh] at ht
        exact ⟨t, es, _, ⟨hEq, hFlt (by omega), hAcc, hf, hReg⟩, .tau ht hW, he, [], rfl, .refl _⟩
      · obtain ⟨hU, hUS, hUA, hUR, hUZ⟩ :=
          runStep hLow (by omega) hSub hFlt hAcc hReg (.inl ⟨rfl, ht⟩)
        obtain ⟨v, rest, tail, hv, hRest, hTarget, consumed, heq, hPath⟩ :=
          ih he hU.1 hU.2 hUS (fun h' => hUZ h' hU.2) hUA hUR
        exact ⟨v, rest, tail, hv, hRest, hTarget, consumed, heq, .tau ht hPath⟩
    | @ev t u e es vs he' hW ih =>
      have hFrom := estep_source_pc he'
      have he'' : target ∈ es := by
        rcases List.mem_cons.mp he with h | h
        · rw [← h] at hFrom
          change target.pc = t.pc at hFrom
          omega
        · exact h
      by_cases hEq : t.pc = 9057
      · obtain ⟨i, hc, hNotLocal, _⟩ := estep_event_source he'
        rw [hEq, Flow.code_9057] at hc
        obtain rfl := Option.some.inj hc
        cases hNotLocal
      · obtain ⟨hU, hUS, hUA, hUR, hUZ⟩ :=
          runStep hLow (by omega) hSub hFlt hAcc hReg (.inr ⟨e, rfl, he'⟩)
        obtain ⟨v, rest, tail, hv, hRest, hTarget, consumed, heq, hPath⟩ :=
          ih he'' hU.1 hU.2 hUS (fun h' => hUZ h' hU.2) hUA hUR
        exact ⟨v, rest, tail, hv, hRest, hTarget, e :: consumed,
          congrArg (e :: ·) heq, .event he' hPath⟩
    | @last t e he' =>
      have hFrom := estep_source_pc he'
      rw [(List.mem_singleton.mp he).symm] at hFrom
      change target.pc = t.pc at hFrom
      omega
  exact go hw hm hAt.1.ge (by rw [hAt.1]; decide) (by rw [hAt.2.1]; decide)
    (fun _ => hAt.2.1) hAt.2.2.1 hAt.2.2.2.2

/-- An observed store reaches the final address checkpoint with its event still in the suffix. -/
theorem cutLseReadyPrefix {p : Params} {l : Launch} {g batch head tile pc : Nat}
    {s : TState} {a : Acc} {bs : List Byte} {es : List Event} {visits : List Visit}
    (hPc : pc = 9073 ∨ pc = 9082) (hAt : At s 7985 (lseFootprintEntryFacts p l g batch head tile))
    (hw : Walk kernel Assumptions.all l g s es visits) (hm : ⟨pc, .wr a bs⟩ ∈ es) :
    ∃ u rest tail, At u 9057 (lseFootprintEntryFacts p l g batch head tile) ∧
      Walk kernel Assumptions.all l g u rest tail ∧ ⟨pc, .wr a bs⟩ ∈ rest := by
  obtain ⟨u, rest, tail, hu, hWalk, he, _⟩ :=
    cutLseReadyFromLateEvent (by change 9057 < pc; omega) hAt hw hm
  exact ⟨u, rest, tail, hu, hWalk, he⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
