-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderScratchFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

structure ScratchLoop where
  head : Nat
  back : Nat
  test : Nat
  seed : Nat

/-- Each unrolled two-row scratch transaction has one predicate-controlled backedge. -/
def loaderScratchLoop : Fin 9 → ScratchLoop
  | 0 => ⟨488, 514, 4, 772⟩
  | 1 => ⟨522, 537, 5, 773⟩
  | 2 => ⟨787, 802, 6, 774⟩
  | 3 => ⟨921, 956, 8, 775⟩
  | 4 => ⟨965, 980, 9, 776⟩
  | 5 => ⟨1211, 1226, 10, 777⟩
  | 6 => ⟨1401, 1426, 11, 778⟩
  | 7 => ⟨1435, 1450, 12, 779⟩
  | 8 => ⟨1616, 1631, 13, 780⟩

private def predInstr (dst : Nat) (src : Opnd) : MoveInstr :=
  ⟨.scalar, .pred, [some dst], [src]⟩

private def predMove (dst : Nat) (src : Opnd) : Op :=
  .move (predInstr dst src)

private def purePredMove (ins : Instr) (dst : Nat) (src : Opnd) : Bool :=
  ins.guard.isNone && match ins.op with
  | .move mv => decide (mv = predInstr dst src)
  | _ => false

private def predBackedge (ins : Instr) (test head : Nat) : Bool :=
  ins.guard == some (test, false) && match ins.op with
  | .bra pc uni => pc == head && !uni
  | _ => false

private def scratchLoopChecked (loop : ScratchLoop) (ins : Instr) (pc : Nat) : Bool :=
  if pc = loop.head then purePredMove ins loop.test (.reg loop.seed)
  else if pc + 1 = loop.back then purePredMove ins loop.seed (.imm 0)
  else if pc = loop.back then predBackedge ins loop.test loop.head
  else !((writesRegs ins.op).contains loop.test) &&
    (match ins.op with
     | .mem a => scratchMemory a && !a.regs.contains loop.test
     | .bra target _ => loop.head < target && target < loop.back
     | .brx .. => false
     | _ => ins.op.isLocal)

private theorem scratchLoopSlice (i : Fin 9) :
    let loop := loaderScratchLoop i
    (((kernel.code.drop loop.head).take (loop.back + 1 - loop.head)).zipIdx loop.head).all
      (fun (ins, pc) => scratchLoopChecked loop ins pc) = true := by
  fin_cases i <;> (set_option maxRecDepth 100000 in decide +kernel)

theorem scratchLoopBounds (i : Fin 9) :
    let loop := loaderScratchLoop i
    174 ≤ loop.head ∧ loop.head + 2 < loop.back ∧ loop.back < 1906 ∧ loop.test ≠ loop.seed := by
  fin_cases i <;> decide

private theorem scratchLoopCode (i : Fin 9) {pc : Nat} {ins : Instr}
    (hLo : (loaderScratchLoop i).head ≤ pc) (hHi : pc ≤ (loaderScratchLoop i).back)
    (hc : kernel.code[pc]? = some ins) :
    scratchLoopChecked (loaderScratchLoop i) ins pc = true := by
  let loop := loaderScratchLoop i
  have hGet :
      (((kernel.code.drop loop.head).take (loop.back + 1 - loop.head)).zipIdx loop.head)[
        pc - loop.head]? = some (ins, pc) := by
    have h₀ : loop.head ≤ pc := hLo
    have h₁ : pc ≤ loop.back := hHi
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le h₀, hc]
    rfl
  exact List.all_eq_true.mp (scratchLoopSlice i) _ (List.mem_of_getElem? hGet)

def scratchBudget (loop : ScratchLoop) (s : TState) : Nat := by
  classical
  exact if s.regs (if s.pc = loop.head then loop.seed else loop.test) =
    some (.pred false) then 1 else 2

theorem scratchBudgetRange (loop : ScratchLoop) (s : TState) :
    1 ≤ scratchBudget loop s ∧ scratchBudget loop s ≤ 2 := by
  by_cases h : s.pc = loop.head <;>
    simp only [scratchBudget, h, ↓reduceIte] <;> split <;> decide

private theorem falseMove {l : Launch} {g dst : Nat} {s u : TState} {src : Opnd}
    (hc : kernel.code[s.pc]? = some ⟨none, predMove dst src⟩)
    (hsrc : src = .imm 0 ∨ ∃ r, src = .reg r ∧ s.regs r = some (.pred false))
    (ht : Tau kernel [] l g s u) : u = next (setReg s dst (.pred false)) := by
  have hf : s.fault = none := by
    cases he : s.fault
    · rfl
    · simp [Tau, out, he] at ht
  have he : execLocalA [] l g s (predMove dst src) =
      .ok (next (setReg s dst (.pred false))) := by
    rcases hsrc with rfl | ⟨_, rfl, hReg⟩
    · rw [predMove, execLocalA_nil, execLocal_move (by rfl)]
      simp [predInstr, execMove, readPred, bind, Except.bind, pure, Except.pure]
    · rw [predMove, execLocalA_nil, execLocal_move (by rfl)]
      simp [predInstr, execMove, readPred, readReg, hReg, bind, Except.bind, pure, Except.pure]
  have hLocal : (predMove dst src).isLocal = true := by
    rcases hsrc with rfl | ⟨_, rfl, _⟩ <;> rfl
  unfold Tau at ht
  exact (Out.tau.inj (by
    simpa only [out, hf, hc, guardHolds, hLocal, he, pure, Except.pure, ite_true] using ht)).symm

private theorem inactiveBranch {l : Launch} {g target test : Nat} {s u : TState}
    (hc : kernel.code[s.pc]? = some ⟨some (test, false), .bra target false⟩)
    (hf : s.regs test = some (.pred false)) (ht : Tau kernel [] l g s u) :
    u = skip s := by
  have he : s.fault = none := by
    cases h : s.fault
    · rfl
    · simp [Tau, out, h] at ht
  have hGuard : guardHolds s (some (test, false)) = .ok false := by
    simp [guardHolds, readReg, hf, bind, Except.bind, pure, Except.pure]
  unfold Tau at ht
  exact (Out.tau.inj (by simpa only [out, he, hc, hGuard] using ht)).symm

private theorem scratchRegular {loop : ScratchLoop} {pc : Nat} {ins : Instr}
    (hHead : pc ≠ loop.head) (hPre : pc + 1 ≠ loop.back) (hBack : pc ≠ loop.back)
    (h : scratchLoopChecked loop ins pc = true) :
    loop.test ∉ writesRegs ins.op ∧ (∀ tgt, ¬ BrxTarget ins.op tgt) ∧
      (nextPc ins.op pc = pc + 1 ∨
        loop.head < nextPc ins.op pc ∧ nextPc ins.op pc < loop.back) ∧
      (ins.op.isLocal = true ∨
        ∃ a, ins.op = .mem a ∧ scratchMemory a = true ∧ loop.test ∉ a.regs) := by
  simp only [scratchLoopChecked, hHead, hPre, hBack, ↓reduceIte, Bool.and_eq_true] at h
  have hk : loop.test ∉ writesRegs ins.op := by simpa using h.1
  refine ⟨hk, ?_⟩
  have hrest := h.2
  generalize ho : ins.op = op at hrest ⊢
  cases op <;> simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at hrest
  case bra target uni =>
    exact ⟨by simp [BrxTarget], .inr hrest, .inl rfl⟩
  case mem a =>
    exact ⟨by simp [BrxTarget], .inl rfl, .inr ⟨a, rfl, hrest.1, by simpa using hrest.2⟩⟩
  all_goals exact ⟨by simp [BrxTarget], .inl rfl, .inl hrest⟩

private theorem eventKeepsTest {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {loop : ScratchLoop} {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins)
    (hm : ins.op.isLocal = true ∨
      ∃ a, ins.op = .mem a ∧ scratchMemory a = true ∧ loop.test ∉ a.regs)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.regs loop.test = s.regs loop.test := by
  obtain ⟨actual, hi, hLocal, hf⟩ := estep_event_source he
  obtain rfl : actual = ins := Option.some.inj (hi.symm.trans hc)
  rcases hm with h | ⟨a, hop, ha, ht⟩
  · rw [hLocal] at h
    cases h
  · rw [hop] at hf
    exact scratchMemoryFrame ha ht hf

private theorem purePredMove_eq {ins : Instr} {dst : Nat} {src : Opnd}
    (h : purePredMove ins dst src = true) : ins = ⟨none, predMove dst src⟩ := by
  rcases ins with ⟨guard, op⟩
  cases op <;> simp only [purePredMove, Bool.and_eq_true, Option.isNone_iff_eq_none,
    decide_eq_true_eq, Bool.false_eq_true, and_false] at h
  case move m => simp [predMove, h.1, h.2]

private theorem predBackedge_eq {ins : Instr} {test head : Nat}
    (h : predBackedge ins test head = true) :
    ins = ⟨some (test, false), .bra head false⟩ := by
  rcases ins with ⟨guard, op⟩
  cases op <;> simp only [predBackedge, Bool.and_eq_true, beq_iff_eq,
    Bool.false_eq_true, and_false] at h
  case bra tgt uni =>
    have hu : uni = false := by cases uni <;> simp_all
    simp [h.1, h.2.1, hu]

private theorem scratchTauCore {l : Launch} {g : Nat} {s u : TState}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906)
    (ht : Tau kernel Assumptions.all l g s u) : Tau kernel [] l g s u := by
  unfold Tau at ht ⊢
  rwa [← loaderOutCore hLo hHi]

private theorem scratchStepHasCode {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906)
    (hw : WStep kernel Assumptions.all l g s e u) : ∃ ins, kernel.code[s.pc]? = some ins := by
  rcases hw with ⟨-, ht⟩ | ⟨_, -, he⟩
  · exact tau_core_has_code (scratchTauCore hLo hHi ht)
  · obtain ⟨ins, hc, _, _⟩ := estep_event_source he
    exact ⟨ins, hc⟩

private theorem scratchLocalStep {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} {ins : Instr} (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906)
    (hc : kernel.code[s.pc]? = some ins) (hl : ins.op.isLocal = true)
    (hw : WStep kernel Assumptions.all l g s e u) : Tau kernel [] l g s u := by
  rcases hw with ⟨-, ht⟩ | ⟨_, -, he⟩
  · exact scratchTauCore hLo hHi ht
  · obtain ⟨i, hi, hiL, _⟩ := estep_event_source he
    obtain rfl : i = ins := Option.some.inj (hi.symm.trans hc)
    rw [hl] at hiL
    cases hiL

private theorem scratchMovePc {l : Launch} {g dst : Nat} {s u : TState} {src : Opnd}
    (hc : kernel.code[s.pc]? = some ⟨none, predMove dst src⟩)
    (ht : Tau kernel [] l g s u) : u.pc = s.pc + 1 := by
  rcases tau_core_frame hc ht with rfl | h
  · rfl
  · exact h.pc.resolve_right (by simp [BrxTarget, predMove])

theorem scratchStep (i : Fin 9) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event}
    (hS : (loaderScratchLoop i).head ≤ s.pc ∧ s.pc ≤ (loaderScratchLoop i).back)
    (hU : (loaderScratchLoop i).head ≤ u.pc ∧ u.pc ≤ (loaderScratchLoop i).back)
    (hSeed : s.pc = (loaderScratchLoop i).back →
      s.regs (loaderScratchLoop i).seed = some (.pred false))
    (hw : WStep kernel Assumptions.all l g s e u) :
    let loop := loaderScratchLoop i
    (u.pc = loop.back → u.regs loop.seed = some (.pred false)) ∧
      (if s.pc = loop.back then 1 else 0) + scratchBudget loop u ≤ scratchBudget loop s := by
  classical
  let loop := loaderScratchLoop i
  have hB : 174 ≤ loop.head ∧ loop.head + 2 < loop.back ∧ loop.back < 1906 ∧
      loop.test ≠ loop.seed := scratchLoopBounds i
  change loop.head ≤ s.pc ∧ s.pc ≤ loop.back at hS
  change loop.head ≤ u.pc ∧ u.pc ≤ loop.back at hU
  have hLo : 174 ≤ s.pc := by omega
  have hHi : s.pc < 1906 := by omega
  obtain ⟨ins, hc⟩ := scratchStepHasCode hLo hHi hw
  have hCode : scratchLoopChecked loop ins s.pc = true := scratchLoopCode i hS.1 hS.2 hc
  change (u.pc = loop.back → u.regs loop.seed = some (.pred false)) ∧
    (if s.pc = loop.back then 1 else 0) + scratchBudget loop u ≤ scratchBudget loop s
  by_cases hHead : s.pc = loop.head
  · have hMov := purePredMove_eq (show purePredMove _ _ _ = true from by
      simpa only [scratchLoopChecked, hHead, ↓reduceIte] using hCode)
    rw [hMov] at hc
    have ht := scratchLocalStep hLo hHi hc (by rfl) hw
    have hPc := scratchMovePc hc ht
    have huHead : u.pc ≠ loop.head := by omega
    have huBack : u.pc ≠ loop.back := by omega
    have hsBack : s.pc ≠ loop.back := by omega
    refine ⟨fun h => (huBack h).elim, ?_⟩
    rw [ite_eq_right hsBack, Nat.zero_add]
    by_cases hF : s.regs loop.seed = some (.pred false)
    · have he := falseMove hc (.inr ⟨_, rfl, hF⟩) ht
      have hTest : u.regs loop.test = some (.pred false) := by simp [he, setReg, next]
      simp [scratchBudget, hHead, huHead, hF, hTest]
    · have hsBudget : scratchBudget loop s = 2 := by simp [scratchBudget, hHead, hF]
      exact hsBudget.symm ▸ (scratchBudgetRange loop u).2
  by_cases hPre : s.pc + 1 = loop.back
  · have hMov := purePredMove_eq (show purePredMove _ _ _ = true from by
      simpa only [scratchLoopChecked, hHead, hPre, ↓reduceIte] using hCode)
    rw [hMov] at hc
    have ht := scratchLocalStep hLo hHi hc (by rfl) hw
    have he := falseMove hc (.inl rfl) ht
    have hsBack : s.pc ≠ loop.back := by omega
    have huHead : u.pc ≠ loop.head := by rw [he]; change s.pc + 1 ≠ loop.head; omega
    have hSeed' : u.regs loop.seed = some (.pred false) := by simp [he, setReg, next]
    have hTest : u.regs loop.test = s.regs loop.test := by
      rw [he]
      exact Function.update_of_ne hB.2.2.2 _ _
    refine ⟨fun _ => hSeed', ?_⟩
    simp [hsBack, scratchBudget, hHead, huHead, hTest]
  by_cases hBack : s.pc = loop.back
  · have hLoop : loop.back ≠ loop.head := by omega
    have hNext : loop.back + 1 ≠ loop.back := by omega
    have hBra := predBackedge_eq (show predBackedge _ _ _ = true from by
      simpa only [scratchLoopChecked, hBack, hLoop, hNext, ↓reduceIte] using hCode)
    rw [hBra] at hc
    have ht := scratchLocalStep hLo hHi hc (by rfl) hw
    have hPc : u.pc = loop.head := by
      rcases tau_core_frame hc ht with rfl | h
      · have hu := hU.2
        change s.pc + 1 ≤ loop.back at hu
        omega
      · exact h.pc.resolve_right (by simp [BrxTarget])
    have hSeed' : u.regs loop.seed = some (.pred false) :=
      (tau_core_regs hc ht (by simp [writesRegs])).trans (hSeed hBack)
    have hTest : s.regs loop.test ≠ some (.pred false) := by
      intro h
      have he := inactiveBranch hc h ht
      rw [he] at hPc
      change s.pc + 1 = loop.head at hPc
      omega
    refine ⟨fun h => by omega, ?_⟩
    simp [hBack, scratchBudget, hLoop, hPc, hSeed', hTest]
  have hChecked := scratchRegular hHead hPre hBack hCode
  have hProgress :
      (u.pc = s.pc ∨ u.pc = s.pc + 1 ∨ loop.head < u.pc ∧ u.pc < loop.back) ∧
      u.regs loop.test = s.regs loop.test := by
    rcases hw with ⟨-, ht⟩ | ⟨ev, -, he⟩
    · have ht' := scratchTauCore hLo hHi ht
      refine ⟨.inr ?_, tau_core_regs hc ht' hChecked.1⟩
      rcases tau_core_frame hc ht' with rfl | h
      · exact .inl rfl
      · rw [h.pc.resolve_right (hChecked.2.1 _)]
        exact hChecked.2.2.1
    · have heCore : EStep kernel [] l g s ev (some u) := by
        obtain ⟨tmpl, hout, hf⟩ := he
        exact ⟨tmpl, by rwa [← loaderOutCore hLo hHi], hf⟩
      exact ⟨(estep_return_pc heCore (fun _ _ _ h => execLocal_frame h)).2.imp_right Or.inl,
        eventKeepsTest hc hChecked.2.2.2 he⟩
  have huHead : u.pc ≠ loop.head := by rcases hProgress.1 with h | h | h <;> omega
  have huBack : u.pc ≠ loop.back := by rcases hProgress.1 with h | h | h <;> omega
  exact ⟨fun h => (huBack h).elim, by simp [hBack, scratchBudget, hHead, huHead, hProgress.2]⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
