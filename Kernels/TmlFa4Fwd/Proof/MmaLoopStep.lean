-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaLoopCounter
public import Lemmas.Flow.Tc
public import Lemmas.Flow.Next

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

private def steadyWarpOp : WarpInstr → Bool
  | ⟨.elect, _, [d, some p], [], some _⟩ => (d != some 7204) && (p != 7204)
  | ⟨.shfl _, _, [some d], [_, _, _], some _⟩ => d != 7204
  | _ => false

private def steadyEventOp (op : Op) : Bool :=
  match op with
  | .tcMma .. | .tcCommit .. => true
  | .mbarWait dst .. => dst != 7204
  | .warp w => steadyWarpOp w
  | _ => false

private theorem steadyEventCode {pc : Nat} {ins : Instr} (hlo : 2291 ≤ pc) (hhi : pc < 2530)
    (hc : kernel.code[pc]? = some ins) (hl : ins.op.isLocal = false) :
    steadyEventOp ins.op = true := by
  have hall : ((kernel.code.drop 2291).take 239).all
      (fun i => i.op.isLocal || steadyEventOp i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hi : ((kernel.code.drop 2291).take 239)[pc - 2291]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hlo]
    exact hc
  simpa only [hl, Bool.false_or] using List.all_eq_true.mp hall ins (List.mem_of_getElem? hi)

private theorem mmaReturnsNext {l : Launch} {g : Nat} {t u : TState} {ins : TcMmaInstr}
    {e : Event} (hf : Fires t.pc (mmaTmpl l g t ins) e (some u)) : u = next t := by
  apply callbackFrame_fires (P := (· = next t)) _ hf
  unfold mmaTmpl
  split
  · apply ofExec_frame
    repeat' first | rfl | trivial | (apply allOk_bind; intro v) | split
  · apply ofExec_frame
    repeat' first | rfl | trivial | (apply allOk_bind; intro v) | split
  · trivial

/-- Event continuations preserve the trip counter and advance exactly once.
Faults have no returning continuation here. -/
theorem steadyEventFrame {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hlo : 2291 ≤ s.pc) (hhi : s.pc < 2530)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.pc = s.pc + 1 ∧ u.sub = s.sub ∧ u.acc = s.acc ∧ u.fault = s.fault ∧
      u.regs 7204 = s.regs 7204 := by
  obtain ⟨ins, hc, hl, hf⟩ := estep_event_source he
  have hOp := steadyEventCode hlo hhi hc hl
  generalize ho : ins.op = op at hOp hf
  cases op <;> try contradiction
  case tcMma mi =>
    have hu := mmaReturnsNext hf
    subst u
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  case tcCommit =>
    obtain rfl := fires_tcCommit hf
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  case mbarWait dst base off par acq sc =>
    change (dst != 7204) = true at hOp
    have hDst : 7204 ≠ dst := Ne.symm (by simpa using hOp)
    obtain ⟨_, _, _, _, _, rfl⟩ := fires_wait hf
    exact ⟨rfl, rfl, rfl, rfl, Function.update_of_ne hDst _ _⟩
  case warp w =>
    change steadyWarpOp w = true at hOp
    unfold steadyWarpOp at hOp
    split at hOp
    · rename_i _ ty d p mask
      obtain ⟨hD, hP⟩ : d ≠ some 7204 ∧ p ≠ 7204 := by simpa using hOp
      obtain ⟨_, _, _, _, rfl⟩ := fires_elect hf
      cases d with
      | none => exact ⟨rfl, rfl, rfl, rfl, Function.update_of_ne hP.symm _ _⟩
      | some d =>
        refine ⟨rfl, rfl, rfl, rfl, ?_⟩
        change Function.update (Function.update _ d _) p _ 7204 = _
        have hD' : 7204 ≠ d := by intro h; exact hD (by rw [← h])
        rw [Function.update_of_ne hP.symm, Function.update_of_ne hD']
    · rename_i _ mode ty d a b c mask
      have hD : 7204 ≠ d := Ne.symm (by simpa using hOp)
      obtain ⟨_, _, _, _, _, _, rfl⟩ := fires_shfl (p := none) hf
      exact ⟨rfl, rfl, rfl, rfl, Function.update_of_ne hD _ _⟩
    · exact (Bool.noConfusion hOp)

/-- Local steady instructions preserve the trip counter and follow the decoded control flow. -/
theorem steadyTauFrame {l : Launch} {g : Nat} {s u : TState}
    (hlo : 2291 ≤ s.pc) (hhi : s.pc < 2530)
    (hSub : s.sub = 0) (hAcc : s.acc = [])
    (ht : Tau kernel Assumptions.all l g s u) :
    (s.pc < u.pc ∨ (s.pc, u.pc) ∈ steadyPollBackedges) ∧
      2291 ≤ u.pc ∧ u.pc ≤ 2530 ∧
      u.sub = s.sub ∧ u.acc = s.acc ∧ u.fault = s.fault ∧ u.regs 7204 = s.regs 7204 := by
  have ht' : Tau kernel [] l g s u := by
    unfold Tau at ht ⊢
    rw [← out_eq_core (by omega) (by omega)]
    exact ht
  obtain ⟨ins, hc⟩ := tau_core_has_code ht'
  have hRegs := counterFrame hlo hhi hc
  have hCtl := steadyControl hlo (by omega) hc
  have hBounds : match ins.op with
    | .bra dst _ => dst ≤ 2530
    | _ => True := by
    have hall : ((kernel.code.drop 2291).take 239).all
        (fun i => match i.op with | .bra dst _ => dst ≤ 2530 | _ => true) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    have hi : ((kernel.code.drop 2291).take 239)[s.pc - 2291]? = some ins := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hlo]
      exact hc
    have h := List.all_eq_true.mp hall ins (List.mem_of_getElem? hi)
    cases hop : ins.op <;> simp_all
  have hT := tau_core_frame hc ht'
  rcases hT with rfl | hT
  · exact ⟨.inl (by simp [skip]), by simp [skip]; omega, by simp [skip]; omega,
      hSub.symm, hAcc.symm, rfl, rfl⟩
  · have hPc := hT.pc
    have hLanding : (s.pc < u.pc ∨ (s.pc, u.pc) ∈ steadyPollBackedges) ∧
        2291 ≤ u.pc ∧ u.pc ≤ 2530 := by
      cases hop : ins.op <;> simp only [hop, BrxTarget, nextPc, or_false] at hPc hCtl hBounds
      case bra dst uni =>
        obtain ⟨hL, -, hForward | hPoll | hBack⟩ := hCtl
        · exact ⟨.inl (by omega), by omega, by omega⟩
        · exact ⟨.inr (hPc ▸ hPoll), by omega, by omega⟩
        · omega
      all_goals exact ⟨.inl (by omega), by omega, by omega⟩
    exact ⟨hLanding.1, hLanding.2.1, hLanding.2.2, hT.sub, hT.acc, hT.fault, hT.regs _ hRegs⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
