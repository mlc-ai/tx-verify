-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderScratchFrame
public import Kernels.TmlFa4Fwd.Proof.MmaRoleFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

def loaderRingWrites : Op → List Nat
  | .mbarWait dst .. => [dst]
  | .mbarArrive _ _ _ _ _ _ _ dst => dst.toList
  | op => writesRegs op

private def ringFrameOp : Op → Bool
  | .warp w => Mma.linearWarpOp w
  | .mem a => if a.rule == some .threadAccess then scratchMemory a else (.mem a : Op).isLocal
  | .cpTensor _ _ _ _ _ _ _ _ none _ _ => true
  | .setMaxReg .. => true
  | .cpAsync .. | .cpAsyncCommit | .cpAsyncArrive .. | .mbarWait .. | .mbarArrive .. => true
  | op => op.isLocal

private theorem ringFrameCode :
    ((kernel.code.drop 174).take (1901 - 174)).all (fun i => ringFrameOp i.op) = true := by
  set_option maxRecDepth 100000 in decide +kernel

private theorem ringEventFrame {l : Launch} {g : Nat} {s u : TState}
    {e : Event} {ins : Instr} (hc : kernel.code[s.pc]? = some ins)
    (hOp : ringFrameOp ins.op = true) (hLocal : ins.op.isLocal = false)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s ins.op) e (some u))
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    (∀ r, r ∉ loaderRingWrites ins.op → u.regs r = s.regs r) ∧
      (loaderSubShape s → (s.sub = 0 → s.acc = []) → u.sub = 0 → u.acc = []) := by
  generalize hop : ins.op = op at hOp hLocal hf ⊢
  cases op <;> simp only [ringFrameOp, hLocal, Bool.false_eq_true] at hOp
  case warp w =>
    constructor
    · intro r hKeep
      apply Mma.mmaEventRegs hc
      · simpa only [hop, Mma.linearEventOp] using hOp
      · simpa only [hop, Mma.mmaWrites, loaderRingWrites] using hKeep
      · exact he
    · intro _ hAcc hSub
      rw [Mma.linearWarpAccumulator hOp hf]
      exact hAcc ((Mma.linearWarpAdvances hOp hf).2.symm.trans hSub)
  case mem a =>
    cases hr : a.rule == some .threadAccess <;>
      simp only [hr, Bool.false_eq_true, ↓reduceIte] at hOp
    refine ⟨fun r hKeep => scratchMemoryFrame hOp hKeep hf, ?_⟩
    intro hShape hAcc
    rcases scratchMemoryContinuation hOp hf with ⟨_, bs, rfl⟩ | ⟨hStore, rfl⟩
    · unfold afterAccessLoad
      split
      · exact hAcc
      · split
        · intro hZero
          change s.sub + 1 = 0 at hZero
          omega
        · exact fun _ => rfl
    · have hZero : s.sub = 0 := by
        by_contra hn
        obtain ⟨op, hI, hV, _⟩ := hShape.2 (by have := hShape.1; omega)
        have he := Option.some.inj (hc.symm.trans hI)
        have hOpEq : ins.op = op := congrArg Instr.op he
        rw [← hOpEq, hop, loaderVector, hStore] at hV
        cases hV
      have hAcc' := hAcc hZero
      unfold afterStore
      split <;> exact fun _ => hAcc'
  case mbarWait d base off parity acquire scope =>
    obtain ⟨_, _, _, _, _, rfl⟩ := fires_wait hf
    refine ⟨?_, fun _ ha hn => ha hn⟩
    intro r hKeep
    have hNot : r ≠ d := by simpa [loaderRingWrites] using hKeep
    exact Function.update_of_ne hNot _ _
  case mbarArrive base off tx count cluster release scope dst =>
    obtain ⟨rfl, _⟩ := fires_arrive_state hf
    cases dst with
    | none => exact ⟨fun _ _ => rfl, fun _ ha hn => ha hn⟩
    | some d =>
      refine ⟨?_, fun _ ha hn => ha hn⟩
      intro r hKeep
      have hNot : r ≠ d := by simpa [loaderRingWrites] using hKeep
      exact Function.update_of_ne hNot _ _
  case cpTensor ca grp dst off map cs mb moff mask mode policy =>
    cases mask
    · obtain ⟨_, _, _, rfl, _⟩ := fires_cpTensor_issue hf
      exact ⟨fun _ _ => rfl, fun _ ha hn => ha hn⟩
    · cases hOp
  case setMaxReg inc n =>
    obtain rfl := fires_next (op := .setMaxReg inc n) trivial hf
    exact ⟨fun _ _ => rfl, fun _ ha hn => ha hn⟩
  case cpAsyncCommit =>
    obtain rfl : u = next s := Option.some.inj hf.2
    exact ⟨fun _ _ => rfl, fun _ ha hn => ha hn⟩
  case cpAsync db doff sb soff size src policy =>
    have h : CallbackFrame (· = next s)
        (eventTmpl Assumptions.all l g s (.cpAsync db doff sb soff size src policy)) := by
      simp only [eventTmpl, cpAsyncTmpl]
      apply ofExec_frame
      repeat' first | rfl | (apply allOk_bind; intro v) | split
    obtain rfl := callbackFrame_fires h hf
    exact ⟨fun _ _ => rfl, fun _ ha hn => ha hn⟩
  case cpAsyncArrive noinc base off generic =>
    have h : CallbackFrame (· = next s)
        (eventTmpl Assumptions.all l g s (.cpAsyncArrive noinc base off generic)) := by
      simp only [eventTmpl, cpAsyncTmpl]
      apply ofExec_frame
      repeat' first | rfl | (apply allOk_bind; intro v) | split
    obtain rfl := callbackFrame_fires h hf
    exact ⟨fun _ _ => rfl, fun _ ha hn => ha hn⟩

private theorem checkedRingFrame {pc : Nat} {ins : Instr} (hLo : 174 ≤ pc)
    (hHi : pc < 1901) (hc : kernel.code[pc]? = some ins) : ringFrameOp ins.op = true := by
  have hGet : ((kernel.code.drop 174).take (1901 - 174))[pc - 174]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
    exact hc
  exact List.all_eq_true.mp ringFrameCode ins (List.mem_of_getElem? hGet)

/-- The actual pipeline's copy, shuffle and memory steps preserve registers outside their
instruction's decoded destinations. This includes the wait and arrival predicates. -/
theorem loaderPipelineStepRegs {l : Launch} {g r : Nat} {s u : TState} {e : Option Event}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hKeep : ∀ ins, kernel.code[s.pc]? = some ins → r ∉ loaderRingWrites ins.op)
    (h : WStep kernel Assumptions.all l g s e u) : u.regs r = s.regs r := by
  rcases h with ⟨-, ht⟩ | ⟨_, -, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore (by omega) (by omega)]
    obtain ⟨ins, hc⟩ := tau_core_has_code ht'
    have hh := hKeep ins hc
    have hWrites : r ∉ writesRegs ins.op := by
      cases ho : ins.op <;> simp_all [loaderRingWrites, writesRegs]
    exact tau_core_regs hc ht' hWrites
  · obtain ⟨ins, hc, hLocal, hf⟩ := estep_event_source he
    exact (ringEventFrame hc (checkedRingFrame hLo hHi hc) hLocal hf he).1 r (hKeep ins hc)

theorem ringStepRegs {l : Launch} {g r : Nat} {s u : TState} {e : Option Event}
    (hLo : 917 ≤ s.pc) (hHi : s.pc < 1744)
    (hKeep : ∀ ins, kernel.code[s.pc]? = some ins → r ∉ loaderRingWrites ins.op)
    (h : WStep kernel Assumptions.all l g s e u) : u.regs r = s.regs r :=
  loaderPipelineStepRegs (by omega) (by omega) hKeep h

def RingShape (s : TState) : Prop :=
  loaderSubShape s ∧ (s.sub = 0 → s.acc = [])

theorem loaderPipelineStepShape {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901) (hs : RingShape s)
    (h : WStep kernel Assumptions.all l g s e u) : RingShape u := by
  rcases h with ⟨-, ht⟩ | ⟨_, -, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore (by omega) (by omega)]
    obtain ⟨ins, hc⟩ := tau_core_has_code ht'
    have hZero : s.sub = 0 := by
      by_contra hn
      obtain ⟨op, hi, _, hl⟩ := hs.1.2 (by have := hs.1.1; omega)
      exact tau_core_not_event hi hl ht'
    rcases tau_core_frame hc ht' with rfl | h
    · exact ⟨⟨by simp [skip], by simp [skip]⟩, fun _ => rfl⟩
    · have hz := h.sub.trans hZero
      exact ⟨⟨by omega, by omega⟩, fun _ => h.acc.trans (hs.2 hZero)⟩
  · obtain ⟨ins, hc, hLocal, hf⟩ := estep_event_source he
    exact ⟨(loaderEventProgress (by omega) (by omega) hs.1 he).1,
      (ringEventFrame hc (checkedRingFrame hLo hHi hc) hLocal hf he).2 hs.1 hs.2⟩

theorem ringStepShape {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 917 ≤ s.pc) (hHi : s.pc < 1744) (hs : RingShape s)
    (h : WStep kernel Assumptions.all l g s e u) : RingShape u :=
  loaderPipelineStepShape (by omega) (by omega) hs h

end
end PTX.Kernels.TmlFa4Fwd.Loader
