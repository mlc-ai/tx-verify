-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyCursorTrace
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Mma

private def afterDrainStep (pc : Nat) (ins : Instr) : Bool :=
  (ins.op.isLocal || Epilogue.ordinaryEvent ins.op) &&
  match ins.op with
  | .brx .. => false
  | _ => decide (1744 ≤ nextPc ins.op pc)

private theorem codeAfterDrain {pc : Nat} {ins : Instr} (hLo : 1744 ≤ pc)
    (hc : kernel.code[pc]? = some ins) : afterDrainStep pc ins = true := by
  let tail := (kernel.code.drop 1744).zipIdx 1744
  have hAll : tail.all (fun (i, site) => afterDrainStep site i) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hAt : tail[pc-1744]? = some (ins,pc) := by
    dsimp [tail]
    rw [List.getElem?_zipIdx, List.getElem?_drop, Nat.add_sub_of_le hLo, hc]
    rfl
  exact List.all_eq_true.mp hAll _ (List.mem_of_getElem? hAt)

private theorem afterDrainSeg {s u : TState} {se : SegMatch CuteSlot}
    (hSite : s.pc ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel s.pc = some se)
    (hu : Assumptions.execSwExp2 se s = .ok u) : 1744 ≤ u.pc := by
  have hAll : Assumptions.swExp2Sites.all (fun pc => match cuteExp2.matchAt kernel pc with
      | none => false | some x => decide (1744 ≤ x.stop)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hCode := List.all_eq_true.mp hAll _ hSite
  rw [hm] at hCode
  exact (Softmax.scoreSegmentFrame hu).1.symm ▸ of_decide_eq_true hCode

private theorem stepAfterDrain {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 1744 ≤ s.pc) (he : WStep kernel Assumptions.all l g s e u) : 1744 ≤ u.pc := by
  rcases he with ⟨_, ht⟩ | ⟨ev, _, he⟩
  · obtain ⟨i, hc, _, hSource⟩ := Softmax.tauScoreSource ht
    rcases hSource with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
    · change 1744 ≤ s.pc + 1
      omega
    · rcases Softmax.scoreExecLocal hLocal with hCore | ⟨se, hSite, hm, hu⟩
      · have hNext := hCore.pc
        have hCode := (Bool.and_eq_true_iff.mp (codeAfterDrain hLo hc)).2
        cases hi : i.op <;> simp only [hi, BrxTarget, or_false] at hNext hCode
        all_goals first
          | exact hNext.symm ▸ of_decide_eq_true hCode
          | exact Bool.noConfusion hCode
      · exact afterDrainSeg hSite hm hu
  · obtain ⟨i, hc, hl, hFire⟩ := estep_event_source he
    have hCode := (Bool.and_eq_true_iff.mp (codeAfterDrain hLo hc)).1
    simp only [hl, Bool.false_or] at hCode
    rcases callbackFrame_fires (Epilogue.ordinaryEventFrame hCode) hFire with h | h
    · exact h.symm ▸ hLo
    · exact h.symm ▸ (Nat.le_succ_of_le hLo)

/-- The actual code never returns from its drain or a later role to a K/V packet. -/
theorem walkAfterDrain {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hs : 1744 ≤ s.pc) (hw : Walk kernel Assumptions.all l g s es vs) :
    ∀ e ∈ es, 1744 ≤ e.pc := by
  induction hw with
  | stop => simp
  | tau ht _ ih => exact ih (stepAfterDrain hs (.inl ⟨rfl, ht⟩))
  | ev he _ ih =>
    intro e h
    rcases List.mem_cons.mp h with rfl | h
    · exact (estep_source_pc he).symm ▸ hs
    · exact ih (stepAfterDrain hs (.inr ⟨_,rfl,he⟩)) e h
  | last he =>
    intro e h
    obtain rfl := List.mem_singleton.mp h
    exact (estep_source_pc he).symm ▸ hs

/-- No recurring packet publishes after the drain has started. -/
theorem noRecurringAfterDrain {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hs : 1744 ≤ s.pc) (hw : Walk kernel Assumptions.all l g s es vs) :
    ∀ e ∈ es, ¬ recurringPublicationEvent e := by
  intro e he hPub
  have hLo := walkAfterDrain hs hw e he
  obtain ⟨site, loc, rfl⟩ := hPub
  have hHi : Loader.reuseArrival site < 1744 := by fin_cases site <;> decide
  exact (Nat.not_lt_of_ge hLo) hHi

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
