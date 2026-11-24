-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaValueDescriptorWord
import Kernels.TmlFa4Fwd.Proof.MmaFirstReadyParity
import Kernels.TmlFa4Fwd.Proof.MmaPvPrefixCut
public import Kernels.TmlFa4Fwd.Proof.MmaRingAddress
public import Lemmas.Flow.WarpUniform
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
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
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.Final

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma

noncomputable section

/-- States outside a short local descriptor setup end at the entry or after
its broadcast. -/
def descriptorSetupOutside (prepare broadcast pos : Nat) : Prop :=
  pos ≤ prepare ∨ broadcast < pos

instance (prepare broadcast pos : Nat) : Decidable (descriptorSetupOutside prepare broadcast pos) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Each step outside descriptor setup either enters at its start or stays outside. -/
def descriptorSetupStepCode (prepare broadcast pos : Nat) (i : Instr) : Bool :=
  !decide (descriptorSetupOutside prepare broadcast pos) || pos == prepare ||
    (decide (descriptorSetupOutside prepare broadcast (pos+1)) &&
      match i.op with
      | .bra dest _ => decide (descriptorSetupOutside prepare broadcast dest)
      | .brx .. => false
      | _ => true)

private theorem descriptorSetupAuditAt {prepare broadcast : Nat}
    (hAudit : (((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907).all
      (fun (i,pos) => descriptorSetupStepCode prepare broadcast pos i) = true)
    {pos : Nat} {i : Instr}
    (hLo : 1907 ≤ pos) (hHi : pos < 2768) (hAllowed : descriptorSetupOutside prepare broadcast pos)
    (hSkip : pos ≠ prepare)
    (hGet : kernel.code[pos]? = some i) :
    descriptorSetupOutside prepare broadcast (pos+1) ∧
      (match i.op with
      | .bra dest _ => decide (descriptorSetupOutside prepare broadcast dest)
      | .brx .. => false
      | _ => true) = true := by
  let code := ((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907
  have hMem : (i,pos) ∈ code := by
    apply List.mem_of_getElem? (i := pos-1907)
    dsimp only [code]
    rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
      Nat.add_sub_of_le hLo,hGet]
    rfl
  have h := List.all_eq_true.mp hAudit (i,pos) hMem
  simp only [descriptorSetupStepCode,decide_eq_true hAllowed,Bool.not_true,
    beq_eq_false_iff_ne.mpr hSkip,Bool.false_or,Bool.and_eq_true,decide_eq_true_eq] at h
  refine ⟨h.1,?_⟩
  cases hOp : i.op
  case bra dest uni =>
    have hs : descriptorSetupOutside prepare broadcast dest := by simpa only [hOp,
      decide_eq_true_eq] using h.2
    exact decide_eq_true hs
  case brx => simp [hOp] at h
  all_goals rfl

/-- An actual ordinary step keeps a checked descriptor preparation cursor outside its slice. -/
theorem ordinaryDescriptorSetupStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    {prepare broadcast : Nat}
    (hAudit : (((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907).all
      (fun (i,pos) => descriptorSetupStepCode prepare broadcast pos i) = true)
    (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (hAllowed : descriptorSetupOutside prepare broadcast s.pc) (hSkip : s.pc ≠ prepare)
    (hw : WStep kernel Assumptions.all l g s ev u) :
    descriptorSetupOutside prepare broadcast u.pc := by
  have checked {i : Instr} (hi : kernel.code[s.pc]? = some i) :=
    descriptorSetupAuditAt hAudit hLo hHi hAllowed hSkip hi
  have hCore := out_eq_core (show 1904 ≤ s.pc by omega) hHi (l := l) (g := g) (t := s)
  rcases hw with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · have htCore : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← hCore]
    obtain ⟨i,hCode⟩ := tau_core_has_code htCore
    rcases tau_core_frame hCode htCore with rfl | h
    · exact (checked hCode).1
    have hPc := h.pc
    cases hi : i.op <;> simp only [hi, nextPc, BrxTarget, or_false] at hPc
    case bra dest uni =>
      rw [hPc]
      exact of_decide_eq_true (by simpa only [hi] using (checked hCode).2)
    case brx =>
      have habs := (checked hCode).2
      simp only [hi,Bool.false_eq_true] at habs
    all_goals exact hPc.symm ▸ (checked hCode).1
  · have heCore : EStep kernel [] l g s e (some u) := by
      obtain ⟨tm,hOut,hFire⟩ := he
      exact ⟨tm,hCore ▸ hOut,hFire⟩
    obtain ⟨i,hCode,_,_⟩ := estep_event_source he
    rcases (estep_return_pc heCore (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · exact h.symm ▸ hAllowed
    · exact h.symm ▸ (checked hCode).1

variable {p : Params} {l : Launch} {m : Mem0}

end
end PTX.Kernels.TmlFa4Fwd.Thread
