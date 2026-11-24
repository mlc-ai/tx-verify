-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescalePublicationFinite
import Kernels.TmlFa4Fwd.Proof.Thread.RescaleAbiScale
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
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
import Lemmas.Execution.EventFrameSource
import Lemmas.Flow.MemTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Softmax

noncomputable section

private theorem rescaleWriteAdvances {l : Launch} {g base r : Nat} {s u : TState}
    {e : Event} (hf : Fires s.pc (storeTmpl l g s .shared 32 base 368 [.reg r]) e (some u)) :
    u.pc = s.pc+1 := by
  unfold storeTmpl at hf
  split at hf
  · cases hf.2
  · cases hs : s.sub with
    | succ k =>
      simp only [hs,List.getElem?_cons_succ,List.getElem?_nil] at hf
      cases hf.2
    | zero =>
      simp only [hs,List.getElem?_cons_zero] at hf
      split at hf
      · cases hf.2
      · obtain rfl := Option.some.inj hf.2
        simp [afterStore,hs]

/-- A returning rescale store advances to its following instruction. -/
theorem rescaleStoreAdvances {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (biased : Bool) (hp : s.pc = (statsStore (rescaleStore biased)).pc)
    (he : EStep kernel Assumptions.all l g s e (some u)) : u.pc = s.pc+1 := by
  obtain ⟨ins,hCode,_,hf⟩ := estep_event_source he
  cases biased
  · change s.pc = 6890 at hp
    rw [hp,Flow.code_6890] at hCode
    obtain rfl := Option.some.inj hCode
    exact rescaleWriteAdvances (base := 5518) (r := 1492) hf
  · change s.pc = 5682 at hp
    rw [hp,Flow.code_5682] at hCode
    obtain rfl := Option.some.inj hCode
    exact rescaleWriteAdvances (base := 4571) (r := 1362) hf

/-- The shift reuses the negated scale from the opening round and the paired scale
loaded upon entry to the plain loop. -/
def RescaleShiftScales (p : Params) (biased : Bool) (t : TState) : Prop :=
  t.regs 1230 = some (fl (-abiFloat p.scaleLog2Bits)) ∧
    (biased = false → t.regs 8692 =
      some (joinValue (b32 p.scaleLog2Bits) (b32 p.scaleLog2Bits)))

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (biased : Bool) {g j : Nat} {a : Acc}
    {data : List Byte} (he : StatisticsStore X (g,j) (rescaleStore biased) a data)
include hp hX biased he

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
