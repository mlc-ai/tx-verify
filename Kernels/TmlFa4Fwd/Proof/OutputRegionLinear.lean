-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Proof.MmaLinearEvents
public import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

/-- The epilogue's extra returning events are stores, group operations and release arrivals. -/
def epilogueExtraOp : Op → Bool
  | .cpTensorStore .. | .bulkCommit | .bulkWait .. | .mbarArrive .. => true
  | _ => false

private def Advances (t u : TState) : Prop :=
  u.pc = t.pc + 1 ∧ u.sub = t.sub ∧ u.acc = t.acc ∧ u.fault = t.fault

private theorem tensorStoreAdvances {l : Launch} {g : Nat} {t : TState}
    {map : Opnd} {cs : List Opnd} {src : Nat} {off : Int} {policy : Option Opnd}
    {mode : TensorMode} {reduce : Option AtomOp} :
    CallbackFrame (Advances t) (tensorStoreTmpl l g t (.cpTensorStore map cs src off
      policy mode reduce)) := by
  simp only [tensorStoreTmpl]
  apply ofExec_frame
  apply allOk_bind
  rintro ⟨_, _⟩
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem arriveAdvances {l : Launch} {g : Nat} {t : TState} {base : Nat}
    {off : Int} {tx cnt : Opnd} {cluster release : Bool} {scope : MbarScope} {dst : Option Nat} :
    CallbackFrame (Advances t)
      (widenMbarScope Assumptions.all t.pc (tmaTmpl l g t (.mbarArrive base off tx cnt
        cluster release scope dst))) := by
  apply widen_next
  cases cluster <;> simp only [tmaTmpl, Bool.false_eq_true, ↓reduceIte] <;> apply ofExec_frame
  all_goals
    repeat' (apply allOk_bind; intro v)
    cases dst <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- A returning output issue, async-group event, or release arrival advances by one instruction.
Any fault before the callback terminates the trace. -/
theorem epilogueExtraProgress {l : Launch} {g : Nat} {s u : TState} {e : Event} {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) (hop : epilogueExtraOp ins.op = true)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.pc = s.pc + 1 ∧ u.sub = s.sub ∧ u.acc = s.acc ∧ u.fault = s.fault := by
  obtain ⟨i, hCode, _, hFire⟩ := estep_event_source he
  rw [hc] at hCode
  obtain rfl := Option.some.inj hCode
  generalize h : ins.op = op at hop hFire
  cases op <;> try contradiction
  case cpTensorStore => exact callbackFrame_fires tensorStoreAdvances hFire
  case mbarArrive => exact callbackFrame_fires arriveAdvances hFire
  case bulkCommit =>
    have h : u = next s := Option.some.inj hFire.2
    subst u
    exact ⟨rfl, rfl, rfl, rfl⟩
  case bulkWait =>
    have h : u = next s := Option.some.inj hFire.2
    subst u
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The outputs of a returning epilogue-only event are the named arrival-state register,
when one is present. Other registers retain their exact values. -/
def epilogueExtraWrites : Op → List Nat
  | .mbarArrive _ _ _ _ _ _ _ dst => dst.toList
  | _ => []

theorem epilogueExtraRegs {l : Launch} {g r : Nat} {s u : TState} {e : Event} {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) (hop : epilogueExtraOp ins.op = true)
    (hReg : r ∉ epilogueExtraWrites ins.op) (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.regs r = s.regs r := by
  obtain ⟨i, hCode, _, hFire⟩ := estep_event_source he
  rw [hc] at hCode
  obtain rfl := Option.some.inj hCode
  generalize h : ins.op = op at hop hFire hReg
  cases op <;> try contradiction
  case cpTensorStore map cs src off policy mode reduce =>
    have hf : CallbackFrame (fun t => t.regs r = s.regs r)
        (tensorStoreTmpl l g s (.cpTensorStore map cs src off policy mode reduce)) := by
      simp only [tensorStoreTmpl]
      apply ofExec_frame
      apply allOk_bind
      rintro ⟨_, _⟩
      rfl
    exact callbackFrame_fires hf hFire
  case mbarArrive base off tx cnt cluster release scope dst =>
    have hf : CallbackFrame (fun t => t.regs r = s.regs r)
        (widenMbarScope Assumptions.all s.pc
          (tmaTmpl l g s (.mbarArrive base off tx cnt cluster release scope dst))) := by
      apply widen_next
      cases cluster <;> simp only [tmaTmpl, Bool.false_eq_true, ↓reduceIte] <;> apply ofExec_frame
      all_goals
        repeat' (apply allOk_bind; intro v)
        cases dst with
        | none => rfl
        | some d =>
          have hd : r ≠ d := by simpa [epilogueExtraWrites] using hReg
          exact Function.update_of_ne hd _ _
    exact callbackFrame_fires hf hFire
  case bulkCommit =>
    have hu : u = next s := Option.some.inj hFire.2
    rw [hu]
    rfl
  case bulkWait =>
    have hu : u = next s := Option.some.inj hFire.2
    rw [hu]
    rfl

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
