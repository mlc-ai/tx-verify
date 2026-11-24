-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.EventFrameSource
public import Lemmas.Execution.EventFrame

@[expose] public section

/-! # The thread state after an asynchronous issue

A proof tool. An MMA issue, a Tensor Core commit and a cluster launch control cancellation
request continue at the next instruction whatever their operands evaluate to. -/

namespace PTX.Flow
open PTX PTX.EventFrame

noncomputable section

theorem fires_tcMma {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {group : CtaGroup}
    {ws : Bool} {kind : MmaKind} {dst : Nat} {ad bd id : Opnd} {mask : List Opnd} {en : Opnd}
    {pc : Nat} {e : Event} (hk : kind = .i8 ∨ kind = .f16 ∨ kind = .tf32)
    (hf : Fires pc (eventTmpl A L g t
      (.tcMma (.dense group ws kind dst (.smem ad) bd id mask en))) e (some u)) :
    u = next t := by
  have hm : CallbackFrame (· = next t)
      (eventTmpl A L g t (.tcMma (.dense group ws kind dst (.smem ad) bd id mask en))) := by
    simp only [eventTmpl, tcTmpl_tcMma_smem hk]
    apply ofExec_frame
    repeat' first
      | rfl
      | exact True.intro
      | (apply allOk_bind; intro v)
      | split
  exact callbackFrame_fires (P := (· = next t)) hm hf

theorem fires_tcCommit {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {group : CtaGroup} {base : Nat} {off : Int} {mask : Option Opnd} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.tcCommit group base off mask)) e (some u)) :
    u = next t := by
  have hm : CallbackFrame (· = next t) (eventTmpl A L g t (.tcCommit group base off mask)) := by
    simp only [eventTmpl, tcCommitTmpl]
    apply ofExec_frame
    repeat' first
      | rfl
      | exact True.intro
      | (apply allOk_bind; intro v)
      | split
  exact callbackFrame_fires (P := (· = next t)) hm hf

theorem fires_clcTryCancel {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {multicast : Bool} {dst mb : Nat} {off moff : Int} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.clcTryCancel multicast dst off mb moff)) e (some u)) :
    u = next t := by
  have hm : CallbackFrame (· = next t)
      (eventTmpl A L g t (.clcTryCancel multicast dst off mb moff)) := by
    simp only [eventTmpl, clcTmpl]
    apply ofExec_frame
    repeat' first
      | rfl
      | exact True.intro
      | (apply allOk_bind; intro v)
      | split
  exact callbackFrame_fires (P := (· = next t)) hm hf

end
end PTX.Flow
