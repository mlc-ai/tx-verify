-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Select
public import Kernels.InklingRelDecode.Proof.Thread.TmAll

@[expose] public section

/-! # `TmplOk` of the thread machine

`Code.TmplOk` says that no state of the machine, at a concrete state that satisfies the state's
facts and the invariant, fires an undefined-behaviour template. `Thread/Tm*.lean` prove it for
every state of the two composed machines that is not in `WComp.tmRest` or `DComp.tmRest`; both
are empty, so `TmplRest` (the statement for those states) holds (`tmplRest_holds`) and `tmplOk`
is `TmplOk` of `threadCode` from `Pre` alone (the development notes, "Pins in the invariants, part
2"). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The states of a thread's machine whose template is not proved. -/
def TSt.tmRest : TSt → Bool
  | .d s => DComp.tmRest s
  | .w s => WComp.tmRest s

/-- **The statement left of `TmplOk`**: no state in `TSt.tmRest` fires an undefined-behaviour
template. -/
def TmplRest (Q : Params) (L : Launch) : Prop :=
  ∀ g < L.threads, ∀ (s : TSt), s.tmRest = true → ∀ (t : TState) (ins : Instr),
    (threadCode L g Q).AtD s t → (threadCode L g Q).inv s →
      kernel.code[(threadCode L g Q).pc s]? = some ins → ∀ f, eventTmpl asms L g t ins.op ≠ .ub f

/-- **`TmplOk` of every thread's machine**, from `Pre` and `TmplRest`. -/
theorem tmplOk_of {Q : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre Q L mem0)
    (hr : TmplRest Q L) : ∀ g < L.threads, (threadCode L g Q).TmplOk := by
  intro g hg s t ins hat hi hc f
  by_cases hs : s.tmRest = true
  · exact hr g hg s hs t ins hat hi hc f
  · have hs' : s.tmRest = false := by simpa using hs
    cases s with
    | d s => exact DComp.tmpl_ok hpre hg hs' (atD_d.mp hat) hi.2 hc f
    | w s => exact WComp.tmpl_ok hpre hg hs' hat hi.2 hc f

/-- **No state is left in `TSt.tmRest`.** -/
theorem tmplRest_holds {Q : Params} {L : Launch} : TmplRest Q L := by
  intro g _ s hs
  cases s <;> simp [TSt.tmRest, DComp.tmRest, WComp.tmRest] at hs

/-- **`TmplOk` of every thread's machine**, from `Pre`. -/
theorem tmplOk {Q : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre Q L mem0) :
    ∀ g < L.threads, (threadCode L g Q).TmplOk :=
  tmplOk_of hpre tmplRest_holds

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
