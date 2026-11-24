-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Code
public import Lemmas.Execution.EventFrameSource

@[expose] public section

/-! # Continuations of `bar.sync` with a count, `relinquish_alloc_permit`, `dealloc` and `cp.async`

A proof tool (promoted from the tml-fa4 MMA warp's and loader warps' proofs). `bar.sync` with a
count, `tcgen05.relinquish_alloc_permit`, `tcgen05.dealloc`, a `cp.async` copy,
`cp.async.commit_group` and `cp.async.mbarrier.arrive` continue at the next instruction
(`fires_barSyncN_next`, `fires_tcRelinquish_next`, `fires_tcDealloc_next`, `fires_cpAsync_next`,
`fires_cpAsyncCommit_next`, `fires_cpAsyncArrive_next`); `advances` (`Step/SiteCases.lean`) uses
them. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.EventFrame

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

theorem fires_barSyncN_next {t u : TState} {a b : Opnd} {al : Bool} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.barSyncN a b al)) e (some u)) : u = PTX.next t := by
  simp only [eventTmpl, barTmpl] at hf
  repeat' split at hf
  all_goals simp_all [Fires]

theorem fires_tcRelinquish_next {t u : TState} {group : CtaGroup} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.tcRelinquish group)) e (some u)) : u = PTX.next t := by
  have hm : CallbackFrame (· = PTX.next t) (eventTmpl A L g t (.tcRelinquish group)) := by
    simp only [eventTmpl, tcTmpl]
    apply ofExec_frame
    repeat' first
      | rfl
      | exact True.intro
      | split
  exact callbackFrame_fires (P := (· = PTX.next t)) hm hf

theorem fires_tcDealloc_next {t u : TState} {group : CtaGroup} {ta nc : Opnd} {pc : Nat}
    {e : Event} (hf : Fires pc (eventTmpl A L g t (.tcDealloc group ta nc)) e (some u)) :
    u = PTX.next t := by
  have hm : CallbackFrame (· = PTX.next t) (eventTmpl A L g t (.tcDealloc group ta nc)) := by
    simp only [eventTmpl, tcTmpl]
    apply ofExec_frame
    repeat' first
      | rfl
      | exact True.intro
      | (apply allOk_bind; intro v)
      | split
  exact callbackFrame_fires (P := (· = PTX.next t)) hm hf

theorem fires_cpAsync_next {t u : TState} {db : Nat} {doff : Int} {sb : Nat} {soff : Int}
    {size : Nat} {source : CpAsyncSource} {policy : Option Opnd} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.cpAsync db doff sb soff size source policy)) e
      (some u)) : u = PTX.next t := by
  have hm : CallbackFrame (· = PTX.next t)
      (eventTmpl A L g t (.cpAsync db doff sb soff size source policy)) := by
    simp only [eventTmpl, cpAsyncTmpl]
    apply ofExec_frame
    repeat' first
      | rfl
      | exact True.intro
      | (apply allOk_bind; intro v)
      | split
  exact callbackFrame_fires (P := (· = PTX.next t)) hm hf

theorem fires_cpAsyncCommit_next {t u : TState} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t .cpAsyncCommit) e (some u)) : u = PTX.next t := by
  simp only [eventTmpl, cpAsyncTmpl] at hf
  simp_all [Fires]

theorem fires_cpAsyncArrive_next {t u : TState} {noinc : Bool} {base : Nat} {off : Int}
    {generic : Bool} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.cpAsyncArrive noinc base off generic)) e (some u)) :
    u = PTX.next t := by
  have hm : CallbackFrame (· = PTX.next t)
      (eventTmpl A L g t (.cpAsyncArrive noinc base off generic)) := by
    simp only [eventTmpl, cpAsyncTmpl]
    apply ofExec_frame
    repeat' first
      | rfl
      | exact True.intro
      | (apply allOk_bind; intro v)
      | split
  exact callbackFrame_fires (P := (· = PTX.next t)) hm hf

end
end PTX.Flow
