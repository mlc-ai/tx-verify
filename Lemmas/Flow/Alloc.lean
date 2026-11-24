-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.EventFrameSource
public import Lemmas.Execution.EventFrame

@[expose] public section

/-! # The thread state after a Tensor Memory allocation

A proof tool. `tcgen05.alloc` performs two events at one instruction: the allocation request,
and on lane 0 the store of the returned address to shared memory, whose column is open
(`sub = 1` between them). -/

namespace PTX.Flow
open PTX PTX.EventFrame

noncomputable section

/-- After the allocation event lane 0 goes on to the address store; the other lanes continue
at the next instruction. The event names the request only. -/
theorem fires_tcAlloc {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {group : CtaGroup} {base : Nat} {off : Int} {nc : Opnd} {pc : Nat} {e : Event}
    (hs : t.sub = 0)
    (hf : Fires pc (eventTmpl A L g t (.tcAlloc group base off nc)) e (some u)) :
    ∃ dst n, e = ⟨pc, .tc (.resource group (some dst) (.alloc n))⟩ ∧
      u = if laneOf L g = 0 then { t with sub := 1 } else next t := by
  simp only [eventTmpl, tcTmpl] at hf
  cases hd : effAddr L g t .shared base off with
  | error f =>
    simp [ofExec, hd, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw, Fires] at hf
    split_ifs at hf <;> simp at hf
  | ok dst =>
    cases hn : readBits L g t 32 nc with
    | error f =>
      simp [ofExec, hd, hn, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw, Fires] at hf
      split_ifs at hf <;> simp at hf
    | ok n =>
      simp [ofExec, hd, hn, hs, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hf
      split_ifs at hf <;> simp only [Fires] at hf
      all_goals first
        | (simp at hf; done)
        | (obtain ⟨rfl, hu⟩ := hf
           exact ⟨dst, n.toNat, rfl, by simp_all⟩)

/-- On lane 0 the second event stores the address, with its column open; the thread then
continues at the next instruction. -/
theorem fires_tcAlloc_write {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {group : CtaGroup} {base : Nat} {off : Int} {nc : Opnd} {pc : Nat} {e : Event}
    (hs : t.sub = 1)
    (hf : Fires pc (eventTmpl A L g t (.tcAlloc group base off nc)) e (some u)) :
    ∃ a bs, e = ⟨pc, .wr a bs⟩ ∧ u = { t with pc := t.pc + 1, sub := 0 } := by
  simp only [eventTmpl, tcTmpl] at hf
  cases hd : effAddr L g t .shared base off with
  | error f =>
    simp [ofExec, hd, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw, Fires] at hf
    split_ifs at hf <;> simp at hf
  | ok dst =>
    cases hn : readBits L g t 32 nc with
    | error f =>
      simp [ofExec, hd, hn, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw, Fires] at hf
      split_ifs at hf <;> simp at hf
    | ok n =>
      simp [ofExec, hd, hn, hs, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hf
      split_ifs at hf
      all_goals first
        | (simp [Fires] at hf; done)
        | (simp only [Fires] at hf
           obtain ⟨col, -, rfl, hu⟩ := hf
           exact ⟨_, _, rfl, Option.some.inj hu⟩)

/-- After its first sub-step the allocation's template is its address store or undefined
behaviour. -/
theorem eventTmpl_alloc_store {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {group : CtaGroup} {base : Nat} {off : Int} {nc : Opnd} (hs : t.sub ≠ 0) :
    (∃ f, eventTmpl A L g t (.tcAlloc group base off nc) = .ub f) ∨
      ∃ dst u, eventTmpl A L g t (.tcAlloc group base off nc) = .tcAllocStore dst u := by
  simp only [eventTmpl, tcTmpl]
  cases effAddr L g t .shared base off with
  | error f =>
    left
    simp [ofExec, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    split_ifs <;> simp
  | ok dst =>
    cases readBits L g t 32 nc with
    | error f =>
      left
      simp [ofExec, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
      split_ifs <;> simp
    | ok n =>
      simp [ofExec, hs, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw]
      split_ifs <;> simp

end
end PTX.Flow
