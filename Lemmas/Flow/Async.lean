-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.EventFrameSource
public import Lemmas.Execution.EventFrame
public import Lemmas.Flow.Next
public import Lemmas.Flow.Hooks

@[expose] public section

/-! # The thread state after barrier, Tensor Memory and bulk-store events

A proof tool. Named barriers, Tensor Memory waits and releases, TMA stores and bulk-group
commits and waits continue at the next instruction; a Tensor Memory load continues with its
destination registers set to the values it returned; a plain load continues with its
destination set to the bytes it read. -/

namespace PTX.Flow
open PTX PTX.EventFrame

noncomputable section

/-- Instructions of this kind whose only continuation is the next instruction. -/
def AsyncAdvancesOp : Op → Prop
  | .barSync .. | .barSyncN .. | .tcWaitLd | .tcRelinquish .. | .tcDealloc ..
  | .tcFenceBefore | .tcFenceAfter | .cpTensorStore .. | .bulkCommit | .bulkWait .. => True
  | _ => False

theorem fires_async_next {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {op : Op}
    {pc : Nat} {e : Event} (h : AsyncAdvancesOp op)
    (hf : Fires pc (eventTmpl A L g t op) e (some u)) : u = next t := by
  have hm : CallbackFrame (· = next t) (eventTmpl A L g t op) := by
    cases op <;> simp only [AsyncAdvancesOp] at h <;>
      simp only [eventTmpl, barTmpl, tcTmpl, tensorStoreTmpl]
    all_goals first
      | rfl
      | (apply ofExec_frame
         repeat' first
           | rfl
           | exact True.intro
           | (apply allOk_bind; intro v)
           | split)
      | (repeat' first
           | rfl
           | exact True.intro
           | split)
  exact callbackFrame_fires (P := (· = next t)) hm hf

/-- After a Tensor Memory load the destinations hold the values the event returned. -/
theorem fires_tcLd {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {ds : List Nat} {ta : Nat} {sh : TcShape} {pc : Nat} {e : Event}
    (hsh : ∀ s, sh ≠ .packed16 s)
    (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta sh)) e (some u))
    (hw : A.any (·.tcLdWait t.pc) = false := by hooks_off) :
    ∃ a vals, vals.length = ds.length ∧ e = ⟨pc, .tc (.ld a vals sh)⟩ ∧
      u = setRegs (next t) ds vals := by
  rw [eventTmpl_tcLd_noWait hw, tcTmpl_tcLd_none hsh] at hf
  cases ha : readBits L g t 32 (.reg ta) with
  | error f =>
    simp [ofExec, ha, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hf
    split_ifs at hf <;> simp [Fires] at hf
  | ok a =>
    simp [ofExec, ha, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf
    split_ifs at hf <;> simp only [Fires] at hf
    all_goals first
      | (simp at hf; done)
      | (obtain ⟨vals, hl, rfl, hu⟩ := hf
         exact ⟨_, vals, hl, rfl, Option.some.inj hu⟩)

theorem storeTmpl_cases {L : Launch} {g : Nat} {t : TState} {sp : Space} {w : Nat}
    {base : Nat} {off : Int} {srcs : List Opnd} :
    (∃ f, storeTmpl L g t sp w base off srcs = .ub f) ∨
      ∃ a bs, storeTmpl L g t sp w base off srcs = .write a bs (afterStore t srcs) := by
  unfold storeTmpl
  repeat' split
  all_goals first | exact .inl ⟨_, rfl⟩ | exact .inr ⟨_, _, rfl⟩

/-- After a store that continues the thread is in `afterStore` of the stored operands. -/
theorem fires_st {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {a : MemAccess}
    {pc : Nat} {e : Event} (hk : a.kind = .store)
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e (some u)) :
    ∃ r bs, e = ⟨pc, .wr r bs⟩ ∧ u = afterStore t a.srcs := by
  simp only [eventTmpl, memTmpl] at hf
  split at hf
  · rename_i sp base _ _ _ _
    split at hf
    · exact absurd hk (by simp_all)
    · exact absurd hk (by simp_all)
    · rename_i v _ _ hv
      rw [hv]
      rcases storeTmpl_cases (L := L) (g := g) (t := t) (sp := sp) (w := a.elem.width)
        (base := base) (off := a.addr.off) (srcs := [v]) with ⟨f, hl⟩ | ⟨r, bs, hl⟩
      · simp only [releaseStoreTmpl, hl] at hf
        exact absurd hf.2 (by simp)
      · simp only [releaseStoreTmpl, hl] at hf
        exact ⟨_, bs, hf.1, Option.some.inj hf.2⟩
    · rcases storeTmpl_cases (L := L) (g := g) (t := t) (sp := sp) (w := a.elem.width)
        (base := base) (off := a.addr.off) (srcs := a.srcs) with ⟨f, hl⟩ | ⟨r, bs, hl⟩
      · rw [hl] at hf
        exact absurd hf.2 (by simp)
      · rw [hl] at hf
        exact ⟨r, bs, hf.1, Option.some.inj hf.2⟩
    · rcases accessTmpl_store (A := A) (L := L) (g := g) (t := t) hk with ⟨f, h⟩ | ⟨r, bs, -, h⟩ <;>
        rw [h] at hf
      · simp only [Fires] at hf
        exact absurd hf.2 (by simp)
      · simp only [Fires] at hf
        exact ⟨r, bs, hf.1, Option.some.inj hf.2⟩
  · have hab : atomTmpl A L g t a = .ub .noRule := by
      simp only [atomTmpl, hk, MemKind.atomOp?]
      rfl
    rw [hab] at hf
    simp only [Fires] at hf
    exact absurd hf.2 (by simp)
  · split at hf
    · rcases accessTmpl_store (A := A) (L := L) (g := g) (t := t) hk with ⟨f, h⟩ | ⟨r, bs, -, h⟩ <;>
        rw [h] at hf
      · simp only [Fires] at hf
        exact absurd hf.2 (by simp)
      · simp only [Fires] at hf
        exact ⟨r, bs, hf.1, Option.some.inj hf.2⟩
    · simp only [Fires] at hf
      exact absurd hf.2 (by simp)

end
end PTX.Flow
