-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.GuardOrder
public import Lemmas.Snoc.ObjectAppend
public import Lemmas.Snoc.SnocObjectOrder

@[expose] public section

/-! # Guarded synchronization under appended events

An execution without release writes or atomics has no release/acquire memory read
(`noSynchronizesWith_of`), and one without thread fences no fence synchronization. If no write,
atomic or fence of `X` releases or fences, appending an event that is no write, atomic or fence,
and is at a canonical spin if it is a successful poll, keeps synchronization guarded, also with
an object record that replies no wait outcome. -/

namespace PTX
noncomputable section
variable {L : Launch} {K : Kernel} {X : Execution}

/-- No `hb` edge of an execution without release writes or atomics is a release/acquire memory
read. -/
theorem noSynchronizesWith_of {Y : Execution}
    (h : ∀ e pc a bs, Y.get e = some ⟨pc, .wr a bs⟩ → a.release = false)
    (hr : ∀ e pc a o n, Y.get e = some ⟨pc, .rmw a o n⟩ → a.release = false) (e f : EvId) :
    ¬ synchronizesWith L Y e f := by
  rintro ⟨a, b, bs, cs, ⟨pc, hw⟩ | ⟨o, pc, hw⟩, -, hrel, -⟩
  · rw [h e pc a bs hw] at hrel
    cases hrel
  · rw [hr e pc a o _ hw] at hrel
    cases hrel

/-- Appending an event that is no write, atomic or fence keeps synchronization guarded, when no
write or atomic of `X` releases, `X` has no fence, and a successful poll that is appended is at
a canonical spin. -/
theorem SyncGuarded.snoc (hsg : SyncGuarded L K X)
    (hnr : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false)
    (hnrmw : ∀ e pc a o n, X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false)
    (hnf : ∀ e sem s, ¬ X.ThreadFence e sem s) {g : Nat}
    {ev : Event} {r : Nat → Option AsyncCopy.Ref}
    (hk : ∀ a bs, ev.kind ≠ .wr a bs) (hrmw : ∀ a o n, ev.kind ≠ .rmw a o n)
    (hfence : ∀ sem s, ev.kind ≠ .fence sem s)
    (hspin : ∀ pc m q acq sc, ev = ⟨pc, .wait m q true acq sc⟩ → ∃ exit, K.CanonicalSpin pc exit) :
    SyncGuarded L K (X.snoc g ev r) := by
  have old : ∀ {v pc k}, (X.snoc g ev r).get v = some ⟨pc, k⟩ →
      X.get v = some ⟨pc, k⟩ ∨ ev = ⟨pc, k⟩ := by
    intro v pc k h
    rw [snoc_get] at h
    split_ifs at h
    · exact .inr (Option.some.inj h)
    · exact .inl h
  refine ⟨fun w pc m q acq sc hw => ?_, fun e f => ⟨noSynchronizesWith_of
    (fun e pc a bs he => ?_) (fun e pc a o n he => ?_) e f, not_fenceSync_of_noFence ?_ e f⟩,
    fun m i j r w hr hw hok hij => hsg.noFault m i j r w hr hw hok hij⟩
  · rcases old hw with hw | hw
    · exact hsg.spin w pc m q acq sc hw
    · exact hspin pc m q acq sc hw
  · rcases old he with he | he
    · exact hnr _ _ _ _ he
    · exact absurd (congrArg Event.kind he) (hk a bs)
  · rcases old he with he | he
    · exact hnrmw _ _ _ _ _ he
    · exact absurd (congrArg Event.kind he) (hrmw a o n)
  · rintro e sem s ⟨pc, he⟩
    rcases old he with he | he
    · exact hnf e sem s ⟨pc, he⟩
    · exact absurd (congrArg Event.kind he) (hfence sem s)

/-- Appending an event that is no write, atomic or fence, with an object record that replies no
wait outcome, keeps synchronization guarded. -/
theorem SyncGuarded.snocObject (hsg : SyncGuarded L K X)
    (hnr : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false)
    (hnrmw : ∀ e pc a o n, X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false)
    (hnf : ∀ e sem s, ¬ X.ThreadFence e sem s) {g : Nat}
    {ev : Event} {r : Nat → Option AsyncCopy.Ref}
    {mb : Loc} {rec : MBarrier.Record AsyncCopy.Ref} (hk : ∀ a bs, ev.kind ≠ .wr a bs)
    (hrmw : ∀ a o n, ev.kind ≠ .rmw a o n) (hfence : ∀ sem s, ev.kind ≠ .fence sem s)
    (hspin : ∀ pc m q acq sc, ev = ⟨pc, .wait m q true acq sc⟩ → ∃ exit, K.CanonicalSpin pc exit)
    (hrec : rec.reply.waited = none) :
    SyncGuarded L K (X.snocObject g ev r mb rec) := by
  have hs := hsg.snoc hnr hnrmw hnf (g := g) (r := r) hk hrmw hfence hspin
  refine ⟨hs.spin, hs.noMemSync, fun m i j r' w hr hw hok hij => ?_⟩
  simp only [Execution.snocObject, Execution.appendObject, snoc_objects] at hr hw
  split_ifs at hr hw with hm
  · subst hm
    have hj : j < (X.objects m).length := by
      by_contra hn
      have hl := (List.getElem?_eq_some_iff.mp hw).1
      simp only [List.length_append, List.length_singleton] at hl
      rw [List.getElem?_append_right (by omega)] at hw
      have hj' : j - (X.objects m).length = 0 := by omega
      rw [hj'] at hw
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
      subst hw
      rw [hrec] at hok
      cases hok
    rw [List.getElem?_append_left (by omega)] at hr
    rw [List.getElem?_append_left hj] at hw
    exact hsg.noFault m i j r' w hr hw hok hij
  · exact hsg.noFault m i j r' w hr hw hok hij

end
end PTX
