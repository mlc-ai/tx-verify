-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotRmw
public import Lemmas.Flow.Hooks

@[expose] public section

/-! # The element index of an access event is the thread's sub-step

A proof tool. An access event of an instruction fired from thread state `t` has element index `0`
or `t.sub` (`fires_elem`): only `elemAcc` sets a nonzero element, and it sets the sub-step. -/

namespace PTX.Flow


/-- The element index of an access is `0` or the thread's sub-step. -/
def ElemOk (n : Nat) : Tmpl → Prop
  | .read a _ | .readNC a _ | .write a _ _ | .rmw a _ _ => a.elem = 0 ∨ a.elem = n
  | _ => True

theorem elemAcc_elem {b : Loc} {n c j : Nat} {a : Acc} (h : elemAcc b n c j = .ok a) :
    a.elem = j := by
  unfold elemAcc at h
  split at h
  · cases h
  · cases h; rfl

theorem semAcc_elem (m : MemAccess) (a : Acc) : (m.semAcc a).elem = a.elem := by
  unfold MemAccess.semAcc; split <;> rfl

theorem elemSub_bind_ok {α β : Type} {r : Exec α} {f : α → Exec β} {b : β}
    (h : (r >>= f) = .ok b) : ∃ x, r = .ok x ∧ f x = .ok b := by
  cases r with
  | error => cases h
  | ok x => exact ⟨x, rfl, h⟩

theorem loadTmpl_elem {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {sp nc w ds base off} :
    ElemOk t.sub (loadTmpl A L g t sp nc w ds base off) := by
  unfold loadTmpl
  split
  · trivial
  · rename_i a h
    obtain ⟨x, -, h⟩ := elemSub_bind_ok h
    have := elemAcc_elem h
    split
    · split <;> first | trivial | exact .inr this
    · exact .inr this

theorem storeTmpl_elem {L : Launch} {g : Nat} {t : TState} {sp w base off srcs} :
    ElemOk t.sub (storeTmpl L g t sp w base off srcs) := by
  unfold storeTmpl
  split
  · trivial
  · rename_i a h
    obtain ⟨x, -, h⟩ := elemSub_bind_ok h
    have := elemAcc_elem h
    split
    · trivial
    · split
      · trivial
      · exact .inr this

theorem acquireLoadTmpl_elem {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {sc sp w d base off} :
    ElemOk t.sub (acquireLoadTmpl A L g t sc sp w d base off) := by
  unfold acquireLoadTmpl
  have h := loadTmpl_elem (A := A) (L := L) (g := g) (t := t) (sp := sp) (nc := false) (w := w)
    (ds := [d]) (base := base) (off := off)
  split
  · rename_i a k hk
    rw [hk] at h
    exact h
  · rename_i hk
    exact h

theorem releaseStoreTmpl_elem {L : Launch} {g : Nat} {t : TState} {sc sp w base off v} :
    ElemOk t.sub (releaseStoreTmpl L g t sc sp w base off v) := by
  unfold releaseStoreTmpl
  have h := storeTmpl_elem (L := L) (g := g) (t := t) (sp := sp) (w := w) (base := base)
    (off := off) (srcs := [v])
  split
  · rename_i a k hk
    rw [hk] at h
    exact h
  · exact h

theorem accessAcc_elem {L : Launch} {g : Nat} {t : TState} {a : MemAccess} {acc : Acc}
    (h : accessAcc L g t a = .ok acc) : acc.elem = t.sub := by
  unfold accessAcc at h
  obtain ⟨x, -, h⟩ := elemSub_bind_ok h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
    Functor.map, Except.map] at h
  split at h <;> try (cases h)
  split at h <;> try (cases h)
  rename_i hh
  split at h
  · cases h
  · cases h
    rw [semAcc_elem]; exact elemAcc_elem (by assumption)

theorem bulkInitTmpl_elem {L : Launch} {g : Nat} {t : TState} {a : MemAccess} :
    ElemOk t.sub (bulkInitTmpl L g t a) := by
  unfold bulkInitTmpl
  extract_lets r
  cases r with
  | error f => exact trivial
  | ok p => exact Or.inl rfl

theorem accessTmpl_elem {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} : ElemOk t.sub (accessTmpl A L g t a) := by
  unfold accessTmpl
  dsimp only
  split
  · exact bulkInitTmpl_elem
  · split
    · trivial
    · rename_i acc h
      have := accessAcc_elem h
      split
      · split <;> first | trivial | exact .inr this
      · exact .inr this
  · split
    · trivial
    · rename_i acc h
      have := accessAcc_elem h
      split
      · trivial
      · split
        · trivial
        · exact .inr this
  · trivial

theorem atomTmpl_elem {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} : ElemOk t.sub (atomTmpl A L g t a) := by
  unfold atomTmpl
  split
  extract_lets n elemOf r
  rcases hh : r with f | ⟨op, acc, vs⟩
  · exact trivial
  · refine Or.inr ?_
    show acc.elem = t.sub
    simp only [r] at hh
    simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at hh
    repeat' split at hh
    all_goals try (cases hh; done)
    all_goals (cases hh; exact elemAcc_elem (by assumption))

theorem memTmpl_elem {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} : ElemOk t.sub (memTmpl A L g t a) := by
  unfold memTmpl
  repeat' split
  all_goals first
    | trivial
    | exact loadTmpl_elem
    | exact storeTmpl_elem
    | exact acquireLoadTmpl_elem
    | exact releaseStoreTmpl_elem
    | exact accessTmpl_elem
    | exact atomTmpl_elem

theorem widen_elemOk {n : Nat} {A : List Assumption} {site : Nat} {m : Tmpl}
    (h : ElemOk n m) : ElemOk n (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_elemOk {n : Nat} {r : Exec Tmpl} (h : PTX.EventFrame.AllOk (ElemOk n) r) :
    ElemOk n (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

theorem eventTmpl_elem {A : List Assumption} {L : Launch} {g : Nat} {t : TState} (op : Op) :
    ElemOk t.sub (eventTmpl A L g t op) := by
  cases op
  case mem a =>
    simp only [eventTmpl]
    exact memTmpl_elem
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_elemOk
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_elemOk)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [warpTmpl, barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | exact Or.inl rfl
         | (apply ofExec_elemOk)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- An access event of an instruction fired from state `t` has element index `0` or `t.sub`. -/
theorem fires_elem {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} {a : Acc}
    (hf : Fires pc (eventTmpl A L g t op) e o) (ha : e.acc = some a) :
    a.elem = 0 ∨ a.elem = t.sub := by
  have h := eventTmpl_elem (A := A) (L := L) (g := g) (t := t) op
  generalize eventTmpl A L g t op = m at h hf
  obtain ⟨epc, ek⟩ := e
  cases m <;> simp only [Fires, Event.mk.injEq] at hf <;> simp only [ElemOk] at h <;>
    aesop (add norm simp [Event.acc])
end PTX.Flow
