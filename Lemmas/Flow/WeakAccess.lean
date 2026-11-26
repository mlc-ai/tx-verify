-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.PollFacts
public import Lemmas.Flow.NotRead

@[expose] public section

/-! # Weak accesses: a kernel without strong memory semantics makes no strong access

`strongOp` lists the instructions whose events may be strong accesses (`Acc.Strong`, §8.4): the
memory accesses whose memory semantics is not `.weak` (`.relaxed`, `.acquire`, `.release`,
`.acq_rel`, `.volatile`). A read or write fired by any other instruction carries none of the
three qualifiers (`fires_read_weak`, `fires_write_weak`): a weak load, store or `st.bulk` keeps
the element footprint (`elemAcc_weak`, `accessAcc_weak`), a `ldmatrix`/`stmatrix` row and a
Tensor Memory allocation's address store have the default footprint, and no other instruction
reads or writes (`eventTmpl_notRead`, `eventTmpl_notWrite`). -/

namespace PTX.Flow
open PTX

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-- The instructions whose accesses may be strong: memory accesses with non-weak semantics. -/
def strongOp : Op → Bool
  | .mem a => decide (a.sem ≠ .weak)
  | _ => false

theorem not_strong_of {a : Acc} (h1 : a.acquire = false) (h2 : a.release = false)
    (h3 : a.relaxed = false) : ¬ a.Strong := by
  simp [Acc.Strong, h1, h2, h3]

theorem bind_elemAcc_weak {r : Exec Loc} {n c j : Nat} {a : Acc}
    (h : (r >>= fun loc => elemAcc loc n c j) = .ok a) : ¬ a.Strong := by
  cases r with
  | error f => cases h
  | ok loc =>
    obtain ⟨h1, h2, h3⟩ := elemAcc_weak (show elemAcc loc n c j = .ok a from h)
    exact not_strong_of h1 h2 h3

/-- A weak access located by `accessLoc`, or a `st.bulk`, reads and writes weakly. -/
theorem accessTmpl_weak {a : MemAccess} (hsem : a.sem = .weak) {acc : Acc}
    (h : (∃ k, accessTmpl A L g t a = .read acc k) ∨
      ∃ bs u, accessTmpl A L g t a = .write acc bs u) : ¬ acc.Strong := by
  have hacc : ∀ {acc0 : Acc}, accessAcc L g t a = .ok acc0 → ¬ acc0.Strong := fun hk =>
    have ⟨h1, h2, h3⟩ := accessAcc_weak hk hsem
    not_strong_of h1 h2 h3
  rcases h with ⟨k, h⟩ | ⟨bs, u, h⟩ <;> unfold accessTmpl at h <;> dsimp only at h <;>
    repeat' first
      | (simp only [Tmpl.read.injEq] at h; obtain ⟨rfl, -⟩ := h; exact hacc ‹_›)
      | (simp only [Tmpl.write.injEq] at h; obtain ⟨rfl, -, -⟩ := h
         first | exact hacc ‹_› | exact not_strong_of rfl rfl rfl)
      | cases h
      | split at h
      | (unfold bulkInitTmpl at h; dsimp only at h)

/-- A weak memory instruction reads and writes weakly. -/
theorem memTmpl_weak {a : MemAccess} (hsem : a.sem = .weak) {acc : Acc}
    (h : (∃ k, memTmpl A L g t a = .read acc k) ∨ ∃ bs u, memTmpl A L g t a = .write acc bs u) :
    ¬ acc.Strong := by
  have hacc := fun h' => accessTmpl_weak (A := A) (L := L) (g := g) (t := t) hsem (acc := acc) h'
  rcases h with ⟨k, h⟩ | ⟨bs, u, h⟩ <;> unfold memTmpl at h <;>
    repeat' first
      | exact hacc (.inl ⟨k, h⟩)
      | exact hacc (.inr ⟨bs, u, h⟩)
      | (simp only [hsem, reduceCtorEq] at *; done)
      | (simp only [Tmpl.read.injEq] at h; obtain ⟨rfl, -⟩ := h; exact bind_elemAcc_weak ‹_›)
      | (simp only [Tmpl.write.injEq] at h; obtain ⟨rfl, -, -⟩ := h
         exact bind_elemAcc_weak ‹_›)
      | cases h
      | split at h
      | (unfold loadTmpl at h; dsimp only at h)
      | (unfold storeTmpl at h; dsimp only at h)
      | (unfold atomTmpl at h; dsimp only at h)

/-- A `ldmatrix` row read and a `stmatrix` row write have the default footprint. -/
theorem matrixTmpl_weak {i : MatrixInstr} {acc : Acc}
    (h : (∃ k, matrixTmpl L g t i = .read acc k) ∨ ∃ bs u, matrixTmpl L g t i = .write acc bs u) :
    ¬ acc.Strong := by
  rcases h with ⟨k, h⟩ | ⟨bs, u, h⟩ <;> unfold matrixTmpl at h <;>
    repeat' first
      | dsimp only at h
      | unfold matrixMoveTmpl at h
      | (simp only [Tmpl.read.injEq] at h; obtain ⟨rfl, -⟩ := h; exact not_strong_of rfl rfl rfl)
      | (simp only [Tmpl.write.injEq] at h; obtain ⟨rfl, -, -⟩ := h
         exact not_strong_of rfl rfl rfl)
      | split at h
      | cases h

/-- **A read fired by an instruction outside `strongOp` is weak.** -/
theorem fires_read_weak {pc : Nat} {op : Op} {epc : Nat} {a : Acc} {bs : List (Option Byte)}
    {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) ⟨epc, .rd a bs⟩ o)
    (hop : strongOp op = false) : ¬ a.Strong := by
  obtain ⟨k, hm⟩ := fires_read_tmpl hf
  cases hr : readOp op
  · have hn := eventTmpl_notRead (A := A) (L := L) (g := g) (t := t) hr
    rw [hm] at hn
    exact hn.elim
  cases op <;> simp only [readOp, Bool.false_eq_true] at hr
  case mem ma =>
    exact memTmpl_weak (by simpa [strongOp] using hop) (.inl ⟨k, hm⟩)
  case matrix mi => exact matrixTmpl_weak (.inl ⟨k, hm⟩)

/-- **A write fired by an instruction outside `strongOp` is weak.** -/
theorem fires_write_weak {pc : Nat} {op : Op} {epc : Nat} {a : Acc} {bs : List Byte}
    {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) ⟨epc, .wr a bs⟩ o)
    (hop : strongOp op = false) : ¬ a.Strong := by
  rcases fires_write_tmpl hf with ⟨u, hm⟩ | ⟨u, -, ha⟩
  swap
  · rw [ha]; exact not_strong_of rfl rfl rfl
  cases hw : writeOp op
  · have hn := eventTmpl_notWrite (A := A) (L := L) (g := g) (t := t) hw
    rw [hm] at hn
    exact hn.elim
  cases op <;> simp only [writeOp, Bool.false_eq_true] at hw
  case mem ma =>
    exact memTmpl_weak (by simpa [strongOp] using hop) (.inr ⟨bs, u, hm⟩)
  case matrix mi => exact matrixTmpl_weak (.inr ⟨bs, u, hm⟩)
  case tcAlloc group base off nc =>
    simp only [eventTmpl, tcTmpl, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hm
    repeat' (first | split at hm | simp [ofExec] at hm)

end PTX.Flow
