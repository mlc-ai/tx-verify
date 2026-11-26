-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Schedule.Sites
public import Kernels.FlashKdaFwd.Proof.Schedule.Dispatch

@[expose] public section

/-!
# The premise `freeTmpl`: a thread at a free site performs a free event

A state of class `free` (`siteCls`, `Defs.lean`) is at a site whose kind is none of: a shuffle,
an election, an `mbarrier.try_wait`, the matrix event of a warp matrix instruction. The
premise `Premises2.freeTmpl` asks that the template of the next event of a thread at such a
state is undefined behaviour or one of the ten "free" templates, which the dispatcher steps
without looking at another thread (`FreeTmpl`, `Proof/Progress/Progress.lean`).

The proof has no case per site. A sound machine's template at a state is the template of the
instruction at the state's site (`Flow.Code.site_out`); the kind of that instruction at the
state's sub-step is the kind of the site (`Ref.site_op`, an evaluated scan of the program,
`Proof/Ref/Kinds/Table.lean`); and `tmpl_free` shows, for every instruction, that a free kind
has a free template:

* an ordinary instruction: by the library's classification of templates
  (`Descent.tmpl_kind`); the generic loads and stores through computed shared addresses are
  ordinary reads and writes (a store instruction's template has no release semantics);
* a `trap` (the decoded `brkpt`): its template is undefined behaviour;
* an `ldmatrix` at sub-step 0: the lane reads its row (`matrix_free`); an `stmatrix` at
  sub-step 1: the lane writes its row; at the other sub-step each is at its matrix event,
  which is not of class `free`;
* the later elements of the vector load are reads of the same load instruction.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Sched PTX.Flow PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Protocol
open PTX.Kernels.FlashKdaFwd.Proof.Thread (Site)
open PTX.Kernels.FlashKdaFwd.Proof.Ref (SiteKind)

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {κ : SiteKind}

theorem FreeTmpl.exit {m : Tmpl} (h : Descent.KindTmpl .exit m) : FreeTmpl m := .inl h

theorem FreeTmpl.read {m : Tmpl} (h : Descent.KindTmpl .read m) : FreeTmpl m := .inr (.inl h)

theorem FreeTmpl.store {m : Tmpl} (h : Descent.KindTmpl .store m) : FreeTmpl m :=
  .inr (.inr (.inl h))

theorem FreeTmpl.quiet {m : Tmpl} (h : Descent.KindTmpl .quiet m) : FreeTmpl m :=
  .inr (.inr (.inr (.inl h)))

theorem FreeTmpl.init {m : Tmpl} (h : Descent.KindTmpl .init m) : FreeTmpl m :=
  .inr (.inr (.inr (.inr (.inl h))))

theorem FreeTmpl.arrive {m : Tmpl} (h : Descent.KindTmpl .arrive m) : FreeTmpl m :=
  .inr (.inr (.inr (.inr (.inr (.inl h)))))

theorem FreeTmpl.bulkWait {m : Tmpl} (h : Descent.KindTmpl .bulkWait m) : FreeTmpl m :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))

theorem FreeTmpl.tensorLoad {m : Tmpl} (h : Descent.KindTmpl .tensorLoad m) : FreeTmpl m :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))

theorem FreeTmpl.tensorStore {m : Tmpl} (h : Descent.KindTmpl .tensorStore m) : FreeTmpl m :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))

theorem FreeTmpl.bar {m : Tmpl} (h : Descent.KindTmpl .bar m) : FreeTmpl m :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))))

/-- **The free events of a warp matrix instruction**: the row read of an `ldmatrix` (sub-step
0) and the row write of an `stmatrix` (sub-step 1). -/
theorem matrix_free {i : MatrixInstr} (hκ : Ref.opKind t.sub (.matrix i) = some κ)
    (hf : kindCls κ = .free) :
    (∃ f, matrixTmpl L g t i = .ub f) ∨ FreeTmpl (matrixTmpl L g t i) := by
  have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  unfold matrixTmpl
  split
  · split
    · -- a matrix load or store
      rename_i m hrule hop
      simp only [Ref.opKind, hop] at hκ
      unfold matrixMoveTmpl
      dsimp only
      split
      · -- `stmatrix`
        rename_i hst
        simp only [hst, ↓reduceIte, Option.some.injEq] at hκ
        split
        · rename_i hs
          simp only [hs, ↓reduceIte] at hκ
          subst hκ
          cases hf
        · split
          · exact .inl ⟨_, rfl⟩
          · exact .inr (FreeTmpl.store ⟨_, _, _, rfl, rfl⟩)
      · -- `ldmatrix`
        rename_i hst
        simp only [hst, Bool.false_eq_true, ↓reduceIte] at hκ
        split at hκ
        · rename_i h32
          simp only [Option.some.injEq] at hκ
          split
          · split
            · exact .inl ⟨_, rfl⟩
            · exact .inr (FreeTmpl.read ⟨_, _, rfl⟩)
          · rename_i hs
            have hs0 : t.sub ≠ 0 := fun h0 => hs ⟨by omega, h0⟩
            simp only [hs0, ↓reduceIte] at hκ
            subst hκ
            cases hf
        · cases hκ
    · -- `movmatrix`
      rename_i d a hrule hop hd hs
      simp only [Ref.opKind, hop, Option.some.injEq] at hκ
      subst hκ
      cases hf
    · -- `mma`
      rename_i s hrule hop
      simp only [Ref.opKind, hop, Option.some.injEq] at hκ
      subst hκ
      cases hf
    · exact .inl ⟨_, rfl⟩
  · exact .inl ⟨_, rfl⟩

set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
/-- **An instruction at a sub-step of a free kind has a free template**, or its template is
undefined behaviour. -/
theorem tmpl_free {op : Op} (hκ : Ref.opKind t.sub op = some κ) (hf : kindCls κ = .free) :
    (∃ f, eventTmpl A L g t op = .ub f) ∨ FreeTmpl (eventTmpl A L g t op) := by
  have hkind := Descent.tmpl_kind (A := A) (L := L) (g := g) (t := t) op
  cases op
  case matrix i => exact matrix_free hκ hf
  case trap => exact .inl ⟨_, rfl⟩
  case ret => exact hkind.imp_right FreeTmpl.exit
  case exit => exact hkind.imp_right FreeTmpl.exit
  case mbarInit => exact hkind.imp_right FreeTmpl.init
  case fenceMbarInit => exact hkind.imp_right FreeTmpl.quiet
  case bulkCommit => exact hkind.imp_right FreeTmpl.quiet
  case barSync => exact hkind.imp_right FreeTmpl.bar
  case barSyncN => exact hkind.imp_right FreeTmpl.bar
  case mbarArrive => exact hkind.imp_right FreeTmpl.arrive
  case cpTensor => exact hkind.imp_right FreeTmpl.tensorLoad
  case cpTensorStore => exact hkind.imp_right FreeTmpl.tensorStore
  case bulkWait => exact hkind.imp_right FreeTmpl.bulkWait
  case fence f =>
    cases f with
    | thread _ _ => cases hκ
    | proxy _ _ _ => exact hkind.imp_right FreeTmpl.quiet
  case mem a =>
    simp only [Ref.opKind] at hκ
    split at hκ
    · cases hκ
    · rename_i hk hs hn _
      simp only [Descent.opKind, hk, hs, hn] at hkind
      exact hkind.imp_right FreeTmpl.read
    · rename_i hk hs
      simp only [Descent.opKind, hk, hs] at hkind
      exact hkind.imp_right FreeTmpl.store
    · cases hκ
  all_goals
    exfalso
    simp only [Ref.opKind] at hκ
    first
      | (cases hκ <;> cases hf)
      | (split at hκ <;> cases hκ <;> cases hf)

variable {X : Execution}

/-- **`Premises2.freeTmpl`**: the template a state of class `free` reaches is undefined
behaviour or a free template. -/
theorem prem_freeTmpl (hsound : (Thread.code L g).Sound) {d : Thread.D} {m : Tmpl}
    (hc : cls g d = .free) (hat : (Thread.code L g).AtD d t) (hinv : (Thread.code L g).inv d)
    (hout : out kernel Assumptions.all L g t = .ev m) : (∃ f, m = .ub f) ∨ FreeTmpl m := by
  have ho := Code.site_out hsound (d := d) (t := t) ⟨hat, hinv⟩
  rw [hout] at ho
  have hm : m = (Thread.code L g).tmpl (some d) t := by injection ho
  subst hm
  simp only [Code.tmpl]
  cases hi : kernel.code[d.site.pc]? with
  | none => exact .inl ⟨_, rfl⟩
  | some ins =>
    have hκ := Ref.site_op d.site hi
    have hsub : t.sub = d.site.sub := hat.2.1
    rw [← hsub] at hκ
    exact tmpl_free hκ (by rw [← siteCls_kind]; exact hc)

end

end PTX.Kernels.FlashKdaFwd.Proof.Progress
