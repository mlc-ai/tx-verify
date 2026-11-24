-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueInitGroup
public import Kernels.TmlFa4Fwd.Proof.PrologueFenceProgress
public import Lemmas.Kernel.NextReads

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem initStartupPc (i : Fin 34) : StartupPc (initSite i).pc := by
  fin_cases i <;> decide

/-- An initializer with the decoded shared address and arrival count can issue in an unfinished
trace, using the mbarrier history extension. This applies to every initializer of the prologue. -/
theorem initializerCanIssue {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (i : Fin 34) {g : Nat} (hg : g < l.threads)
    (hNonempty : X.tr g ≠ []) (hReleased : Step.Released l X g)
    {u t : TState} (hrun : Run kernel Assumptions.all l g {} (X.tr g) (some u))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) u t)
    (hPc : t.pc = (initSite i).pc) (hFault : t.fault = none)
    (hAddr : t.regs (initSite i).baseReg = some (b32 (l.sharedBase + (initSite i).baseOffset)))
    (hCount : t.regs (initSite i).countReg = some (b32 (initSite i).count)) :
    ∃ Y, Consistent l kernel Assumptions.all m Y ∧ X.le Y ∧ X.size l < Y.size l := by
  let mb : Loc := ⟨.shared, g / l.block, l.sharedBase + (initSite i).baseOffset +
    (initSite i).displacement⟩
  let c := (initSite i).count
  have hOut : out kernel Assumptions.all l g t = .ev (.mbInit mb c (next t)) :=
    startupOut (hPc ▸ initStartupPc i) (initOut hp i g t hPc hFault hAddr hCount)
  let e : Event := ⟨(initSite i).pc,.mbInit mb c⟩
  have hStep : EStep kernel Assumptions.all l g t e (some (next t)) :=
    ⟨_,hOut,by simp [e,hPc],rfl⟩
  have hAction (loc : Loc) : AsyncCopy.objectAction (X.snoc g e (fun _ => none)) X.async loc
      (.thread (g,(X.tr g).length)) = if loc = mb then some (.init c) else none := by
    by_cases hl : loc = mb
    · subst loc
      simp [AsyncCopy.objectAction,snoc_get_new,e]
    · simp [AsyncCopy.objectAction,snoc_get_new,e,hl,Ne.symm hl]
  refine Step.object_counted_extension_silent (e := e) hX trivial hg (.inl hNonempty) hReleased
    hrun hLocal hStep ⟨trivial,by intro _ h; cases h⟩ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    (act := .init c) ?_ hAction
    (fun rec => Assumptions.wfStep.quiet hX
      (Execution.le_trans le_snoc (Execution.le_appendObject _ _ _)) rfl
          ((Execution.noNewRead_snoc (r := fun _ => none) rfl).trans
            (Execution.noNewRead_of_tr rfl)))
  all_goals intros; simp [e,Kind.Quiet] at *

/-- An actual execution prefix and its remaining events, separated by a local path. -/
structure InitCursor (l : Launch) (X : Execution) (g n : Nat) (t : TState) : Prop where
  length : n ≤ (X.tr g).length
  present : ∃ u, Run kernel Assumptions.all l g {} ((X.tr g).take n) (some u) ∧
    Relation.ReflTransGen (Tau kernel Assumptions.all l g) u t ∧
    ∃ o, Run kernel Assumptions.all l g u ((X.tr g).drop n) o

theorem InitCursor.localStep {l : Launch} {X : Execution} {g n : Nat} {t u : TState}
    (h : InitCursor l X g n t) (hu : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) :
    InitCursor l X g n u := by
  obtain ⟨hl, s, hp, ht, o, hr⟩ := h
  exact ⟨hl, s, hp, ht.trans hu, o, hr⟩

/-- If the next trace position exists, it is the decoded initializer and advances its cursor. -/
theorem initializerAtCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (i : Fin 34) {g n : Nat} {t : TState}
    (hCur : InitCursor l X g n t) (hLt : n < (X.tr g).length)
    (hPc : t.pc = (initSite i).pc) (hFault : t.fault = none)
    (hAddr : t.regs (initSite i).baseReg = some (b32 (l.sharedBase + (initSite i).baseOffset)))
    (hCount : t.regs (initSite i).countReg = some (b32 (initSite i).count)) :
    X.get (g, n) = some (initEvent l g i) ∧ InitCursor l X g (n + 1) (next t) := by
  obtain ⟨_, u, hRun, hLocal, o, hRest⟩ := hCur
  have hSplit := List.drop_eq_getElem_cons hLt
  rw [hSplit] at hRest
  let mb : Loc := ⟨.shared, g / l.block, l.sharedBase + (initSite i).baseOffset +
    (initSite i).displacement⟩
  have hOut : out kernel Assumptions.all l g t =
      .ev (.mbInit mb (initSite i).count (next t)) :=
    startupOut (hPc ▸ initStartupPc i) (initOut hp i g t hPc hFault hAddr hCount)
  have hNext : Next kernel Assumptions.all l g u t (.mbInit mb (initSite i).count (next t)) :=
    ⟨hLocal, hOut⟩
  obtain ⟨v, ⟨he, hv⟩, hTail⟩ := hNext.continuing_event (by rintro ⟨_, h⟩; cases h) hRest
  obtain rfl := Option.some.inj hv
  have he' : (X.tr g)[n] = initEvent l g i := by rw [he, hPc]; rfl
  have hTake : (X.tr g).take (n + 1) = (X.tr g).take n ++ [(X.tr g)[n]] :=
    List.take_succ_eq_append_getElem hLt
  refine ⟨?_, Nat.succ_le_of_lt hLt, next t, ?_, .refl, o, hTail⟩
  · change (X.tr g)[n]? = _
    rw [List.getElem?_eq_getElem hLt, he']
  · rw [hTake]
    exact hRun.snoc hLocal ⟨_, hOut, he, rfl⟩

/-- The next decoded initializer appears in every maximal execution reaching it. -/
theorem initializerProgress {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (i : Fin 34) {g n : Nat} (hg : g < l.threads) (hn : 0 < n)
    {t : TState} (hCur : InitCursor l X g n t)
    (hReady : n = (X.tr g).length → Step.Released l X g)
    (hPc : t.pc = (initSite i).pc) (hFault : t.fault = none)
    (hAddr : t.regs (initSite i).baseReg = some (b32 (l.sharedBase + (initSite i).baseOffset)))
    (hCount : t.regs (initSite i).countReg = some (b32 (initSite i).count)) :
    X.get (g, n) = some (initEvent l g i) ∧ InitCursor l X g (n + 1) (next t) := by
  have hLt : n < (X.tr g).length := by
    by_contra hShort
    obtain ⟨hLen, u, hRun, hLocal, _, _⟩ := hCur
    have hEq : n = (X.tr g).length := by omega
    rw [List.take_of_length_le hEq.ge] at hRun
    apply hMax.not_grows
    apply initializerCanIssue hp hMax.1 i hg ?_ (hReady hEq)
      hRun hLocal hPc hFault hAddr hCount
    intro hNil
    rw [hNil, List.length_nil] at hEq
    omega

  exact initializerAtCursor hp i hCur hLt hPc hFault hAddr hCount

end
end PTX.Kernels.TmlFa4Fwd.Prologue
