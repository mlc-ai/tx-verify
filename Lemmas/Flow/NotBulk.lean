-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc
public import Lemmas.Flow.CommitTarget
public import Lemmas.Flow.ElectMask
public import Lemmas.Execution.EventFrameSource

@[expose] public section

/-! # Asynchronous copies and invalidations come from their instructions

A proof tool. Only an asynchronous copy instruction (`cp.async.bulk`, `st.async`/`red.async` or
`cp.async`) fires a copy event (`fires_bulk_op`), and only an `mbarrier.inval` fires an
invalidation (`fires_mbInval_op`). Every event of a thread's
run is undefined behaviour or the event of the instruction at its position (`event_source`), so
a kernel without such instructions has no such event in any consistent execution
(`no_kind_of_code`). -/

namespace PTX.Flow

/-- A template that fires no asynchronous copy. -/
def NotBulk : Tmpl → Prop
  | .copy .. => False
  | _ => True

/-- A template that fires no invalidation. -/
def NotInval : Tmpl → Prop
  | .mbInval .. => False
  | _ => True

/-- Whether an instruction is an asynchronous copy. -/
def bulkOp : Op → Bool
  | .cpBulk .. | .asyncStore .. | .cpAsync .. => true
  | _ => false

/-- Whether an instruction is an invalidation. -/
def invalOp : Op → Bool
  | .mbarInval .. => true
  | _ => false

theorem widen_notBulk {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotBulk m) :
    NotBulk (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem widen_notInval {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotInval m) :
    NotInval (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notBulk {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotBulk r) :
    NotBulk (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

theorem ofExec_notInval {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotInval r) :
    NotInval (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- An instruction other than an asynchronous copy fires no copy. -/
theorem eventTmpl_notBulk {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : bulkOp op = false) : NotBulk (eventTmpl A L g t op) := by
  cases op <;> simp only [bulkOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notBulk
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notBulk)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite))
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notBulk)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- An instruction other than an invalidation fires no invalidation. -/
theorem eventTmpl_notInval {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : invalOp op = false) : NotInval (eventTmpl A L g t op) := by
  cases op <;> simp only [invalOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notInval
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notInval)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notInval)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A copy is fired by an asynchronous copy instruction. -/
theorem fires_bulk_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {s : AsyncCopy.Spec} (hk : e.kind = .copy s) : bulkOp op = true := by
  cases hq : bulkOp op
  · exfalso
    have hm := eventTmpl_notBulk (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotBulk] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

/-- An invalidation is fired by an invalidation instruction. -/
theorem fires_mbInval_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {m : Loc} (hk : e.kind = .mbInval m) : invalOp op = true := by
  cases hq : invalOp op
  · exfalso
    have hm := eventTmpl_notInval (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotInval] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

/-- A cancellation request is fired by a cancellation instruction. -/
theorem fires_clcIssue_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {sp : Clc.Spec} {tg : List Nat} (hk : e.kind = .clcIssue sp tg) : clcOp op = true := by
  cases hq : clcOp op
  · exfalso
    have hm := eventTmpl_notClc (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotClc] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

/-! ### Every event comes from its position's instruction -/

variable {K : Kernel} {A : List Assumption} {L : Launch}

/-- **An event of a thread's run** is undefined behaviour or the event of the instruction at its
position, from some thread state. -/
theorem event_source {g : Nat} {es : List Event} (hp : Produces K A L g es) {e : Event}
    (he : e ∈ es) :
    (∃ f, e.kind = .ub f) ∨
      ∃ t ins o, t.pc = e.pc ∧ K.code[e.pc]? = some ins ∧
        Fires e.pc (eventTmpl A L g t ins.op) e o := by
  obtain ⟨o, hr⟩ := hp
  obtain ⟨t, o', m, hm, hf⟩ := hr.estep he
  have hpc := PTX.EventFrame.fires_source_pc hf
  rcases out_ev hm with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · obtain ⟨rfl, -⟩ := hf
    exact .inl ⟨f, rfl⟩
  · exact .inr ⟨t, ins, o', hpc.symm, hpc ▸ hc, hpc ▸ hf⟩

/-- **An event of a consistent execution** is undefined behaviour or the event of the
instruction at its position, from some state of its thread. -/
theorem get_source {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X) {i : EvId}
    {e : Event} (he : X.get i = some e) :
    (∃ f, e.kind = .ub f) ∨
      ∃ t ins o, t.pc = e.pc ∧ K.code[e.pc]? = some ins ∧
        Fires e.pc (eventTmpl A L i.1 t ins.op) e o := by
  obtain ⟨g, k⟩ := i
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hg : g < L.threads := by
    by_contra hn
    rw [hX.outside g (by omega)] at hk
    simp at hk
  exact event_source (hX.thr g hg) (List.mem_of_getElem? he)

/-- **No event of a kind an instruction class alone fires**: when every instruction of that
class is absent from the code, no event of a consistent execution has a kind of it. -/
theorem no_kind_of_code {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X)
    (p : Op → Bool) (bad : Kind → Prop) (hub : ∀ f, ¬ bad (.ub f))
    (hfire : ∀ {g pc t op e o}, Fires pc (eventTmpl A L g t op) e o → bad e.kind → p op = true)
    (hK : K.code.all (fun ins => !p ins.op) = true) {i : EvId} {e : Event}
    (he : X.get i = some e) : ¬ bad e.kind := by
  intro hb
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · rw [hf] at hb
    exact hub f hb
  · have hp := hfire hf hb
    have hall := List.all_eq_true.mp hK ins (List.mem_of_getElem? hc)
    simp [hp] at hall

end PTX.Flow
