-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc

@[expose] public section

/-! # The paired Tensor Memory instructions and their events

A proof tool. A paired Tensor Memory event (`tcgen05.alloc`, `relinquish_alloc_permit`,
`dealloc`) is fired only by one of those three instructions (`fires_resource_op`). Before the
allocation's address store, such an instruction's template is undefined behaviour or the request
(`TmemTmpl`); the request names the instruction's group and, for the allocation and the
deallocation, the column count its operand register holds. -/

namespace PTX.Flow

/-- A template that fires no paired Tensor Memory operation. -/
def NotResource : Tmpl → Prop
  | .tc (.resource ..) _ => False
  | _ => True

theorem widen_notResource {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotResource m) :
    NotResource (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notResource {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotResource r) :
    NotResource (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is a paired Tensor Memory instruction. -/
def tmemOp : Op → Bool
  | .tcAlloc .. | .tcDealloc .. | .tcRelinquish .. => true
  | _ => false

/-- The event of a local rule of an integer, move or conversion instruction fires no such
event. -/
theorem localSregTmpl_notResource {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotResource (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotResource]

/-- The template of an instruction's rule, or its `noRule` fault, fires no such event. -/
theorem ruleTmpl_notResource {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} : NotResource (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notResource
  · simp only [NotResource]

/-- An `if` of two templates that fire no such event fires none. -/
theorem ite_notResource {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotResource a)
    (hb : NotResource b) : NotResource (if c then a else b) := by
  split <;> assumption

/-- An instruction other than a paired Tensor Memory instruction fires no such operation. -/
theorem eventTmpl_notResource {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} (hop : tmemOp op = false) : NotResource (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_notResource (op := .int i)
  case move m => exact ruleTmpl_notResource (op := .move m)
  case cvt c => exact ruleTmpl_notResource (op := .cvt c)
  all_goals simp only [tmemOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notResource
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notResource)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, tensorStoreTmpl,
        reduxTmpl, matchTmpl, activemaskTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, tensorTmpl, tensorMulticast]
       repeat' first
         | trivial
         | (apply ofExec_notResource)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notResource)
         | split)
    | trivial

/-- A paired Tensor Memory operation is fired by a paired Tensor Memory instruction. -/
theorem fires_resource_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {group : CtaGroup} {dst : Option Loc} {act : Tmem.Request}
    (hk : e.kind = .tc (.resource group dst act)) : tmemOp op = true := by
  cases hq : tmemOp op
  · exfalso
    have hm := eventTmpl_notResource (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotResource] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

/-- The template of a paired Tensor Memory instruction of group `group` before the allocation's
address store: undefined behaviour or the request. -/
def TmemTmpl (group : CtaGroup) : Tmpl → Prop
  | .ub _ => True
  | .tc (.resource grp _ _) _ => grp = group
  | _ => False

theorem ofExec_tmemTmpl {group : CtaGroup} {r : Exec Tmpl}
    (h : PTX.EventFrame.AllOk (TmemTmpl group) r) : TmemTmpl group (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- The allocation's template before its address store. -/
theorem tmemTmpl_alloc {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {group : CtaGroup} {base : Nat} {off : Int} {nc : Opnd} (hs : t.sub = 0) :
    TmemTmpl group (eventTmpl A L g t (.tcAlloc group base off nc)) := by
  simp only [eventTmpl, tcTmpl, hs]
  apply ofExec_tmemTmpl
  repeat' first
    | (apply PTX.EventFrame.allOk_bind; intro _)
    | contradiction
    | split
    | exact rfl

/-- The deallocation's template. -/
theorem tmemTmpl_dealloc {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {group : CtaGroup} {ta nc : Opnd} :
    TmemTmpl group (eventTmpl A L g t (.tcDealloc group ta nc)) := by
  simp only [eventTmpl, tcTmpl]
  apply ofExec_tmemTmpl
  repeat' first
    | (apply PTX.EventFrame.allOk_bind; intro _)
    | split
    | exact rfl

/-- The permit relinquishment's template. -/
theorem tmemTmpl_relinquish {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {group : CtaGroup} : TmemTmpl group (eventTmpl A L g t (.tcRelinquish group)) := by
  simp only [eventTmpl, tcTmpl]
  apply ofExec_tmemTmpl
  repeat' first
    | (apply PTX.EventFrame.allOk_bind; intro _)
    | split
    | exact rfl

/-- An event of a paired Tensor Memory template is its undefined behaviour or its operation. -/
theorem fires_tmemTmpl {group : CtaGroup} {m : Tmpl} (hm : TmemTmpl group m) {pc : Nat}
    {e : Event} {o : Option TState} (hf : Fires pc m e o) :
    (∃ f, e = ⟨pc, .ub f⟩) ∨ ∃ dst act, e = ⟨pc, .tc (.resource group dst act)⟩ := by
  cases m <;> simp only [TmemTmpl] at hm
  · simp only [Fires] at hf
    exact .inl ⟨_, hf.1⟩
  · rename_i k u
    cases k <;> simp only at hm
    simp only [Fires] at hf
    subst hm
    exact .inr ⟨_, _, hf.1⟩

/-- The allocation's request is fired before its address store, with the column count its
operand holds. -/
theorem fires_tcAlloc_resource {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {group : CtaGroup} {base : Nat} {off : Int} {nc : Opnd} {pc : Nat} {e : Event}
    {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.tcAlloc group base off nc)) e o)
    {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request}
    (hk : e.kind = .tc (.resource grp dst act)) :
    t.sub = 0 ∧ grp = group ∧ ∃ n, readBits L g t 32 nc = .ok n ∧ act = .alloc n.toNat := by
  simp only [eventTmpl, tcTmpl] at hf
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  cases hd : effAddr L g t .shared base off with
  | error f =>
    simp [ofExec, hd, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Fires] at hf
    split_ifs at hf <;> simp at hf
  | ok d =>
  cases hn : readBits L g t 32 nc with
  | error f =>
    simp [ofExec, hd, hn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Fires] at hf
    split_ifs at hf <;> simp at hf
  | ok n =>
    simp only [hd, hn, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf
    split_ifs at hf
    all_goals simp only [ofExec, Fires] at hf
    all_goals first
      | (simp at hf; done)
      | (obtain ⟨he, -⟩ := hf
         simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at he
         obtain ⟨-, rfl, -, rfl⟩ := he
         exact ⟨‹t.sub = 0›, rfl, n, rfl, rfl⟩)

/-- The deallocation's operation names the column count its operand holds. -/
theorem fires_tcDealloc_resource {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {group : CtaGroup} {ta nc : Opnd} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.tcDealloc group ta nc)) e o)
    {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request}
    (hk : e.kind = .tc (.resource grp dst act)) :
    grp = group ∧ dst = none ∧ ∃ n a, readBits L g t 32 nc = .ok n ∧ act = .dealloc a n.toNat := by
  simp only [eventTmpl, tcTmpl] at hf
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  cases ha : readBits L g t 32 ta with
  | error f =>
    simp [ofExec, ha, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Fires] at hf
    split_ifs at hf <;> simp at hf
  | ok a =>
  cases hn : readBits L g t 32 nc with
  | error f =>
    simp [ofExec, ha, hn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Fires] at hf
    split_ifs at hf <;> simp at hf
  | ok n =>
    simp only [ha, hn, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf
    split_ifs at hf
    all_goals simp only [ofExec, Fires] at hf
    all_goals first
      | (simp at hf; done)
      | (simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hf
         obtain ⟨⟨-, rfl, rfl, rfl⟩, -⟩ := hf
         exact ⟨rfl, rfl, n, _, rfl, rfl⟩)

/-- The permit relinquishment's operation. -/
theorem fires_tcRelinquish_resource {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {group : CtaGroup} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.tcRelinquish group)) e o)
    {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request}
    (hk : e.kind = .tc (.resource grp dst act)) :
    grp = group ∧ dst = none ∧ act = .relinquish := by
  simp only [eventTmpl, tcTmpl] at hf
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  split_ifs at hf
  all_goals simp [ofExec, Fires, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hf
  exact hf.1.2

end PTX.Flow
