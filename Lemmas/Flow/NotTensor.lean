-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotWait
public import Lemmas.Flow.Polls
public import Lemmas.Flow.Events
public import Lemmas.Isa.Tmpl

@[expose] public section

/-! # Tensor copies

A proof tool. Only a tensor copy into shared memory fires a tensor issue; protocol proofs
counting a thread's tensor copies completing on a barrier use this to skip every other
event. -/

namespace PTX.Flow
open PTX

noncomputable section

/-- Whether event `e` is a tensor issue whose completion barrier is `m`. -/
def issuesTo (m : Loc) (e : Event) : Bool := match e.kind with
  | .tensorIssue _ s => decide (s.mbar = m)
  | _ => false

theorem issuesTo_tensorIssue {m : Loc} {pc a : Nat} {s : TensorCopy.Spec} :
    issuesTo m ⟨pc, .tensorIssue a s⟩ = decide (s.mbar = m) := rfl

/-- An event that is not a tensor issue is not a tensor issue on any barrier. -/
theorem issuesTo_notTensor {m : Loc} {e : Event}
    (h : ∀ (a : Nat) (s : TensorCopy.Spec), e.kind ≠ .tensorIssue a s) :
    issuesTo m e = false := by
  unfold issuesTo
  split
  · rename_i a s heq; exact absurd heq (h a s)
  · rfl

theorem issues_snoc (m : Loc) (es : List Event) (e : Event) :
    (es ++ [e]).countP (issuesTo m) = es.countP (issuesTo m) + if issuesTo m e then 1 else 0 := by
  simp only [List.countP_append, List.countP_singleton]

/-- A unicast tensor load that issues fires one tensor issue whose completion barrier is the
mbarrier its operand resolves to in the cluster. -/
theorem fires_cpTensor_mbar {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {grp : Bool} {dst mb : Nat} {off moff : Int} {map : Opnd} {cs : List Opnd} {lm : TensorMode}
    {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.cpTensor true grp dst off map cs mb moff none lm)) e
      (some u)) :
    ∃ a s, e = ⟨pc, .tensorIssue a s⟩ ∧ mbarClusterLoc L g t mb moff = .ok s.mbar := by
  have hf' : Fires pc (tensorTmpl L g t (.cpTensor true grp dst off map cs mb moff none lm)) e
      (some u) := hf
  rcases tensorTmpl_cpTensor_unicast (L := L) (g := g) (t := t) (ca := true) (grp := grp)
    (dst := dst) (mb := mb) (off := off) (moff := moff) (map := map) (cs := cs) (lm := lm) with
    ⟨f, hT⟩ | ⟨a, s, hT⟩
  · rw [hT] at hf'
    simp [Fires] at hf'
  · rw [hT] at hf'
    obtain ⟨rfl, -⟩ := hf'
    obtain ⟨hcopy, -⟩ := tensorTmpl_unicast_issue hT
    have := tensorLoadCopy_ok hcopy
    exact ⟨a, s, rfl, by simpa using this.2.1⟩

/-- A unicast tensor copy through a cluster address reads its descriptor from the map at the
address its map operand evaluates to. -/
theorem fires_cpTensor_desc {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {grp : Bool} {dst mb : Nat} {off moff : Int} {map : Opnd} {cs : List Opnd} {lm : TensorMode}
    {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.cpTensor true grp dst off map cs mb moff none lm)) e
      (some u)) :
    ∀ a s, e.kind = .tensorIssue a s → tensorMapAddress L g t map = .ok a ∧
      ∃ d, L.tensorMaps a = some ⟨s.outer, d⟩ ∧ s.descriptor = lm.transfer d := by
  intro a s hk
  have hf' : Fires pc (tensorTmpl L g t (.cpTensor true grp dst off map cs mb moff none lm)) e
      (some u) := hf
  rcases tensorTmpl_cpTensor_unicast (L := L) (g := g) (t := t) (ca := true) (grp := grp)
    (dst := dst) (mb := mb) (off := off) (moff := moff) (map := map) (cs := cs) (lm := lm) with
    ⟨f, hT⟩ | ⟨a', s', hT⟩
  · rw [hT] at hf'
    simp [Fires] at hf'
  · rw [hT] at hf'
    obtain ⟨rfl, -⟩ := hf'
    cases hk
    obtain ⟨hcopy, -⟩ := tensorTmpl_unicast_issue hT
    obtain ⟨hma, -, d, hd, -, hdesc, -⟩ := tensorLoadCopy_ok hcopy
    exact ⟨hma, d, hd, hdesc⟩

/-- A template that issues no tensor copy. -/
def NotTensor : Tmpl → Prop
  | .tensorIssue .. => False
  | _ => True

/-- Whether an instruction is a tensor copy into shared memory. -/
def tensorOp : Op → Bool
  | .cpTensor .. => true
  | _ => false

theorem widen_notTensor {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotTensor m) :
    NotTensor (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notTensor {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotTensor r) :
    NotTensor (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- The event of a local rule of an integer, move or conversion instruction copies no tensor. -/
theorem localSregTmpl_notTensor {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotTensor (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotTensor]

/-- The template of an instruction's rule, or its `noRule` fault, copies no tensor. -/
theorem ruleTmpl_notTensor {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op} :
    NotTensor (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notTensor
  · simp only [NotTensor]

/-- An `if` of two templates that copy no tensor copies none. -/
theorem ite_notTensor {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotTensor a)
    (hb : NotTensor b) : NotTensor (if c then a else b) := by
  split <;> assumption

/-- A template that is a `ub` fault on a failed execution and `ok` on a successful one copies no
    tensor when both do not. -/
theorem exec_notTensor {α : Type} {r : Exec α} {ub : Fault → Tmpl} {ok : α → Tmpl}
    (hub : ∀ f, NotTensor (ub f)) (hok : ∀ a, NotTensor (ok a)) :
    NotTensor (match r with | .error f => ub f | .ok a => ok a) := by
  cases r with
  | error f => exact hub f
  | ok a => exact hok a

/-- An instruction that is not a tensor copy fires no tensor issue. -/
theorem eventTmpl_notTensor {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : tensorOp op = false) : NotTensor (eventTmpl A L g t op) := by
  cases op <;> simp only [tensorOp] at hop
  case int i => exact ruleTmpl_notTensor (op := .int i)
  case move m => exact ruleTmpl_notTensor (op := .move m)
  case cvt c => exact ruleTmpl_notTensor (op := .cvt c)
  case mem a =>
    have hm := memTmpl_isMem (A := A) (L := L) (g := g) (t := t) (a := a)
    simp only [eventTmpl]
    generalize memTmpl A L g t a = m at hm ⊢
    cases m <;> trivial
  case warp w =>
    have hm := warpTmpl_isWarp (L := L) (g := g) (t := t) (w := w)
    simp only [eventTmpl]
    generalize warpTmpl L g t w = m at hm ⊢
    cases m <;> trivial
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notTensor
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notTensor)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notTensor)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notTensor)
         | split)
    | trivial

theorem fires_notTensor {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState} (hm : NotTensor m)
    (hf : Fires pc m e o) : ∀ (a : Nat) (s : TensorCopy.Spec), e.kind ≠ .tensorIssue a s := by
  intro a s he
  cases m <;> simp only [NotTensor] at hm <;> simp only [Fires] at hf <;> aesop

theorem fires_none_notTensor {pc : Nat} {m : Tmpl} {e : Event} (hf : Fires pc m e none) :
    ∀ (a : Nat) (s : TensorCopy.Spec), e.kind ≠ .tensorIssue a s := by
  intro a s he
  cases m <;> simp only [Fires] at hf <;> aesop

end
end PTX.Flow
