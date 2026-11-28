-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.FloatRules
public import Lemmas.Flow.OutLit
public import Lemmas.Flow.OutFloatItems
public import Lemmas.Flow.MaxSwap
import Kernels.InklingRelDecode.Proof.Lib.Segments

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

/-- The scale word `%r498 = %r525 * log2(e)` of pc 601. -/
def scaleItem : XItem :=
  .fn (fOp (mulI false) 498 [.reg 525, .f32imm 1069066811]) 498
    (regsOf [.reg 525, .f32imm 1069066811]) (fF (mulL false) [.reg 525, .f32imm 1069066811])

/-- The maximum of the running maximum and the row's two halves (pc 1839). -/
def maxItem : XItem := .fn (maxOp 1522 [1914,1520,1521]) 1522 [1914,1520,1521] maxE

/-- The rescale factor (pcs 1840 to 1846): `%r507`, with the test `%p168` and the new maximum
`%r1522` that the loop-carried maximum `%r1914` takes at pc 949. -/
def alphaRest : List XItem :=
  [.base (.setp (.ord .eq) false 167 1522 4286578688),
   .base (.selp 1523 (.f32imm 0) (.reg 1522) 167),
   .base (.sub false 1524 1914 1523),
   .base (.mul false 1270 498 1524),
   .base (.setp (.ord .ge) false 168 1270 3238002688),
   .base (.ex2 true 1269 1270),
   .base (.selp 507 (.f32imm 1065353216) (.reg 1269) 168)]

def alphaItems : List XItem := maxItem :: alphaRest

/-- The update of the running maximum (pc 949). -/
def updItem : OItem := .selp 1914 (.reg 1914) (.reg 1522) 168

def scaleWord (s : Value) : Value := xFinal (fun _ => s) [scaleItem] 498

/-- The value of `%r1522` after the maximum of the carried maximum, the row's own and the
partner half's maximum. -/
def mxWord (m a b : Value) : Value :=
  xFinal (fun r => if r = 1914 then m else if r = 1520 then a else b) [maxItem] 1522

/-- The registers the rescale factor's run reads, as a value function. -/
def alphaIn (c m mx : Value) (r : Nat) : Value :=
  if r = 1914 then m else if r = 498 then c else if r = 1522 then mx else b32 0

def alphaVal (c m mx : Value) : Nat → Value := xFinal (alphaIn c m mx) alphaRest

/-- The running maximum after the round. -/
def mNext (c m mx : Value) : Value := oFinal (alphaVal c m mx) [updItem] 1914

/-- The row sum of a round (register 1531, pc 2235): the lane's sum and its partner's. -/
def psWord (s r : Value) : Value := okVal (b32 0) (floatE (addI false) [s, r])

/-- The running sum after a round (pc 950): the old sum, the factor and the round's row sum. -/
def lStep (l f ps : Value) : Value := okVal (b32 0) (floatE (fmaI .rn false) [l, f, ps])

/-- The maximum of the carried maximum and the two halves does not depend on their order. -/
theorem mxWord_swap (m a b : Value) : mxWord m a b = mxWord m b a := by
  have h := (maxE_swap m a b).okVal (.bits 32 0)
  simp only [mxWord, maxItem, xFinal, XItem.upd, XItem.vals, List.foldl_cons, List.foldl_nil,
    Function.update_self, List.map_cons, List.map_nil, ite_true,
    show (1520 = 1914) = False by decide, show (1521 = 1914) = False by decide,
    show (1521 = 1520) = False by decide, ite_false]
  exact h

/-- A register no item of a run writes keeps its value. -/
theorem xFinal_other {V : Nat → Value} {r : Nat} : ∀ {items : List XItem},
    r ∉ xWrites items → xFinal V items r = V r
  | [], _ => rfl
  | it :: its, h => by
    simp only [xWrites, List.flatMap_cons, List.mem_append, not_or] at h
    obtain ⟨h1,h2⟩ := h
    have : it.upd V r = V r := by
      unfold XItem.upd
      rw [← XItem.vals_keys V it] at h1
      generalize it.vals V = l at h1
      clear h2
      induction l generalizing V with
      | nil => rfl
      | cons p l ih =>
        simp only [List.map_cons, List.mem_cons, not_or] at h1
        simp only [List.foldl_cons]
        rw [ih h1.2, Function.update_of_ne h1.1]
    rw [xFinal, xFinal_other h2, this]

/-- The values an item writes depend only on the registers it reads. -/
theorem vals_congr {V W : Nat → Value} {it : XItem} (h : ∀ r ∈ it.reads, V r = W r) :
    it.vals V = it.vals W := by
  cases it with
  | base it =>
    cases it <;> simp only [XItem.vals, OItem.vals, XItem.reads, OItem.reads, opndRegs] at h ⊢
    all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at h
    all_goals try simp [h]
    rename_i d a b p
    cases a <;> cases b <;> simp_all [opndVal]
  | fn op d srcs f =>
    have : srcs.map V = srcs.map W := List.map_congr_left h
    simp only [XItem.vals, this]

private theorem foldl_update_eq (l : List (Nat × Value)) :
    ∀ {V W : Nat → Value} {r : Nat}, (r ∈ l.map Prod.fst ∨ V r = W r) →
      l.foldl (fun V p => Function.update V p.1 p.2) V r =
        l.foldl (fun V p => Function.update V p.1 p.2) W r := by
  induction l with
  | nil => intro V W r h; simpa using h
  | cons p l ih =>
    intro V W r h
    simp only [List.foldl_cons]
    apply ih
    by_cases hr : r = p.1
    · right; subst hr; simp
    · rcases h with h | h
      · left; simpa [hr] using h
      · right; simp [Function.update_of_ne hr, h]

/-- A run's values depend only on the registers it reads before writing them. -/
theorem xFinal_congr {S : List Nat} : ∀ {items : List XItem} {V W : Nat → Value},
    xReadsB S items = true → (∀ r ∈ S, V r = W r) →
      ∀ r, (r ∈ xWrites items ∨ r ∈ S) → xFinal V items r = xFinal W items r
  | [], _, _, _, h, r, hr => by simpa [xWrites, xFinal] using h r (by simpa [xWrites] using hr)
  | it :: its, V, W, hb, h, r, hr => by
    simp only [xReadsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hb
    have hv : it.vals V = it.vals W := vals_congr fun x hx => h x (hb.1 x hx)
    refine xFinal_congr (S := it.writes ++ S) hb.2 ?_ r ?_
    · intro x hx
      unfold XItem.upd
      rw [hv]
      apply foldl_update_eq
      rcases List.mem_append.mp hx with hx | hx
      · left; rwa [XItem.vals_keys]
      · right; exact h x hx
    · simp only [xWrites, List.flatMap_cons, List.mem_append] at hr ⊢
      tauto

end

end PTX.Kernels.InklingRelDecode.Proof.Lib
