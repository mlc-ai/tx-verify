-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.TraceProjection
public import Core.Assembly.Execution
public import Lemmas.Order.Order
public import Lemmas.Execution.NoAsync
public import Lemmas.Cluster.ClusterBarrierExecution

@[expose] public section

section
namespace PTX.Proof
open PTX

namespace EventShape

theorem isBar {e f : Event} (h : EventShape e f) : Execution.isBar e = Execution.isBar f := by
  cases h <;> rfl

theorem isShfl {e f : Event} (h : EventShape e f) : Execution.isShfl e = Execution.isShfl f := by
  cases h <;> rfl

end EventShape

namespace ShapePrefix

theorem length_le {a b : List Event} (h : ShapePrefix a b) : a.length ≤ b.length + 1 := by
  induction h with
  | nil => simp
  | fault => simp
  | cons h ht ih => simp only [List.length_cons]; omega

theorem get {a b : List Event} (h : ShapePrefix a b) {n : Nat} {e : Event}
    (he : a[n]? = some e) (hn : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    ∃ e', b[n]? = some e' ∧ EventShape e e' := by
  induction h generalizing n with
  | nil => simp at he
  | fault pc f l =>
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he; subst e;
        exact (hn pc f rfl).elim
    | succ n => simp at he
  | @cons e0 f0 a b hs ht ih =>
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he; subst e;
        exact ⟨f0, rfl, hs⟩
    | succ n => exact ih he


theorem count_before {a b : List Event} (h : ShapePrefix a b) {n : Nat} {e e' : Event}
    (he : a[n]? = some e) (hf : b[n]? = some e') (_hs : EventShape e e')
    (p : Event → Bool) (hp : ∀ x y, EventShape x y → p x = p y) :
    (a.take n).countP p = (b.take n).countP p := by
  induction h generalizing n with
  | nil => simp at he
  | fault pc f l =>
    cases n with
    | zero => rfl
    | succ n => simp at he
  | @cons e0 f0 a b h ht ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [List.take_succ_cons, List.countP_cons, hp _ _ h, ih he hf]

end ShapePrefix

end PTX.Proof
end

section
namespace PTX.Proof
open PTX

private theorem count_index_unique {α : Type} (p : α → Bool) {l : List α}
    {i j : Nat} {e f : α} (he : l[i]? = some e) (hf : l[j]? = some f)
    (hpe : p e = true) (hpf : p f = true)
    (hc : (l.take i).countP p = (l.take j).countP p) : i = j := by
  induction l generalizing i j with
  | nil => simp at he
  | cons a l ih =>
    cases i <;> cases j
    · rfl
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst a
      simp [hpe] at hc
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst a
      simp [hpf] at hc
    · simp only [List.take_succ_cons, List.countP_cons] at hc
      have hc' : (l.take _).countP p = (l.take _).countP p := Nat.add_right_cancel hc
      exact congrArg Nat.succ (ih he hf hc')

theorem shfl_index_unique {X : Execution} {g i j k : Nat}
    (hi : X.ShflK (g, i) k) (hj : X.ShflK (g, j) k) : i = j := by
  obtain ⟨⟨pci, mi, ai, bi, ci, vi, oi, hi⟩, hc⟩ := hi
  obtain ⟨⟨pcj, mj, aj, bj, cj, vj, oj, hj⟩, hd⟩ := hj
  exact count_index_unique Execution.isShfl hi hj rfl rfl (hc.trans hd.symm)

variable {L : Launch} {X Y : Execution}

def ShapeExecution (L : Launch) (X Y : Execution) : Prop :=
  ∀ g < L.threads, ShapePrefix (X.tr g) (Y.tr g)

theorem ShapeExecution.bar (h : ShapeExecution L X Y) {e : EvId} {k : Nat}
    (hg : e.1 < L.threads) (hb : X.BarK e k) : Y.BarK e k := by
  obtain ⟨⟨id, pc, he⟩, hc⟩ := hb
  obtain ⟨f, hf, hs⟩ := (h e.1 hg).get he (by intros; intro eq; cases eq)
  cases hs
  exact ⟨⟨id, pc, hf⟩, ((h e.1 hg).count_before he hf (.bar ..)
    Execution.isBar (fun _ _ h => h.isBar)).symm.trans hc⟩

theorem ShapeExecution.shfl (h : ShapeExecution L X Y) {e : EvId} {k : Nat}
    (hg : e.1 < L.threads) (hb : X.ShflK e k) : Y.ShflK e k := by
  obtain ⟨⟨pc, m, a, b, c, v, ok, he⟩, hc⟩ := hb
  obtain ⟨f, hf, hs⟩ := (h e.1 hg).get he (by intros; intro eq; cases eq)
  cases hs
  exact ⟨⟨_, _, _, _, _, _, _, hf⟩, ((h e.1 hg).count_before he hf (.shfl ..)
    Execution.isShfl (fun _ _ h => h.isShfl)).symm.trans hc⟩


theorem ShapeExecution.acc (h : ShapeExecution L X Y) {e : EvId} (hg : e.1 < L.threads) {a : Acc}
    (he : (X.get e).bind Event.acc = some a) : (Y.get e).bind Event.acc = some a := by
  obtain ⟨ev, hev, hacc⟩ : ∃ ev, X.get e = some ev ∧ ev.acc = some a := by
    cases hx : X.get e <;> simp_all
  obtain ⟨f, hf, hs⟩ := (h e.1 hg).get hev (by rintro pc ff rfl; simp [Event.acc] at hacc)
  change Y.get e = some f at hf
  rw [hf]
  cases hs <;> simp_all [Event.acc]


theorem ShapeExecution.read (h : ShapeExecution L X Y) {e : EvId} {a : Acc}
    {bs : List (Option Byte)} (hg : e.1 < L.threads) (he : X.Reads e a bs) :
    ∃ cs, Y.Reads e a cs := by
  obtain ⟨pc, he⟩ := he
  obtain ⟨f, hf, hs⟩ := (h e.1 hg).get he (by intros; intro eq; cases eq)
  cases hs
  exact ⟨_, _, hf⟩

theorem ShapeExecution.write (h : ShapeExecution L X Y) {e : EvId} {a : Acc}
    {bs : List Byte} (hg : e.1 < L.threads) (he : X.Writes e a bs) :
    ∃ cs, Y.Writes e a cs := by
  obtain ⟨pc, he⟩ := he
  obtain ⟨f, hf, hs⟩ := (h e.1 hg).get he (by intros; intro eq; cases eq)
  cases hs
  exact ⟨_, _, hf⟩

theorem ShapeExecution.access (h : ShapeExecution L X Y) {e : EvId} {a : Acc}
    {w : Bool} (hg : e.1 < L.threads) (he : X.Access e a w) : Y.Access e a w := by
  rcases he with ⟨bs, he, rfl⟩ | ⟨bs, he, rfl⟩ | ⟨old, new, pc, he⟩
  · obtain ⟨cs, hc⟩ := h.read hg he
    exact hc.access
  · obtain ⟨cs, hc⟩ := h.write hg he
    exact hc.access
  · obtain ⟨f, _, hs⟩ := (h e.1 hg).get he (by intro p f eq; cases eq)
    cases hs

theorem event_thread_lt {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) {e : EvId} {ev : Event}
    (he : X.get e = some ev) : e.1 < L.threads := by
  by_contra hn
  unfold Execution.get at he
  rw [hX.outside e.1 (by omega)] at he
  simp at he

theorem access_thread_lt {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) {e : EvId} {a : Acc} {w : Bool}
    (he : X.Access e a w) : e.1 < L.threads := by
  rcases he with ⟨_, ⟨_, he⟩, _⟩ | ⟨_, ⟨_, he⟩, _⟩ | ⟨_, _, ⟨_, he⟩⟩
  all_goals exact event_thread_lt hX he

theorem ShapeExecution.conflict {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (h : ShapeExecution L X Y) (hX : Consistent L K A mem0 X)
    {e f : EvId} {a b : Acc} (hc : Conflict X e f a b) : Conflict Y e f a b := by
  obtain ⟨hne, we, wf, he, hf, hw, hov⟩ := hc
  exact ⟨hne, we, wf, h.access (access_thread_lt hX he) he,
    h.access (access_thread_lt hX hf) hf, hw, hov⟩

end PTX.Proof
end
