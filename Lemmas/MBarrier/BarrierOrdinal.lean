-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events
public import Core.Assembly.Safety

@[expose] public section

/-!
A trace-index query used by the old kernel proof adapters during migration. This
counts source barrier occurrences; it is not the semantics of a barrier instance.
Core synchronization, completion and blocking use CtaBarK and resource histories.
-/
namespace PTX
namespace Execution

variable (X : Execution)

/-- `e` is the `k`-th barrier arrival of its thread. -/
def BarK (e : EvId) (k : Nat) : Prop :=
  (∃ id pc, X.IsBarrier e id none pc) ∧ ((X.tr e.1).take e.2).countP isBar = k

theorem count_index_unique {α : Type} (p : α → Bool) {l : List α}
    {i j : Nat} {e f : α} (he : l[i]? = some e) (hf : l[j]? = some f)
    (hpe : p e = true) (hpf : p f = true)
    (hc : (l.take i).countP p = (l.take j).countP p) : i = j := by
  induction l generalizing i j with
  | nil => simp at he
  | cons a l ih =>
    cases i <;> cases j
    · rfl
    · simp only [List.getElem?_cons_zero,Option.some.injEq] at he
      subst a
      simp [hpe] at hc
    · simp only [List.getElem?_cons_zero,Option.some.injEq] at hf
      subst a
      simp [hpf] at hc
    · simp only [List.take_succ_cons,List.countP_cons] at hc
      exact congrArg Nat.succ (ih he hf (Nat.add_right_cancel hc))

theorem _root_.PTX.Kernel.isAlignedCtaBar_iff {K : Kernel} {ev : Event}
    (h : K.isAlignedCtaBar ev = true) :
    ∃ pc id mode, ev = ⟨pc, .bar id none mode⟩ ∧ K.alignedAt pc = true := by
  obtain ⟨pc, kd⟩ := ev
  cases kd <;> try (simp [Kernel.isAlignedCtaBar] at h; done)
  rename_i id count mode
  cases count <;> simp [Kernel.isAlignedCtaBar] at h
  exact ⟨pc, id, mode, rfl, h⟩

/-- When every barrier of the traces is an aligned whole-CTA `bar.sync`, the `isAlignedCtaBar`
count is the barrier count. -/
theorem countP_isAlignedCtaBar {K : Kernel} {l : List Event}
    (hall : ∀ ev ∈ l, ∀ id count,
      ev.kind = .bar id count → count = none ∧ K.alignedAt ev.pc = true)
    (hna : ∀ ev ∈ l, ∀ id count, ev.kind ≠ .bar id count .arrive) :
    l.countP K.isAlignedCtaBar = l.countP isBar := by
  apply List.countP_congr
  rintro ⟨pc, kd⟩ hm
  cases kd <;> simp [Kernel.isAlignedCtaBar, isBar]
  rename_i id count mode
  cases mode
  · obtain ⟨h1, h2⟩ := hall _ hm id count rfl
    subst h1
    simp [h2]
  · exact (hna _ hm id count rfl).elim

/-- A thread whose trace has its `k`-th barrier arrival at `j` did not exit having executed
at most `k` aligned whole-CTA barriers, when all its barriers are of that form. -/
theorem not_exitedShort_of_barK {K : Kernel} {f : EvId} {j k : Nat}
    (hall : ∀ g ev, ev ∈ X.tr g → ∀ id count, ev.kind = .bar id count →
      count = none ∧ K.alignedAt ev.pc = true)
    (hna : ∀ g ev, ev ∈ X.tr g → ∀ id count, ev.kind ≠ .bar id count .arrive)
    (hf : X.BarK (f.1, j) k) (hs : X.ExitedShort K.isAlignedCtaBar f k) : False := by
  obtain ⟨⟨id, pc, hj⟩, hc⟩ := hf
  have hget : (X.tr f.1)[j]? = some ⟨pc, .bar id none⟩ := hj
  have h1 := hs.2
  rw [countP_isAlignedCtaBar (hall f.1) (hna f.1)] at h1
  have h2 : ((X.tr f.1).take (j + 1)).countP isBar ≤ (X.tr f.1).countP isBar :=
    (List.take_sublist _ _).countP_le
  rw [List.take_add_one, hget, List.countP_append] at h2
  simp [isBar, hc] at h2
  omega

end Execution


end PTX
