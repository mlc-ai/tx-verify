-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.BlockSum.Proof.Values
public import Lemmas.Kernel.Descent
public import Lemmas.Execution.ExecutionGrowth

@[expose] public section

/-! # Every maximal execution is complete

Descent over the pending threads (`Descent.progress_of_threads`), ranked `1` once a thread has
arrived at the barrier and `0` before. A pending thread whose last event is not an unreleased
barrier arrival extends the execution (`Descent.plain_extends`). A thread blocked at the barrier
of CTA `c`:

* some thread of `c` has not arrived: it is pending, of rank `0`;
* some thread of `c` has passed its barrier: generation `0` is released, and so is the blocked
  thread's arrival (`key_of_released`), contrary to the premise;
* every thread of `c` has its arrival as its last event: the history's missing records are
  appended (`NamedBar.named_finish`), which releases the arrival, and the thread extends the
  extended execution. -/

namespace PTX.Kernels.BlockSum.Proof

open PTX PTX.Proof PTX.Flow CtaBarrier

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B : Nat} {x : Nat → ℝ} {mem0 : Mem0} {X : Execution}

/-- The rank of a thread: `1` once it has arrived at the barrier. -/
def rankOf (X : Execution) (g : Nat) : Nat := if 3 ≤ (X.tr g).length then 1 else 0

theorem not_canceled (hX : Consistent L kernel Prod mem0 X) {g : Nat} : ¬ ClcCanceled L X g := by
  rintro ⟨-, req, ho⟩
  obtain ⟨i, s, targets, -, ⟨pc, hi⟩, -⟩ := hX.clc.canceled_has_issue ho
  cases noTma_of_consistent noTma hX _ _ _ hi

theorem noShfl : kernel.NoShfl := rfl

theorem wf_all : ∀ a ∈ Prod, ∀ Y, a.wf L mem0 Y := by
  intro a ha Y
  obtain rfl := List.mem_singleton.mp ha
  trivial

theorem ext_wf (X : Execution) (g : Nat) : X.ExtWf Prod L mem0 g :=
  fun _ _ _ a ha => wf_all a ha _

theorem init_not_bar {g : Nat} : ∀ ins, kernel.code[(codes A B L g).pc (codes A B L g).init]? =
    some ins → ins.op.isBar = false := by
  intro ins hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
  rfl

/-- The last event of a thread, if a barrier arrival, is released. -/
abbrev LastReleased (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∀ id count pc, 0 < (X.tr g).length → X.IsBarrier (g, (X.tr g).length - 1) id count pc →
    ∃ key, CtaBarK L X (g, (X.tr g).length - 1) key ∧ CtaBarDone L X (g / L.block) key

/-- **The descent step of a pending thread.** -/
theorem noAtomic : kernel.NoAtomic := rfl

theorem thread_steps (hpre : Pre L A B x mem0) (hsafe : SafeGoal kernel Prod L mem0)
    (hT : ∀ X, Consistent L kernel Prod mem0 X → ThreadFacts A B L X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) :
    Descent.Steps L kernel Prod mem0 (Frame.Pending L) rankOf X g := by
  have hX := hmax.1
  have ht := hT X hX
  have hub : ¬ HasUb X := fun h => hsafe.2 X hX (.inl h)
  have hC : ∀ g < L.threads, (codes A B L g).Sound := fun _ hg => sound hpre hg
  have hB := hpre.block
  have hb : 0 < L.block := by omega
  have hg := hp.1
  by_cases hrel : LastReleased L X g
  · refine .inl (Descent.plain_extends noTma noShfl noAtomic hC hX ht.tracked hub hp init_not_bar
      (fun id count pc hbar => ?_) (ext_wf X g))
    have hl : 0 < (X.tr g).length := by
      have hlt := len_of_get hbar
      simp only at hlt
      omega
    obtain ⟨key, hk, hd⟩ := hrel id count pc hl hbar
    exact NamedBar.ready_of_released hX.ctaBar hbar hk hd
  simp only [LastReleased, not_forall, not_exists, not_and] at hrel
  obtain ⟨id, count, pc, hlen0, hbar, hnr⟩ := hrel
  obtain ⟨h2, rfl, rfl, -⟩ := bar_cases hpre hX ht hbar
  rw [h2] at hbar hnr
  have hl3 : (X.tr g).length = 3 := by omega
  set c := g / L.block with hc
  have hcg : c < L.grid := cta_lt hpre hg
  by_cases hlag : ∃ h, h / L.block = c ∧ h < L.threads ∧ (X.tr h).length < 3
  · obtain ⟨h, -, hh, hlh⟩ := hlag
    refine .inr ⟨X, h, hmax, ⟨hh, not_canceled hX, fun pcx hx => ?_⟩, ?_⟩
    · have he : X.get (h, (X.tr h).length - 1) = some ⟨pcx, .exit⟩ := by
        unfold Execution.get
        rw [← List.getLast?_eq_getElem?]
        exact hx
      have := exit_index hpre hX ht he
      omega
    · simp only [rankOf, hl3, le_refl, ↓reduceIte]
      rw [ite_eq_right (by omega)]
      omega
  push Not at hlag
  by_cases hpass : ∃ h, h / L.block = c ∧ h < L.threads ∧ 3 < (X.tr h).length
  · obtain ⟨h, hhc, hh, hlh⟩ := hpass
    have hd := released hpre hX ht (bar_at hpre hX ht hub (g := h) (by omega)) hlh
    rw [hhc] at hd
    obtain ⟨hk, hdone⟩ := key_of_released hpre hX ht hbar hd
    exact absurd hdone (hnr 0 hk)
  push Not at hpass
  -- every thread of the CTA has its arrival as its last event
  have hall : ∀ h, h / L.block = c → h < L.threads → (X.tr h).length = 3 := fun h hhc hh =>
    le_antisymm (hpass h hhc hh) (hlag h hhc hh)
  have hlane_lt : ∀ g', g' < L.block → c * L.block + g' < L.threads := by
    intro g' hg'
    simp only [Launch.threads]
    calc c * L.block + g' < c * L.block + L.block := by omega
      _ = (c + 1) * L.block := by ring
      _ ≤ L.grid * L.block := Nat.mul_le_mul_right _ hcg
  have hP : NamedBar.Part L X c none 0 (Finset.range 8) := by
    refine ⟨fun e pc' cnt he hec => ?_, fun y hyc _ j pcx hx => ?_⟩
    · obtain ⟨e1, e2⟩ := e
      obtain ⟨-, -, hcnt, -⟩ := bar_cases hpre hX ht he
      refine ⟨?_, hcnt⟩
      rw [Finset.mem_range]
      have := Nat.mod_lt e1 hb
      simp only
      omega
    · have hy := Frame.lt_of_get hX hx
      have hj := exit_index hpre hX ht hx
      have hl := len_of_get hx
      simp only at hl
      rw [hall y hyc hy] at hl
      omega
  obtain ⟨Y, hmaxY, hle, hsz, htr, hdone, hkeys⟩ := NamedBar.named_finish hmax hcg (n := 8)
    (by decide) (target_none hpre) (by decide) (Finset.card_range 8) (warps_bound hpre) hP
    (G := 0) (fun g' hg' _ => by
      obtain ⟨h1, -⟩ := NamedBar.lane_cta (c := c) hb hg'
      have hl := hall _ h1 (hlane_lt g' hg')
      rw [hl]
      exact ⟨Flow.bar_0, bar_at hpre hX ht hub (by omega), barId_take_two hpre hX ht _⟩)
    (fun Y a ha => wf_all a ha Y)
  have hgc : c * L.block + g % L.block = g := by
    rw [hc, Nat.mul_comm]; exact Nat.div_add_mod g L.block
  have hkey := hkeys (g % L.block) (Nat.mod_lt _ hb)
    (by rw [Finset.mem_range]; have := Nat.mod_lt g hb; omega)
  rw [hgc] at hkey
  have hYX : ∀ h, Y.tr h = X.tr h := fun h => congrFun htr h
  have hpY : Frame.Pending L Y g :=
    ⟨hg, not_canceled hmaxY.1, by rw [hYX]; exact hp.2.2⟩
  have hblY : LastReleased L Y g := by
    intro id' count' pc' _ _
    refine ⟨0 + 16 * 0, ?_, hdone⟩
    rw [hYX]
    exact hkey
  obtain ⟨Z, hZ, hYZ, hlt⟩ := Descent.plain_extends noTma noShfl noAtomic hC hmaxY.1
    (hT Y hmaxY.1).tracked (fun h => hsafe.2 Y hmaxY.1 (.inl h)) hpY init_not_bar
    (fun id count pc hbar => by
      have hl : 0 < (Y.tr g).length := by
        have hlt := len_of_get hbar
        simp only at hlt
        omega
      obtain ⟨key, hk, hd⟩ := hblY id count pc hl hbar
      exact NamedBar.ready_of_released hmaxY.1.ctaBar hbar hk hd)
    (ext_wf Y g)
  exact .inl ⟨Z, hZ, Execution.le_trans hle hYZ, by omega⟩

/-- **Every maximal execution is complete.** -/
theorem progress_goal (hpre : Pre L A B x mem0)
    (hT : ∀ X, Consistent L kernel Prod mem0 X → ThreadFacts A B L X)
    (hsafe : SafeGoal kernel Prod L mem0) : ProgressGoal kernel Prod L mem0 :=
  Descent.progress_of_threads noTma rankOf fun _ _ hmax hp => thread_steps hpre hsafe hT hmax hp

end
end PTX.Kernels.BlockSum.Proof
