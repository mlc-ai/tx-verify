-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Protocol.Objects
public import Lemmas.Protocol.MbarOneShot
public import Lemmas.Flow.SpinsAtLoop

@[expose] public section

/-! # `tc_gemm`: the two mbarriers

`bar0` is a one-phase barrier of thread 0's initialization, its arrival expecting 4352 bytes and
the complete-tx of the copies of `A` (4096 bytes) and `B` (256 bytes), polled by thread 0
(`table0`); `bar1` is a one-phase barrier of thread 0's initialization and the commit's arrive-on,
polled by every thread (`table1`): both are `MbarOneShot.Table`s. So no record faults and every
record follows its published initialization (`object_fault_free`, `object_published`); a
successful poll of `bar0` observes both copies' completion (`wait_observes_copies`), and a
successful poll of `bar1` observes the MMA's completion through the commit
(`wait_observes_mma`). -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}

/-- **The kernel's polls are canonical spins**: each heads a self loop whose branch alone reads
its predicate. -/
theorem spins {pc : Nat} (h : pc = Flow.mbarWait_0 ∨ pc = Flow.mbarWait_1) :
    ∃ exit, kernel.CanonicalSpin pc exit := by
  rcases h with rfl | rfl
  · exact ⟨_, Kernel.canonicalSpin_of_selfLoop Flow.code_26 Flow.code_27 (by decide) (by decide)
      (by decide +kernel) (by unfold Kernel.SpinPred; decide +kernel)⟩
  · exact ⟨_, Kernel.canonicalSpin_of_selfLoop Flow.code_41 Flow.code_42 (by decide) (by decide)
      (by decide +kernel) (by unfold Kernel.SpinPred; decide +kernel)⟩

/-- The copies completing on `bar0`. -/
def copies : List (EvId × Nat) := [((0, 6), 4096), ((0, 7), 256)]

/-- The commit's arrive-on of `bar1`. -/
def commitRef (P : Nat → Par) : Ref := .async (0, hd 0 + 3 + (P 0).n0) (.tcNotify 0)

section
variable (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre hX hW

omit hpre hX hW in
/-- A later event of thread 0 after an event without an access happens after it. -/
theorem po0 {i j : Nat} {ev : Event} (hi : X.get (0, i) = some ev) (hacc : ev.acc = none)
    (hij : i < j) (hj : j < (X.tr 0).length) : baseCausality L X (0, i) (0, j) :=
  po_baseCausality hij hj (by rw [hi]; exact hacc)

omit hpre hX in
/-- An event before a thread's read is in its whole trace. -/
theorem lt_m_of_get {g j : Nat} {ev : Event} (he : X.get (g, j) = some ev) (hj : j ≤ hd g) :
    j < m g := by
  obtain ⟨hg, ⟨hjm, -⟩ | ⟨hjeq, pc, f, -, -⟩⟩ := hW.get he
  · exact hjm
  · have hg' : g < 128 := hg
    have hj' : j = m g := hjeq
    have := tl_ge (g := g) (P g)
    have := ldIdx_eq (g := g) (P g)
    rcases hW.ub g hg' with hu | ⟨pc', f', -, ⟨h1, -⟩ | ⟨k, -, h1, -⟩⟩
    · have hl := hW.length g hg'
      rw [hu, List.length_nil] at hl
      have hlt : j < (X.tr g).length := len_of_get he
      omega
    · omega
    · omega

omit hpre hX in
/-- Thread 0's initializations, once it has made them. -/
theorem init_get {k : Nat} {ev : Event} (hk : k = 2 ∨ k = 3) (he : X.get (0, k) = some ev) :
    ev = if k = 2 then init0E L.sharedBase else init1E L.sharedBase := by
  have hkm := lt_m_of_get hW he (by rcases hk with rfl | rfl <;> decide)
  rw [hW.get_of_lt (by decide) hkm, fullAt_head _ (by rcases hk with rfl | rfl <;> decide)] at he
  rcases hk with rfl | rfl <;> simp [headE] at he <;> simp [he]

omit hpre in
/-- The initialization at position `k` of thread 0 happens before the issuer of a record of an
object, other than itself, at a later position. -/
theorem init_baseCausality_of {mb : Loc} {k : Nat} (hk : k = 2 ∨ k = 3) {r : Record Ref}
    (hr : r ∈ X.objects mb) (h0 : r.id.issuer.1 = 0) (hlt : k < r.id.issuer.2)
    (hpres : ∃ ev, X.get (0, k) = some ev) : baseCausality L X (0, k) r.id.issuer := by
  obtain ⟨hi0, hi1⟩ := object_record_issuer_lt hX hW hr
  obtain ⟨ev, he⟩ := hpres
  have hev := init_get hW hk he
  have hl := hW.length 0 (by decide)
  revert h0 hlt hi1
  obtain ⟨i1, i2⟩ := r.id.issuer
  intro h0 hlt hi1
  simp only at h0 hlt hi1
  subst h0
  exact po0 he (by rw [hev]; rcases hk with rfl | rfl <;> rfl) hlt (by omega)

omit hpre in
/-- **`bar0` is a one-phase transaction barrier** of the initialization, the arrival, the two
copies and thread 0's polls. -/
theorem table0 :
    MbarOneShot.Table L X (bar0 L.sharedBase) (0, 2) [(.thread (0, 5), 4352)] copies := by
  have h0 : hd 0 = 9 := rfl
  refine ⟨by decide, by decide, ⟨rfl, by simp [copies]⟩, by decide, by simp, fun r hr => ?_,
    fun r hr a ha hid => ?_, fun r hr hid => ?_, fun ev he => ?_, fun c hc s hs => ?_,
    fun v hv => ?_⟩
  · rcases copy_record_cases hX hW hr with h | h | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ |
      ⟨j, ok, -, -, h1, h2, -⟩
    · exact .inl h
    · exact .inr (.inl ⟨_, List.mem_singleton_self _, h⟩)
    · exact .inr (.inr (.inl ⟨((0, 6), 4096), by simp [copies], h1, h2⟩))
    · exact .inr (.inr (.inl ⟨((0, 7), 256), by simp [copies], h1, h2⟩))
    · exact .inr (.inr (.inr ⟨_, ok, h1, h2⟩))
  · obtain rfl := List.mem_singleton.mp ha
    rcases copy_record_cases hX hW hr with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
      ⟨j, ok, hj, -, h, -, -⟩
    · rw [h] at hid; simp at hid
    · exact h
    · rw [h] at hid; simp at hid
    · rw [h] at hid; simp at hid
    · rw [h] at hid; simp at hid; omega
  · have hpres : ∃ ev, X.get (0, 2) = some ev := by
      obtain ⟨-, hi1⟩ := object_record_issuer_lt hX hW hr
      have := hW.length 0 (by decide)
      exact ⟨_, List.getElem?_eq_getElem (show 2 < (X.tr 0).length by
        rcases copy_record_cases hX hW hr with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
          ⟨j, ok, hj, -, h, -, -⟩ <;> rw [h] at hi1 hid <;> simp [Ref.issuer] at hi1 hid ⊢ <;>
          omega)⟩
    have key : r.id.issuer.1 = 0 ∧ 2 < r.id.issuer.2 := by
      rcases copy_record_cases hX hW hr with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
        ⟨j, ok, hj, -, h, -, -⟩ <;> rw [h] at hid ⊢ <;> simp [Ref.issuer] at hid ⊢
      omega
    exact init_baseCausality_of hX hW (k := 2) (.inl rfl) hr key.1 key.2 hpres
  · have := init_get hW (.inl rfl) he
    simp only [↓reduceIte] at this
    rw [this]; rfl
  · simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hc
    exact (hW.copy_spec (issuedBy_some.mp hs)).1
  · obtain ⟨pc, hp⟩ := hv
    obtain ⟨g, j⟩ := v
    exact hW.no_inval hp

/-- **`bar1` is a one-phase barrier** of the initialization, the commit's arrive-on and every
thread's polls. -/
theorem table1 : MbarOneShot.Table L X (bar1 L.sharedBase) (0, 3) [(commitRef P, 0)] [] := by
  have h0 : hd 0 = 9 := rfl
  have hT := threads_eq hpre
  refine ⟨by simp only [List.length_singleton]; decide, by simp, ⟨rfl, by simp⟩, by simp, by simp,
    fun r hr => ?_, fun r hr a ha hid => ?_, fun r hr hid => ?_, fun ev he => ?_,
    fun c hc => by simp at hc, fun v hv => ?_⟩
  · rcases mma_record_cases hX hW hr with h | ⟨h1, h2, -⟩ | ⟨g, -, j, ok, -, -, h1, h2, -⟩
    · exact .inl h
    · exact .inr (.inl ⟨_, List.mem_singleton_self _, h1, h2⟩)
    · exact .inr (.inr (.inr ⟨_, ok, h1, h2⟩))
  · obtain rfl := List.mem_singleton.mp ha
    rcases mma_record_cases hX hW hr with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨g, -, j, ok, -, -, h, -⟩
    · rw [h] at hid; simp [commitRef] at hid
    · exact h
    · rw [h] at hid; simp [commitRef] at hid
  · obtain ⟨hi0, hi1⟩ := object_record_issuer_lt hX hW hr
    rcases mma_record_cases hX hW hr with ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨g, hg, j, ok, hj, -, h, -, -⟩
    · exact (hid h).elim
    · rw [h] at hi1 ⊢
      simp only [Ref.issuer] at hi1 ⊢
      have hl := hW.length 0 (by decide)
      refine po0 (ev := init1E L.sharedBase) ?_ rfl (by omega) (by omega)
      rw [hW.get_of_lt (by decide) (by omega), fullAt_head _ (by decide)]; rfl
    · rw [h] at hi0 hi1 ⊢
      simp only [Ref.issuer] at hi0 hi1 ⊢
      have := tl_ge (g := g) (P g)
      have hl := hW.length g hg
      by_cases hg0 : g = 0
      · subst hg0
        exact po0 (ev := init1E L.sharedBase) (by
          rw [hW.get_of_lt (by decide) (by omega), fullAt_head _ (by decide)]; rfl) rfl (by omega)
          (by omega)
      · have hm0 := issued_of_passed hpre hX hW hg (by omega)
        exact sync0 hpre hX hW (by decide) hg (by decide) (by omega) (by omega) (by omega)
  · have := init_get hW (k := 3) (.inr rfl) he
    simp only [show (3 : Nat) ≠ 2 by decide, ↓reduceIte] at this
    rw [this]; rfl
  · obtain ⟨pc, hp⟩ := hv
    obtain ⟨g, j⟩ := v
    exact hW.no_inval hp

/-- **No record of an mbarrier faults.** -/
theorem object_fault_free {mb : Loc} {r : Record Ref} (hr : r ∈ X.objects mb) : r.fault = none := by
  rcases object_record_cases hX hW hr with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact ((table0 hX hW).hist hX).fault_free hX hr
  · exact ((table1 hpre hX hW).hist hX).fault_free hX hr

/-- **Every record of an mbarrier follows its published initialization.** -/
theorem object_published {mb : Loc} {r : Record Ref} (hr : r ∈ X.objects mb) :
    ObjectPublished L X mb r := by
  rcases object_record_cases hX hW hr with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact (table0 hX hW).published hX hr
  · exact (table1 hpre hX hW).published hX hr

omit hpre in
/-- **A successful poll of `bar0` observes both copies' completion.** -/
theorem wait_observes_copies {w : EvId} {pc : Nat} {acq : Bool} {ws : MbarScope}
    (he : X.get w = some ⟨pc, .wait (bar0 L.sharedBase) 0 true acq ws⟩) :
    AsyncObserved X (0, 6) (.notify .copy) w acq ws ∧
      AsyncObserved X (0, 7) (.notify .copy) w acq ws :=
  ⟨((table0 hX hW).hist hX).observes_copy hX (c := ((0, 6), 4096)) (by simp [copies]) he,
    ((table0 hX hW).hist hX).observes_copy hX (c := ((0, 7), 256)) (by simp [copies]) he⟩

/-- **A successful poll of `bar1` observes the MMA's completion** through the commit. -/
theorem wait_observes_mma {w : EvId} {pc : Nat} {acq : Bool} {ws : MbarScope}
    (he : X.get w = some ⟨pc, .wait (bar1 L.sharedBase) 0 true acq ws⟩) :
    AsyncObserved X (0, hd 0 + 2 + (P 0).n0) .mmaDone w acq ws := by
  have hu := ((table1 hpre hX hW).hist hX).observes_arrive hX (List.mem_singleton_self _) he
  obtain ⟨i, j, d, wr, ph, hd', hdid, -⟩ := hu
  have hdm : d ∈ X.objects (bar1 L.sharedBase) := List.mem_of_getElem? hd'
  have ha := ((hX.tma.2.2.1 _).2.1 d hdm).1
  rw [hdid] at ha
  obtain ⟨hi0, hi1⟩ := object_record_issuer_lt hX hW hdm
  rw [hdid] at hi1
  simp only [commitRef, Ref.issuer] at hi1
  have hcget : X.get (0, hd 0 + 3 + (P 0).n0) = some (commitE L.sharedBase) := by
    rw [hW.get_of_lt (by decide) hi1, fullAt_commit]
  have hmget : X.get (0, hd 0 + 2 + (P 0).n0) = some (mmaE L.sharedBase (P 0).c) := by
    rw [hW.get_of_lt (by decide) (by omega), fullAt_mma]
  have hnot : (0 : Fin 16) ∈ X.tcNotified (0, hd 0 + 3 + (P 0).n0) := by
    simp only [commitRef, objectAction, hcget, commitE] at ha
    split_ifs at ha with hc
    exact hc.2
  have hcommit : X.Commit (0, hd 0 + 3 + (P 0).n0) (commitSpec L.sharedBase) := ⟨_, hcget⟩
  exact ⟨_, _, ⟨(0, hd 0 + 3 + (P 0).n0), commitSpec L.sharedBase, 0, rfl,
    ⟨rfl, by simp, .inl ⟨_, _, _, _, _, hmget⟩, _, hcommit⟩, hcommit, commitSpec_target_zero, hnot⟩,
    ⟨⟨pc, 0, he⟩, ((table1 hpre hX hW).hist hX).observes_arrive hX (List.mem_singleton_self _) he⟩⟩

end

end

end PTX.Kernels.TcGemm.Proof
