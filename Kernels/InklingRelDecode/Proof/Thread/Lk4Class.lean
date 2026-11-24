-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LkD
public import Kernels.InklingRelDecode.Proof.Thread.LkWStep

@[expose] public section

/-!
# Warp lockstep: the warp-collective `tcgen05` states and the exit

The warp-collective `tcgen05` instructions (`isTcColl`: the paired Tensor Memory operations, the
loads, the stores and their waits) are fired from states of the common start (the allocation and
the permit relinquishment), of the softmax region (the score tile's load and its wait, the
probabilities' store and its wait, the rescale's load, wait, store and wait) and of the epilogue
(the load and its wait, the deallocation). `collPcs` lists the program's positions (checked by
`decide +kernel`: exactly the instructions of those forms); the other machines have no state at
one. `dTc` is the predicate of the default partition's states, from the sites; the workers have
none. A state of the class is synchronizing (`dTc_sy`), and a synchronizing state is in the class
exactly when its position is one of those (`dTc_iff`).

The exit: the position of the program's `ret` is not a synchronizing position, and the key of the
state that fires it is that position (`d_exit_key`, `w_exit_key`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The instruction is a warp-collective `tcgen05` instruction. -/
def collOp : Op → Bool
  | .tcAlloc .. | .tcDealloc .. | .tcRelinquish .. | .tcLd .. | .tcWaitLd | .tcSt ..
  | .tcWaitSt => true
  | _ => false

/-- The positions of the warp-collective `tcgen05` instructions of the program. -/
def collPcs : List Nat :=
  [11, 15, 1009, 1010, 1265, 1298, 2260, 2261, 2328, 2329, 2607, 2608, 2851, 2854]

/-- Every warp-collective `tcgen05` instruction is listed, and only those. -/
theorem kernel_collPcs : OpPcsFast kernel.code collOp collPcs = true := by decide +kernel

/-- The position is a warp-collective `tcgen05` instruction. -/
def collPc (pc : Nat) : Bool := collPcs.contains pc

/-! ### The sites at the listed positions -/

theorem dstart_coll (s : DStart.Site) (h : s.pc ∈ collPcs) :
    s = .alloc ∨ s = .allocWr ∨ s = .relinq := by
  revert h
  cases s <;> first | (intro _; simp; done) | (intro h; exfalso; revert h; decide +kernel)

theorem pro_notColl (s : ProA.Site) : s.pc ∉ collPcs := by
  cases s <;> decide +kernel

theorem sm_coll (s : Sm.Site) (h : s.pc ∈ collPcs) :
    s = .ldS ∨ s = .waitLd ∨ s = .tmemSt ∨ s = .tmemWait ∨ s = .ldO ∨ s = .waitLdO ∨ s = .stO
      ∨ s = .waitStO := by
  revert h
  cases s
  all_goals try (rename_i j; revert j)
  all_goals first
    | (intro _; simp; done)
    | (intro h; exfalso; revert h; decide +kernel)
    | (intro j h; exfalso; revert j h; decide +kernel)

theorem epi_coll (s : Epi.Site) (h : s.pc ∈ collPcs) : s = .ld ∨ s = .waitLd ∨ s = .dealloc := by
  revert h
  cases s
  all_goals try (rename_i j; revert j)
  all_goals first
    | (intro _; simp; done)
    | (intro h; exfalso; revert h; decide +kernel)
    | (intro j h; exfalso; revert j h; decide +kernel)

theorem worker_notColl (s : Worker.Site) : s.pc ∉ collPcs := by cases s <;> decide +kernel
theorem idle_notColl (s : Worker.Idle.Site) : s.pc ∉ collPcs := by cases s <;> decide +kernel
theorem loader_notColl (s : Loader.Site) : s.pc ∉ collPcs := by cases s <;> decide +kernel
theorem mma_notColl (s : Mma.Site) : s.pc ∉ collPcs := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel
theorem exitSite_notColl (s : WComp.ExitSite) : s.pc ∉ collPcs := by cases s <;> decide +kernel

/-- **A worker state is at no warp-collective `tcgen05` position.** -/
theorem wColl_not (s : WComp.WSt) : collPc (WComp.pc s) = false := by
  have : WComp.pc s ∉ collPcs := by
    cases s with
    | worker w => exact worker_notColl w.site
    | idle d => exact idle_notColl d.site
    | loader d _ => exact loader_notColl d.site
    | mma d _ => exact mma_notColl d.site
    | exit x => exact exitSite_notColl x.site
  simpa [collPc] using this

/-! ### The states of the default partition -/

/-- The default-partition state's event is a warp-collective `tcgen05` event (the allocation and
the relinquishment, the softmax region's eight, the epilogue's three). -/
def dTc : DComp.St → Bool
  | .dstart d => decide (d.site = .alloc ∨ d.site = .relinq)
  | .pro _ => false
  | .sm d => decide (d.site = .ldS ∨ d.site = .waitLd ∨ d.site = .tmemSt ∨ d.site = .tmemWait ∨
      d.site = .ldO ∨ d.site = .waitLdO ∨ d.site = .stO ∨ d.site = .waitStO)
  | .epi d => decide (d.site = .ld ∨ d.site = .waitLd ∨ d.site = .dealloc)

theorem dstart_tc_pc (s : DStart.Site) (h : s = .alloc ∨ s = .relinq) : s.pc ∈ collPcs := by
  rcases h with rfl | rfl <;> decide +kernel

theorem sm_tc_pc (s : Sm.Site) (h : s = .ldS ∨ s = .waitLd ∨ s = .tmemSt ∨ s = .tmemWait ∨
    s = .ldO ∨ s = .waitLdO ∨ s = .stO ∨ s = .waitStO) : s.pc ∈ collPcs := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem epi_tc_pc (s : Epi.Site) (h : s = .ld ∨ s = .waitLd ∨ s = .dealloc) : s.pc ∈ collPcs := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- **A state of the class is synchronizing.** -/
theorem dTc_sy {s : DComp.St} (h : dTc s = true) : dSy s = true := by
  cases s with
  | dstart d =>
    obtain ⟨site, tm⟩ := d
    simp only [dTc, decide_eq_true_eq] at h
    simp only [dSy, dsSy, Bool.and_eq_true, decide_eq_true_eq]
    rcases h with rfl | rfl <;> decide +kernel
  | pro d => simp [dTc] at h
  | sm d =>
    obtain ⟨site, e, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
    simp only [dTc, decide_eq_true_eq] at h
    simp only [dSy, smSy]
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  | epi d =>
    obtain ⟨site, pr, o, sk⟩ := d
    simp only [dTc, decide_eq_true_eq] at h
    simp only [dSy, epSy]
    rcases h with rfl | rfl | rfl <;> decide +kernel

/-- **A synchronizing state of the default partition is in the class exactly when its position
is a warp-collective `tcgen05` position.** -/
theorem dTc_iff {s : DComp.St} (hs : dSy s = true) : dTc s = true ↔ collPc (DComp.pc s) = true := by
  cases s with
  | dstart d =>
    obtain ⟨site, tm⟩ := d
    simp only [dSy, dsSy, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨hsy, hne⟩ := hs
    simp only [dTc, DComp.pc, collPc, List.contains_iff_mem, decide_eq_true_eq]
    constructor
    · exact dstart_tc_pc site
    · intro h
      rcases dstart_coll site h with h | h | h
      · exact .inl h
      · subst h; exfalso; revert hsy; decide +kernel
      · exact .inr h
  | pro d =>
    simp only [dTc, DComp.pc, collPc, Bool.false_eq_true, false_iff, List.contains_iff_mem]
    exact pro_notColl d.site
  | sm d =>
    obtain ⟨site, e, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
    simp only [dTc, DComp.pc, collPc, List.contains_iff_mem, decide_eq_true_eq]
    exact ⟨sm_tc_pc site, sm_coll site⟩
  | epi d =>
    obtain ⟨site, pr, o, sk⟩ := d
    simp only [dTc, DComp.pc, collPc, List.contains_iff_mem, decide_eq_true_eq]
    exact ⟨epi_tc_pc site, epi_coll site⟩

/-! ### The exit -/

theorem syPc_exit : syPc Epi.Site.exit.pc = false := by decide +kernel

theorem syAt_ne_exit {pc sub : Nat} (h : syAt pc sub = true) : pc ≠ Epi.Site.exit.pc := by
  intro hpc
  simp only [syAt, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [hpc, syPc_exit] at h
  exact absurd h.1 (by simp)

/-- **A synchronizing state of the default partition is not at the program's exit.** -/
theorem dSy_ne_exit {s : DComp.St} (h : dSy s = true) : DComp.pc s ≠ Epi.Site.exit.pc := by
  cases s with
  | dstart d => simp only [dSy, Bool.and_eq_true] at h; exact syAt_ne_exit h.1
  | pro d => exact syAt_ne_exit h
  | sm d => exact syAt_ne_exit h
  | epi d => exact syAt_ne_exit h

/-- **A synchronizing state of a worker is not at the program's exit.** -/
theorem wSy_ne_exit {s : WComp.WSt} (h : wSy s = true) : WComp.pc s ≠ Epi.Site.exit.pc := by
  simp only [wSy, Bool.or_eq_true] at h
  rcases h with h | h
  · exact syAt_ne_exit h
  · cases s with
    | worker w =>
      obtain ⟨site, P⟩ := w
      cases site <;> simp only [isLdRole, Bool.false_eq_true] at h
      show Worker.Site.ldRole.pc ≠ Epi.Site.exit.pc
      decide +kernel
    | _ => simp [isLdRole] at h

/-- **The key of the epilogue's exit state is the position of the exit.** -/
theorem d_exit_key (L : Launch) (g : Nat) (d : Epi.D) (h : d.site = .exit) :
    (dKey L g (.epi d)).1 = Epi.Site.exit.pc := by
  obtain ⟨site, pr, o, sk⟩ := d
  simp only at h
  subst h
  simp only [dKey, epKey, epK, reduceCtorEq, ↓reduceIte]
  decide +kernel

/-- **The key of the exit role's `ret` state is the position of the exit.** -/
theorem w_exit_key (L : Launch) (g : Nat) (x : WComp.ExitD) (h : x.site = .ret) :
    wKey L g (.exit x) = Epi.Site.exit.pc := by
  obtain ⟨site, P⟩ := x
  simp only at h
  subst h
  simp only [wKey, wkX]
  decide +kernel

end
end PTX.Kernels.InklingRelDecode.Proof.Lk
