-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WtMonoRoles

@[expose] public section

/-!
# The virtual time rises along the steps of both thread machines

`dcompT_lt` and `wcompT_lt`: a counted step of the default-partition thread's machine raises
`time`; so does a counted step of the worker's machine, except the dispatch (the load of the role
byte), which in a later round of the loop goes to the exit, not to a role (the roles' states are
earlier than the later round's loop head). The consequence for the three `after` clauses of
`Remaining` is `time_after` (`WtAfter.lean`).

The composed machines' successors are unfolded by `show` and `rfl` (definitional unfolding).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000
open Classical

/-- A softmax state of the loop is below the epilogue: the loop counter is below `2 ^ 31`. -/
theorem smT_lt_epi0 {L : Launch} {g : Nat} {d : Sm.D} (hI : Sm.Inv L g d) : smT d < epi0 := by
  have h1 := hI.i
  have h2 := Bound.Sm.r26_lt hI.ok
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp only [smT, Bound.Sm.pos] at * <;> wt_omega

/-- **Every counted step of the default-partition thread's machine raises the time.** -/
theorem dcompT_lt {L : Launch} {g : Nat} {Q : Params} {d d' : DComp.St} {e : Event}
    (hI : DComp.Inv L g Q d) (h : DComp.next L g Q d e = some (some d'))
    (hc : e.counts = true) : dcompT d < dcompT d' := by
  cases d with
  | dstart d =>
    obtain ⟨a, ha, hf⟩ := Bound.map_inv (show (DStart.next L g d e).map (Option.map _) =
      some (some d') from h)
    by_cases hs : a.site = DStart.Site.toProA
    · simp only [hs, eq_self, ↓reduceIte] at hf
      subst hf
      have := dstartT_le d
      have h0 : ProA.Site.sMax.ctorIdx = 0 := rfl
      simp only [dcompT, proT, ProA.D.start, h0]
      omega
    · simp only [hs, ↓reduceIte] at hf
      subst hf
      exact dstartT_lt ha hc
  | pro d =>
    have h1 : (if d.site = ProA.Site.bar18 then
        (if ProA.WordsMatch Q (ProA.cta L g .z) d.dt ∧ ProA.wGood d.dt = true then
          some (some (DComp.St.sm (SmEntry.d0 (SmEntry.entOf Q L g d.dt)))) else some none)
        else (ProA.next L g d e).map (Option.map DComp.St.pro)) = some (some d') := h
    by_cases hs : d.site = ProA.Site.bar18
    · simp only [hs, eq_self, ↓reduceIte] at h1
      split at h1
      · simp only [Option.some.injEq] at h1
        subst h1
        have h0 : ProA.Site.bar18.ctorIdx = 181 := rfl
        simp only [dcompT, proT, smT, SmEntry.d0, hs, h0]
        wt_omega
      · simp at h1
    · simp only [hs, ↓reduceIte] at h1
      obtain ⟨a, ha, rfl⟩ := Bound.map_inv h1
      have := Bound.ProA.next_lt ha
      simp only [dcompT, proT]
      omega
  | sm d =>
    have h1 : (if DComp.leaves L g d e then DComp.exitNext L g d
        else (Sm.next L g d e).map (Option.map DComp.St.sm)) = some (some d') := h
    by_cases hl : DComp.leaves L g d e
    · simp only [hl, ↓reduceIte] at h1
      have h2 : (if (DComp.exitIn L g d).NoFault then
          some (some (DComp.St.epi (if (DComp.exitIn L g d).skip then
            Epi.D.startSk (Br.prm (DComp.exitIn L g d))
            else Epi.D.start (Br.prm (DComp.exitIn L g d))))) else none) = some (some d') := h1
      split at h2
      · simp only [Option.some.injEq] at h2
        subst h2
        have := smT_lt_epi0 hI
        have h3 : epi0 ≤ epiT (if (DComp.exitIn L g d).skip then
            Epi.D.startSk (Br.prm (DComp.exitIn L g d))
            else Epi.D.start (Br.prm (DComp.exitIn L g d))) := by
          unfold epiT
          omega
        simp only [dcompT]
        omega
      · simp at h2
    · simp only [hl, ↓reduceIte] at h1
      obtain ⟨a, ha, rfl⟩ := Bound.map_inv h1
      exact smT_lt ha hc
  | epi d =>
    obtain ⟨a, ha, rfl⟩ := Bound.map_inv (show (Epi.next d e).map (Option.map DComp.St.epi) =
      some (some d') from h)
    exact epiT_lt ha hc

/-- The loop's head after a role's return is in a later round, timed at `c3 - 4`. -/
theorem workerT_loop_late (P : Loader.Pro) :
    workerT ⟨.loop, Worker.bumpPro P⟩ = c3 - 4 := by
  simp [workerT, Worker.late_bumpPro]

theorem next_worker_eq {L : Launch} {g : Nat} {e : Event} {w : Worker.D} (hs : w.site ≠ .ldRole) :
    WComp.next L g (.worker w) e = (Worker.next L g w e).map (Option.map WComp.WSt.worker) := by
  obtain ⟨s, P⟩ := w
  cases s <;> first | rfl | exact absurd rfl hs

theorem next_idle_eq {L : Launch} {g : Nat} {e : Event} {d : Worker.Idle.D} (hs : d.site ≠ .inc) :
    WComp.next L g (.idle d) e = (Worker.Idle.next d e).map (Option.map WComp.WSt.idle) := by
  obtain ⟨s, P⟩ := d
  cases s <;> first | rfl | exact absurd rfl hs

theorem next_loader_eq {L : Launch} {g : Nat} {e : Event} {d : Loader.D} (P : Loader.Pro)
    (hs : d.site ≠ .setMaxInc) : WComp.next L g (.loader d P) e =
      (Loader.next L g d e).map (Option.map fun d' => WComp.WSt.loader d' P) := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  cases s <;> first | rfl | exact absurd rfl hs

theorem next_mma_eq {L : Launch} {g : Nat} {e : Event} {d : Mma.D} (P : Loader.Pro)
    (hs : d.site ≠ .setMaxRegInc) : WComp.next L g (.mma d P) e =
      (Mma.next L g d e).map (Option.map fun d' => WComp.WSt.mma d' P) := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> first | rfl | exact absurd rfl hs

/-- **Every counted step of the worker thread's machine that is not the dispatch raises the
time.** The dispatch (the load of the role byte) goes to a role in the first round and to the exit
in the later one; the later round's loop head is timed after the roles. -/
theorem wcompT_lt {L : Launch} {g : Nat} {d d' : WComp.WSt} {e : Event}
    (hI : WComp.Inv L g d) (hne : ∀ P, d ≠ .worker ⟨.ldRole, P⟩)
    (hnb : ∀ P, d ≠ .worker ⟨.bad1, P⟩)
    (h : WComp.next L g d e = some (some d')) (hc : e.counts = true) : wcompT d < wcompT d' := by
  cases d with
  | worker w =>
    have hs : w.site ≠ .ldRole := fun hs => hne w.P (by obtain ⟨s, P⟩ := w; subst hs; rfl)
    rw [next_worker_eq hs] at h
    obtain ⟨a, ha, rfl⟩ := Bound.map_inv h
    have hb : w.site ≠ .bad1 := fun hb => hnb w.P (by obtain ⟨s, P⟩ := w; subst hb; rfl)
    exact workerT_lt hs hb ha
  | idle d =>
    obtain ⟨s, P⟩ := d
    by_cases hs : s = .inc
    · subst hs
      have h1 : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P⟩)) = some (some d') := h
      simp only [Option.some.injEq] at h1
      subst h1
      simp only [wcompT, idleT, workerT_loop_late]
      wt_omega
    · rw [next_idle_eq (d := ⟨s, P⟩) hs] at h
      obtain ⟨a, ha, rfl⟩ := Bound.map_inv h
      exact idleT_lt ha
  | loader d P =>
    by_cases hs : d.site = .setMaxInc
    · obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
      simp only at hs
      subst hs
      have h1 : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P⟩)) = some (some d') := h
      simp only [Option.some.injEq] at h1
      subst h1
      simp only [wcompT, loaderT, workerT_loop_late]
      wt_omega
    · rw [next_loader_eq P hs] at h
      obtain ⟨a, ha, rfl⟩ := Bound.map_inv h
      exact loaderT_lt hI.1 hs ha hc
  | mma d P =>
    by_cases hs : d.site = .setMaxRegInc
    · obtain ⟨s, i, n, tm, pro⟩ := d
      simp only at hs
      subst hs
      have h1 : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P⟩)) = some (some d') := h
      simp only [Option.some.injEq] at h1
      subst h1
      simp only [wcompT, mmaT, workerT_loop_late]
      wt_omega
    · rw [next_mma_eq P hs] at h
      obtain ⟨a, ha, rfl⟩ := Bound.map_inv h
      exact mmaT_lt hI.1 hs ha hc
  | exit x =>
    obtain ⟨s, P⟩ := x
    cases s
    · have h1 : some (some (WComp.WSt.exit ⟨.ret, P⟩)) = some (some d') := h
      simp only [Option.some.injEq] at h1
      subst h1
      simp only [wcompT, exitT]
      wt_omega
    · have h1 : (none : Option (Option WComp.WSt)) = some (some d') := h
      cases h1

end

end PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
