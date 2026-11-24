-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WqKxWMma

@[expose] public section

/-!
# The key time of the worker warps at synchronizing steps, all roles

`kxW_step`: two lanes' synchronizing worker states with one key and one key time, which agree
(`WAgree`) and are valid (`WValid`), have successors of one key time. The roles are told apart by
position (`role_eq`); a role's last state returns to the dispatch loop's head in its later round
(`workerT_loop_late`); the dispatch enters the role the two lanes agree on, whose first state has
a fixed time, or the bad path, timed by the round marker, which one key time fixes.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {L : Launch} {g h : Nat} {e e' : Event}

/-! ### The MMA warp -/

theorem qk_notSy : ∀ j : Fin 8, syPc (Mma.Site.qk j).pc = false := by decide +kernel

theorem pv_notSy : ∀ j : Fin 8, syPc (Mma.Site.pv j).pc = false := by decide +kernel

theorem kstep_M {d d' t t' : Mma.D} (hs : syPc d.site.pc = true)
    (hs' : syPc d'.site.pc = true) (hpc : d.site.pc = d'.site.pc) (hx : kxM d = kxM d')
    (hb : d.site = .bar0 → d.i = d'.i)
    (ha : d.site.isSkip = false ∧ d'.site.isSkip = false ∧
      (d.site = .bar0 → (Mma.start d).site = (Mma.start d').site) ∧
      (d.site = .qkElect → (Mma.afterQk d).site = (Mma.afterQk d').site) ∧
      (d.site = .pvElect → (Mma.iterNext d).site = (Mma.iterNext d').site))
    (hn : Mma.next L g d e = some (some t)) (hn' : Mma.next L h d' e' = some (some t')) :
    kxM t = kxM t' := by
  obtain ⟨hk, hk', ha⟩ := ha
  have hab := Mma.Site.eq_of_pc hk hk' hpc
  obtain ⟨a, i, n, tm, pro⟩ := d
  obtain ⟨b, i', n', tm', pro'⟩ := d'
  simp only at hab hs hk
  subst hab
  cases a with
  | qk j => exact absurd hs (by rw [qk_notSy j]; simp)
  | pv j => exact absurd hs (by rw [pv_notSy j]; simp)
  | qkSkip => exact absurd hk (by decide)
  | pvSkip => exact absurd hk (by decide)
  | _ =>
    first
    | (exfalso; revert hs; decide +kernel)
    | exact mstep_setMaxReg hx hb ha hn hn'
    | exact mstep_bar0 hx hb ha hn hn'
    | exact mstep_qkBar hx hb ha hn hn'
    | exact mstep_qkShfl hx hb ha hn hn'
    | exact mstep_qkBar2 hx hb ha hn hn'
    | exact mstep_qkElect hx hb ha hn hn'
    | exact mstep_pvBar hx hb ha hn hn'
    | exact mstep_pvShfl hx hb ha hn hn'
    | exact mstep_pvBar2 hx hb ha hn hn'
    | exact mstep_pvElect hx hb ha hn hn'
    | exact mstep_finBar hx hb ha hn hn'
    | exact mstep_finElect hx hb ha hn hn'
    | exact mstep_bar1 hx hb ha hn hn'
    | (simp [Mma.next] at hn; done)

/-! ### The worker -/

theorem late_iff_of {s : Worker.Site} {P P' : Loader.Pro}
    (hs : s = .loop ∨ s = .bar2 ∨ s = .ldRole ∨ s = .bad0 ∨ s = .bad1)
    (hx : workerT ⟨s, P⟩ = workerT ⟨s, P'⟩) : (Worker.late P ↔ Worker.late P') := by
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp only [workerT] at hx <;>
    by_cases h1 : Worker.late P <;> by_cases h2 : Worker.late P' <;>
    simp only [h1, h2, ↓reduceIte, iff_true, true_iff, iff_false, false_iff, not_false_eq_true,
      not_true_eq_false, iff_self] at hx ⊢ <;> wt_omega

theorem kstep_ldRole {P P' : Loader.Pro} {t t' : WComp.WSt} (hl : Worker.late P ↔ Worker.late P')
    (ha : roleIdx L g ⟨.ldRole, P⟩ e = roleIdx L h ⟨.ldRole, P'⟩ e')
    (hn : WComp.dispatch L g P e = some (some t))
    (hn' : WComp.dispatch L h P' e' = some (some t')) : kxW t = kxW t' := by
  unfold WComp.dispatch at hn hn'
  unfold roleIdx at ha
  cases h1 : Worker.next L g ⟨.ldRole, P⟩ e with
  | none => simp [h1] at hn
  | some o =>
    cases o with
    | none => simp [h1] at hn
    | some d1 =>
      cases h2 : Worker.next L h ⟨.ldRole, P'⟩ e' with
      | none => simp [h2] at hn'
      | some o' =>
        cases o' with
        | none => simp [h2] at hn'
        | some d2 =>
          rw [h1, h2] at ha
          simp only [Option.map_some, Option.some.injEq] at ha
          rw [h1] at hn
          rw [h2] at hn'
          obtain ⟨s1, Q1⟩ := d1
          obtain ⟨s2, Q2⟩ := d2
          have hP1 : Q1 = P := by
            simp only [Worker.next, Worker.dispatch] at h1
            (repeat' split at h1) <;> simp_all
          have hP2 : Q2 = P' := by
            simp only [Worker.next, Worker.dispatch] at h2
            (repeat' split at h2) <;> simp_all
          subst hP1 hP2
          simp only at ha hn hn'
          subst ha
          cases s1 <;> simp only [WComp.roleStart] at hn hn' <;>
            (repeat' split at hn) <;> (repeat' split at hn') <;>
            first
            | (simp at hn; done)
            | (simp at hn'; done)
            | (simp only [Option.some.injEq] at hn hn'
               subst hn hn'
               first
               | rfl
               | (simp only [kxW, kxWk, workerT]
                  by_cases h1 : Worker.late Q1 <;> by_cases h2 : Worker.late Q2 <;>
                    simp_all))

theorem kstep_W {w w' : Worker.D} {t t' : WComp.WSt} (hs : wSy (.worker w) = true)
    (hs' : wSy (.worker w') = true) (hpc : w.site.pc = w'.site.pc) (hx : kxWk w = kxWk w')
    (hv : w.site = .shfl → ¬ Worker.late w.P) (hv' : w'.site = .shfl → ¬ Worker.late w'.P)
    (ha : w.site = .ldRole → roleIdx L g w e = roleIdx L h w' e')
    (hn : WComp.next L g (.worker w) e = some (some t))
    (hn' : WComp.next L h (.worker w') e' = some (some t')) : kxW t = kxW t' := by
  obtain ⟨a, P⟩ := w
  obtain ⟨b, P'⟩ := w'
  simp only at hpc ha hv hv' hx
  cases a <;> cases b <;>
    simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false, Bool.or_true] at hs hs' <;>
    first
    | (exfalso; revert hs hs' hpc; decide +kernel)
    | exact kstep_ldRole (late_iff_of (s := .ldRole) (by simp) hx) (ha rfl) hn hn'
    | (simp only [WComp.next, Worker.next] at hn hn'
       (repeat' split at hn)
       all_goals (repeat' split at hn')
       all_goals
         first
         | (simp at hn; done)
         | (simp at hn'; done)
         | (simp only [Option.map_some, Option.some.injEq] at hn hn'
            subst hn hn'
            first
            | rfl
            | (simp only [kxW, kxWk, workerT] at hx hv hv' ⊢
               by_cases h1 : Worker.late P <;> by_cases h2 : Worker.late P' <;>
                 simp_all <;> wt_omega)))

/-! ### The idle role and the exit -/

theorem kstep_I {d d' : Worker.Idle.D} {t t' : WComp.WSt}
    (hpc : d.site.pc = d'.site.pc)
    (hn : WComp.next L g (.idle d) e = some (some t))
    (hn' : WComp.next L h (.idle d') e' = some (some t')) : kxW t = kxW t' := by
  obtain ⟨a, P⟩ := d
  obtain ⟨b, P'⟩ := d'
  simp only at hpc
  cases a <;> cases b <;> first
    | (exfalso; revert hpc; decide +kernel)
    | (simp only [WComp.next, Worker.Idle.next] at hn hn'
       simp only [Option.map_some, Option.some.injEq] at hn hn'
       subst hn hn'
       first | rfl | simp only [kxW, kxWk, workerT_loop_late])

theorem kstep_X {x x' : WComp.ExitD} {t t' : WComp.WSt}
    (hn : WComp.next L g (.exit x) e = some (some t))
    (hn' : WComp.next L h (.exit x') e' = some (some t')) : kxW t = kxW t' := by
  obtain ⟨a, P⟩ := x
  obtain ⟨b, P'⟩ := x'
  cases a <;> cases b <;> first
    | (simp [WComp.next] at hn; done)
    | (simp [WComp.next] at hn'; done)
    | (simp only [WComp.next, Option.some.injEq] at hn hn'
       subst hn hn'
       rfl)

/-! ### The loader and the MMA warp, with their returns -/

theorem kstep_Lw {d d' : Loader.D} {P P' : Loader.Pro} {t t' : WComp.WSt}
    (hs : wSy (.loader d P) = true) (hs' : wSy (.loader d' P') = true)
    (hpc : d.site.pc = d'.site.pc) (hx : kxL d = kxL d') (hb : d.site = .bar0 → d.i = d'.i)
    (ha : LdAgree d d')
    (hn : WComp.next L g (.loader d P) e = some (some t))
    (hn' : WComp.next L h (.loader d' P') e' = some (some t')) : kxW t = kxW t' := by
  have hs0 := sy_loader hs
  have hs0' := sy_loader hs'
  by_cases hl : d.site = .setMaxInc
  · have hl' := loader_sm hs0' hpc hl
    obtain ⟨a, pro, i, n, p0, p1, ln⟩ := d
    obtain ⟨b, pro', i', n', p0', p1', ln'⟩ := d'
    simp only at hl hl'
    subst hl hl'
    simp only [WComp.next, Option.some.injEq] at hn hn'
    subst hn hn'
    simp only [kxW, kxWk, workerT_loop_late]
  · have hl' : d'.site ≠ .setMaxInc := fun h' => hl (loader_sm hs0 hpc.symm h')
    rw [next_loader hl] at hn
    rw [next_loader hl'] at hn'
    obtain ⟨t0, ht0, rfl⟩ := mapInv hn
    obtain ⟨t0', ht0', rfl⟩ := mapInv hn'
    exact kstep_L hs0 hs0' hpc hx hb ha ht0 ht0'

theorem kstep_Mw {d d' : Mma.D} {P P' : Loader.Pro} {t t' : WComp.WSt}
    (hs : wSy (.mma d P) = true) (hs' : wSy (.mma d' P') = true)
    (hpc : d.site.pc = d'.site.pc) (hx : kxM d = kxM d') (hb : d.site = .bar0 → d.i = d'.i)
    (ha : d.site.isSkip = false ∧ d'.site.isSkip = false ∧
      (d.site = .bar0 → (Mma.start d).site = (Mma.start d').site) ∧
      (d.site = .qkElect → (Mma.afterQk d).site = (Mma.afterQk d').site) ∧
      (d.site = .pvElect → (Mma.iterNext d).site = (Mma.iterNext d').site))
    (hn : WComp.next L g (.mma d P) e = some (some t))
    (hn' : WComp.next L h (.mma d' P') e' = some (some t')) : kxW t = kxW t' := by
  have hs0 := sy_mma hs
  have hs0' := sy_mma hs'
  by_cases hl : d.site = .setMaxRegInc
  · have hl' := mma_sm hs0' hpc hl
    obtain ⟨a, i, n, tm, pro⟩ := d
    obtain ⟨b, i', n', tm', pro'⟩ := d'
    simp only at hl hl'
    subst hl hl'
    simp only [WComp.next, Option.some.injEq] at hn hn'
    subst hn hn'
    simp only [kxW, kxWk, workerT_loop_late]
  · have hl' : d'.site ≠ .setMaxRegInc := fun h' => hl (mma_sm hs0 hpc.symm h')
    rw [next_mma hl] at hn
    rw [next_mma hl'] at hn'
    obtain ⟨t0, ht0, rfl⟩ := mapInv hn
    obtain ⟨t0', ht0', rfl⟩ := mapInv hn'
    exact kstep_M hs0 hs0' hpc hx hb ha ht0 ht0'

/-! ### All roles -/

/-- **Two lanes' synchronizing worker states with one key and one key time, which agree and are
valid with one number `c`, have successors of one key time.** -/
theorem kxW_step {c : Nat} {s s' t t' : WComp.WSt} (hs : wSy s = true) (hs' : wSy s' = true)
    (hk : wKey L g s = wKey L h s') (hx : kxW s = kxW s') (hv : WValid c s)
    (hv' : WValid c s') (ha : WAgree L g h s s' e e')
    (hn : WComp.next L g s e = some (some t)) (hn' : WComp.next L h s' e' = some (some t')) :
    kxW t = kxW t' := by
  have hpc : WComp.pc s = WComp.pc s' :=
    (w_sy_key (L := L) (g := g) hs).symm.trans (hk.trans (w_sy_key (L := L) (g := h) hs'))
  have hr := role_eq hs hs' hn hn' hpc
  cases s <;> cases s' <;> try (simp [wRole] at hr; done)
  · exact kstep_W hs hs' hpc hx hv hv' ha hn hn'
  · exact kstep_I hpc hn hn'
  · rename_i d P d' P'
    have hab := loader_site_eq _ _ (sy_loader hs) (sy_loader hs') hpc
    refine kstep_Lw hs hs' hpc hx (fun h0 => ?_) ha hn hn'
    have h0' : d'.site = .bar0 := by rw [← hab]; exact h0
    exact (hv h0).trans (hv' h0').symm
  · rename_i d P d' P'
    have hab := Mma.Site.eq_of_pc ha.1 ha.2.1 hpc
    refine kstep_Mw hs hs' hpc hx (fun h0 => ?_) ha hn hn'
    have h0' : d'.site = .bar0 := by rw [← hab]; exact h0
    exact (hv h0).trans (hv' h0').symm
  · exact kstep_X hn hn'

end
end PTX.Kernels.InklingRelDecode.Proof.Lk
