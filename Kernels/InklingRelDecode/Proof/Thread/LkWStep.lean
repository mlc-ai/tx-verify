-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LkWSilent

@[expose] public section

/-!
# Warp lockstep: the worker warps, synchronizing states

Two lanes' synchronizing states of one key have successors of one key when they agree on
`WAgree` (`w_step`). The statement is proved role by role (`step_W`, `step_I`, `step_L`,
`step_M`) at states of one role, and the states of different roles are told apart by their
positions (`pc_mem`, `rolePcs_disj`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g h : Nat} {e e' : Event}

/-! ### The loader -/

theorem step_L {d d' t t' : Loader.D} (hs : syPc d.site.pc = true) (hs' : syPc d'.site.pc = true)
    (hpc : d.site.pc = d'.site.pc)
    (ha : LdAgree d d')
    (hn : Loader.next L g d e = some (some t)) (hn' : Loader.next L h d' e' = some (some t')) :
    wkL t = wkL t' := by
  obtain ⟨a, pro, i, n, p0, p1, ln⟩ := d
  obtain ⟨b, pro', i', n', p0', p1', ln'⟩ := d'
  simp only at hs hs' hpc ha hn hn'
  cases a <;> cases b <;> first
    | (exfalso; revert hs hs' hpc; decide +kernel)
    | (unfold LdAgree at ha
       simp at ha
       simp only [Loader.next, Loader.afterIter] at hn hn'
       (repeat' split at hn)
       all_goals (repeat' split at hn')
       all_goals
         first
         | (simp at hn; done)
         | (simp at hn'; done)
         | (simp only [Option.some.injEq] at hn hn'
            subst hn hn'
            simp only [wkL, Loader.sub]
            (repeat' split)
            all_goals first | decide +kernel | omega))

/-! ### The MMA warp -/

theorem start_site (d : Mma.D) :
    (Mma.start d).site = if d.n = 0 ∨ 2147483646 < d.n then .finBar else .qkBar := by
  unfold Mma.start
  split <;> rfl

theorem iterNext_site (d : Mma.D) :
    (Mma.iterNext d).site =
      if d.i = d.n then .finBar else if d.i + 1 < d.n then .qkBar else .pvBar := rfl

theorem afterQk_site (d : Mma.D) :
    (Mma.afterQk d).site =
      if d.i = 0 then (if d.i = d.n then .finBar else if d.i + 1 < d.n then .qkBar else .pvBar)
      else .pvBar := by
  unfold Mma.afterQk
  split <;> rfl

theorem step_M {d d' t t' : Mma.D} (hs : syPc d.site.pc = true) (hs' : syPc d'.site.pc = true)
    (hpc : d.site.pc = d'.site.pc)
    (ha : d.site.isSkip = false ∧ d'.site.isSkip = false ∧
      (d.site = .bar0 → (Mma.start d).site = (Mma.start d').site) ∧
      (d.site = .qkElect → (Mma.afterQk d).site = (Mma.afterQk d').site) ∧
      (d.site = .pvElect → (Mma.iterNext d).site = (Mma.iterNext d').site))
    (hn : Mma.next L g d e = some (some t)) (hn' : Mma.next L h d' e' = some (some t')) :
    wkM t = wkM t' := by
  obtain ⟨hk, hk', ha⟩ := ha
  have hab := Mma.Site.eq_of_pc hk hk' hpc
  obtain ⟨a, i, n, tm, pro⟩ := d
  obtain ⟨b, i', n', tm', pro'⟩ := d'
  simp only at hs hs' hpc ha hn hn' hab hk
  subst hab
  clear hs' hpc hk'
  cases a <;> first
    | (exfalso; revert hs; decide +kernel)
    | (exfalso; revert hk; decide +kernel)
    | (exfalso; clear ha hn hn'; rename_i j; revert hs; revert j; decide +kernel)
    | (simp only [start_site, afterQk_site, iterNext_site] at ha
       simp only [Mma.next, Mma.start, Mma.afterQk, Mma.iterNext] at hn hn'
       (repeat' split at hn)
       all_goals (repeat' split at hn')
       all_goals
         first
         | (simp at hn; done)
         | (simp at hn'; done)
         | (simp only [Option.some.injEq] at hn hn'
            subst hn hn'
            simp only [wkM, Mma.afterQk, Mma.iterNext]
            (repeat' split)
            all_goals (try dsimp only)
            all_goals
              first
              | decide +kernel
              | omega
              | (simp_all; done)
              | ((repeat' split at ha) <;> simp_all)))

/-! ### The worker -/

/-- The role the dispatch enters is a function of the role index only: both lanes' first states
of the role have the same key. -/
theorem step_ldRole {P P' : Loader.Pro} {t t' : WComp.WSt}
    (ha : roleIdx L g ⟨.ldRole, P⟩ e = roleIdx L h ⟨.ldRole, P'⟩ e')
    (hn : WComp.dispatch L g P e = some (some t))
    (hn' : WComp.dispatch L h P' e' = some (some t')) : wKey L g t = wKey L h t' := by
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
          simp only at ha hn hn'
          subst ha
          cases s1 <;> simp only [WComp.roleStart] at hn hn' <;>
            (repeat' split at hn) <;> (repeat' split at hn') <;>
            first
            | (simp at hn; done)
            | (simp at hn'; done)
            | (simp only [Option.some.injEq] at hn hn'
               subst hn hn'
               simp only [wKey, wkL, wkM, wkI, wkX, wkW, Loader.D.start, Worker.Idle.D.start,
                 Loader.sub])

/-- The worker's own states: the forward sites, the dispatch loop and the dispatch. -/
theorem step_W {w w' : Worker.D} {t t' : WComp.WSt} (hs : wSy (.worker w) = true)
    (hs' : wSy (.worker w') = true) (hpc : w.site.pc = w'.site.pc)
    (ha : w.site = .ldRole → roleIdx L g w e = roleIdx L h w' e')
    (hn : WComp.next L g (.worker w) e = some (some t))
    (hn' : WComp.next L h (.worker w') e' = some (some t')) : wKey L g t = wKey L h t' := by
  obtain ⟨a, P⟩ := w
  obtain ⟨b, P'⟩ := w'
  simp only at hpc ha
  cases a <;> cases b <;>
    simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at hs hs' <;>
    first
    | (exfalso; revert hs hs' hpc; decide +kernel)
    | exact step_ldRole (ha rfl) hn hn'
    | (simp only [WComp.next, Worker.next] at hn hn'
       (repeat' split at hn)
       all_goals (repeat' split at hn')
       all_goals
         first
         | (simp at hn; done)
         | (simp at hn'; done)
         | (simp only [Option.map_some, Option.some.injEq] at hn hn'
            subst hn hn'
            simp only [wKey, wkW]))

/-! ### The idle role and the exit -/

theorem step_I {d d' : Worker.Idle.D} {t t' : WComp.WSt}
    (hpc : d.site.pc = d'.site.pc)
    (hn : WComp.next L g (.idle d) e = some (some t))
    (hn' : WComp.next L h (.idle d') e' = some (some t')) : wKey L g t = wKey L h t' := by
  obtain ⟨a, P⟩ := d
  obtain ⟨b, P'⟩ := d'
  simp only at hpc
  cases a <;> cases b <;> first
    | (exfalso; revert hpc; decide +kernel)
    | (simp only [WComp.next, Worker.Idle.next] at hn hn'
       simp only [Option.map_some, Option.some.injEq] at hn hn'
       subst hn hn'
       simp only [wKey, wkW, wkI])

theorem step_X {x x' : WComp.ExitD} {t t' : WComp.WSt}
    (hn : WComp.next L g (.exit x) e = some (some t))
    (hn' : WComp.next L h (.exit x') e' = some (some t')) : wKey L g t = wKey L h t' := by
  obtain ⟨a, P⟩ := x
  obtain ⟨b, P'⟩ := x'
  cases a <;> cases b <;> first
    | (simp [WComp.next] at hn; done)
    | (simp [WComp.next] at hn'; done)
    | (simp only [WComp.next, Option.some.injEq] at hn hn'
       subst hn hn'
       simp only [wKey, wkX])

/-! ### The roles told apart by position -/

/-- The role of a state: worker 0, idle 1, loader 2, MMA warp 3, exit 4. -/
def wRole : WComp.WSt → Nat
  | .worker _ => 0
  | .idle _ => 1
  | .loader _ _ => 2
  | .mma _ _ => 3
  | .exit _ => 4

/-- The synchronizing positions of a role's states (the worker's without the entries of the
roles, which the composed machine does not follow). -/
def rolePcs : Nat → List Nat
  | 0 => [12, 14, 17, 2337, 2338, 2340, 2557, 2558]
  | 1 => [2333, 2334, 2335, 2336]
  | 2 => [2344, 2346, 2377, 2387, 2388, 2392, 2393, 2401, 2403, 2407, 2409, 2419, 2420]
  | 3 => [2422, 2424, 2461, 2464, 2466, 2477, 2509, 2512, 2514, 2525, 2550, 2551, 2554, 2555]
  | _ => [2853]

theorem rolePcs_disj :
    ∀ a ∈ List.range 5, ∀ b ∈ List.range 5, a ≠ b → ∀ x ∈ rolePcs a, x ∉ rolePcs b := by
  decide +kernel

theorem wRole_lt (s : WComp.WSt) : wRole s ∈ List.range 5 := by
  cases s <;> simp [wRole]

/-- A synchronizing state that has a successor is at a position of its role. -/
theorem pc_mem {s t : WComp.WSt} (hs : wSy s = true)
    (hn : WComp.next L g s e = some (some t)) : WComp.pc s ∈ rolePcs (wRole s) := by
  cases s with
  | worker w =>
    obtain ⟨a, P⟩ := w
    cases a <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, wRole, rolePcs,
      Bool.or_false] at hs ⊢ <;>
      first
      | (revert hs; decide +kernel)
      | (exfalso; simp [WComp.next, Worker.next] at hn)
  | idle d =>
    obtain ⟨a, P⟩ := d
    cases a <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, wRole, rolePcs,
      Bool.or_false] at hs ⊢ <;> (revert hs; decide +kernel)
  | loader d P =>
    obtain ⟨a, pro, i, n, p0, p1, ln⟩ := d
    cases a <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Loader.sub, wRole, rolePcs,
      Bool.or_false] at hs ⊢ <;> (revert hs; decide +kernel)
  | mma d P =>
    obtain ⟨a, i, n, tm, pro⟩ := d
    clear hn
    cases a <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, wRole, rolePcs,
      Bool.or_false] at hs ⊢ <;>
      first
      | (revert hs; decide +kernel)
      | (rename_i j; revert hs j; decide +kernel)
  | exit x =>
    obtain ⟨a, P⟩ := x
    cases a <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, wRole, rolePcs,
      Bool.or_false] at hs ⊢ <;> (revert hs; decide +kernel)

/-- Two synchronizing states at one position are of one role. -/
theorem role_eq {s s' : WComp.WSt} {t t' : WComp.WSt} (hs : wSy s = true) (hs' : wSy s' = true)
    (hn : WComp.next L g s e = some (some t)) (hn' : WComp.next L h s' e' = some (some t'))
    (hpc : WComp.pc s = WComp.pc s') : wRole s = wRole s' := by
  by_contra hne
  have h1 := pc_mem hs hn
  have h2 := pc_mem hs' hn'
  rw [← hpc] at h2
  exact rolePcs_disj (wRole s) (wRole_lt s) (wRole s') (wRole_lt s') hne _ h1 h2

/-! ### The roles' last states return to the dispatch loop -/

theorem sy_loader {d : Loader.D} {P : Loader.Pro} (hs : wSy (.loader d P) = true) :
    syPc d.site.pc = true := by
  simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false, syAt, Bool.and_eq_true] at hs
  exact hs.1

theorem sy_mma {d : Mma.D} {P : Loader.Pro} (hs : wSy (.mma d P) = true) :
    syPc d.site.pc = true := by
  simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false, syAt, Bool.and_eq_true] at hs
  exact hs.1

theorem loader_sm {a b : Loader.Site} (hs' : syPc b.pc = true) (hpc : a.pc = b.pc)
    (h : a = .setMaxInc) : b = .setMaxInc := by
  subst h
  cases b <;> first | rfl | (exfalso; revert hs' hpc; decide +kernel)

theorem mma_sm {a b : Mma.Site} (hs' : syPc b.pc = true) (hpc : a.pc = b.pc)
    (h : a = .setMaxRegInc) : b = .setMaxRegInc := by
  subst h
  cases b <;> first
    | rfl
    | (exfalso; revert hs' hpc; decide +kernel)
    | (exfalso; rename_i j; revert hs' hpc j; decide +kernel)

theorem step_Lw {d d' : Loader.D} {P P' : Loader.Pro} {t t' : WComp.WSt}
    (hs : wSy (.loader d P) = true) (hs' : wSy (.loader d' P') = true)
    (hpc : d.site.pc = d'.site.pc)
    (ha : LdAgree d d')
    (hn : WComp.next L g (.loader d P) e = some (some t))
    (hn' : WComp.next L h (.loader d' P') e' = some (some t')) : wKey L g t = wKey L h t' := by
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
    rfl
  · have hl' : d'.site ≠ .setMaxInc := fun h' => hl (loader_sm hs0 hpc.symm h')
    rw [next_loader hl] at hn
    rw [next_loader hl'] at hn'
    obtain ⟨t0, ht0, rfl⟩ := mapInv hn
    obtain ⟨t0', ht0', rfl⟩ := mapInv hn'
    exact step_L hs0 hs0' hpc ha ht0 ht0'

theorem step_Mw {d d' : Mma.D} {P P' : Loader.Pro} {t t' : WComp.WSt}
    (hs : wSy (.mma d P) = true) (hs' : wSy (.mma d' P') = true)
    (hpc : d.site.pc = d'.site.pc)
    (ha : d.site.isSkip = false ∧ d'.site.isSkip = false ∧
      (d.site = .bar0 → (Mma.start d).site = (Mma.start d').site) ∧
      (d.site = .qkElect → (Mma.afterQk d).site = (Mma.afterQk d').site) ∧
      (d.site = .pvElect → (Mma.iterNext d).site = (Mma.iterNext d').site))
    (hn : WComp.next L g (.mma d P) e = some (some t))
    (hn' : WComp.next L h (.mma d' P') e' = some (some t')) : wKey L g t = wKey L h t' := by
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
    rfl
  · have hl' : d'.site ≠ .setMaxRegInc := fun h' => hl (mma_sm hs0 hpc.symm h')
    rw [next_mma hl] at hn
    rw [next_mma hl'] at hn'
    obtain ⟨t0, ht0, rfl⟩ := mapInv hn
    obtain ⟨t0', ht0', rfl⟩ := mapInv hn'
    exact step_M hs0 hs0' hpc ha ht0 ht0'

/-- **Two lanes' synchronizing states of one key have successors of one key when they agree
(`WAgree`).** -/
theorem w_step {s s' t t' : WComp.WSt} (_hw : SameWarp L g h) (hs : wSy s = true)
    (hs' : wSy s' = true) (hk : wKey L g s = wKey L h s') (ha : WAgree L g h s s' e e')
    (hn : WComp.next L g s e = some (some t)) (hn' : WComp.next L h s' e' = some (some t')) :
    wKey L g t = wKey L h t' := by
  have hpc : WComp.pc s = WComp.pc s' := (w_sy_key hs).symm.trans (hk.trans (w_sy_key hs'))
  have hr := role_eq hs hs' hn hn' hpc
  cases s <;> cases s' <;> try (simp [wRole] at hr; done)
  · exact step_W hs hs' hpc ha hn hn'
  · exact step_I hpc hn hn'
  · exact step_Lw hs hs' hpc ha hn hn'
  · exact step_Mw hs hs' hpc ha hn hn'
  · exact step_X hn hn'

end
end PTX.Kernels.InklingRelDecode.Proof.Lk
