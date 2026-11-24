-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LkEpi
public import Kernels.InklingRelDecode.Proof.Thread.LkPro

@[expose] public section

/-!
# Warp lockstep: the softmax region

The region's loop runs, in execution order, the preload and the bias loads (silent), the `s_ready`
poll (silent), the `shfl`/`tcgen05` events of the score stage, the exchanges of the rescale test,
the rescale (when the minimum of `alpha` is below 1) and the `P` store. Its key is the next
synchronizing position and three control numbers: `num_iters` (`%r26`), the loop counter `i` and
`%r25` (whose sign decides the epilogue's zero-iteration branch). The counter is the one the
state will have at the next synchronizing state (`arrive` has already counted the iteration).
Three silent sites leave for the epilogue when the counter reaches `num_iters`: the last preload,
the arrival, and (as sync states) `bar0` and `bar21`; the key of the leaving state is the key of the
epilogue's first state (`exitKey`).

Branches that depend on the thread only (the masked loads, lane 0's arrival) reach the same next
synchronizing state. The two branches that depend on a value are the first-iteration test at
`shfl6` (the counter, in the key) and the lazy-rescale test at `shfl12`
(`min(alpha) >= 1`: `D.p170`), whose agreement across the lanes of a warp is `SmAgree`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

/-- `%p173`: `num_iters < 1` as a signed 32-bit comparison. -/
def skipOf (r25 : Nat) : Bool := decide (toSigned 32 (BitVec.ofNat 64 r25) < 1)

/-- The key of the epilogue's first state, reached from the loop's exit at thread `g`. -/
def exitKey (L : Launch) (g : Nat) (r25 : Nat) : Key :=
  (if skipOf r25 then keyPc Epi.Site.bar1.pc 0 else keyPc Epi.Site.shfl.pc 0,
    if skipOf r25 then 1 else 0, if g % L.block < 32 then 1 else 0, 0)

/-- The key of a softmax state, from its site and its numbers `num_iters`, `i`, `%r25`. -/
def smKeyOf (L : Launch) (g : Nat) (s : Sm.Site) (r26 i r25 : Nat) : Key :=
  match s with
  | .pre _ => if r26 = i then exitKey L g r25 else (keyPc Sm.Site.shfl4.pc 0, r26, i, r25)
  | .arrive => if r26 = i + 1 then exitKey L g r25 else (keyPc Sm.Site.shfl4.pc 0, r26, i + 1, r25)
  | s => (keyPc s.pc 0, r26, i, r25)

/-- The key of a softmax state. -/
def smKey (L : Launch) (g : Nat) (d : Sm.D) : Key := smKeyOf L g d.site d.e.r26 d.i d.e.r25

/-- The state's event is synchronizing. -/
def smSy (d : Sm.D) : Bool := syAt d.site.pc 0

theorem pre_notSy : ∀ j : Fin 64, syAt (Sm.Site.pre j).pc 0 = false := by decide +kernel

theorem nxt_notSy : ∀ j : Fin 64, syAt (Sm.Site.nxt j).pc 0 = false := by decide +kernel

theorem sm_sy_key (L : Launch) (g : Nat) {d : Sm.D} (h : smSy d = true) :
    (smKey L g d).1 = d.site.pc := by
  obtain ⟨s, e, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  simp only [smSy] at h
  cases s <;> simp only [smKey, smKeyOf] <;>
    first
    | (exfalso; revert h; decide +kernel)
    | (revert h; decide +kernel)
    | (rename_i j; first | (have := pre_notSy j; simp_all) | (have := nxt_notSy j; simp_all))

/-- The key of a default-partition state. -/
def dKey (L : Launch) (g : Nat) : DComp.St → Key
  | .dstart d => dsKey d
  | .pro d => kOf (proKey L g d)
  | .sm d => smKey L g d
  | .epi d => epKey d

theorem epKey_entry (L : Launch) (g : Nat) (e : Sm.Ent) (i : Br.In)
    (hp3 : i.p3 = decide (g % L.block < 32)) (hsk : i.skip = skipOf e.r25) :
    epKey (if i.skip = true then Epi.D.startSk (Br.prm i) else Epi.D.start (Br.prm i)) =
      exitKey L g e.r25 := by
  simp only [Epi.D.startSk, Epi.D.start, Epi.D.entry, hsk, exitKey, epKey, epK, Br.prm, hp3]
  cases skipOf e.r25 <;> by_cases h : g % L.block < 32 <;> simp [h]

/-- **The loop's exit from a silent state** has the key of the state. -/
theorem sm_leaves_key {L : Launch} {g : Nat} {d : Sm.D} {e : Event}
    (hl : DComp.leaves L g d e) (hs : smSy d = false) :
    exitKey L g d.e.r25 = smKey L g d := by
  obtain ⟨st, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  simp only [smSy] at hs
  revert hs hl
  cases st <;> simp only [DComp.leaves] <;>
    first
    | (intro hl hs; exact absurd hl id)
    | (intro hl hs; exfalso; revert hs; decide +kernel)
    | (intro hl hs; simp [smKey, smKeyOf, hl.2.2])
    | (intro hl hs; simp [smKey, smKeyOf, hl.2])

theorem nxt_succ_key : ∀ j : Fin 64, ∀ hj : j.val + 1 < 64,
    keyPc (Sm.Site.nxt ⟨j.val + 1, hj⟩).pc 0 = keyPc (Sm.Site.nxt j).pc 0 := by
  decide +kernel

theorem nxt_last_key : ∀ j : Fin 64, ¬ (j.val + 1 < 64) →
    keyPc Sm.Site.waitS.pc 0 = keyPc (Sm.Site.nxt j).pc 0 := by
  decide +kernel

theorem toBar20_fields {d d' : Sm.D} (h : Sm.toBar20 d = some (some d')) :
    d'.site = .bar20 ∧ d'.e = d.e ∧ d'.i = d.i := by
  unfold Sm.toBar20 at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl⟩
  · simp at h

/-- **A silent step of the loop's own code keeps the key.** -/
theorem sm_next_silent {L : Launch} {g : Nat} {d d' : Sm.D} {e : Event}
    (h : Sm.next L g d e = some (some d')) (hs : smSy d = false) :
    smKey L g d' = smKey L g d := by
  obtain ⟨st, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  simp only [smSy] at hs
  cases st <;> first
    | (exfalso; revert hs; decide +kernel)
    | (simp only [Sm.next, Sm.afterSetup, Sm.afterArrive] at h <;>
       (repeat' split at h) <;>
       first
       | (simp at h; done)
       | (obtain ⟨h1, h2, h3⟩ := toBar20_fields h; exfalso; revert hs; decide +kernel)
       | (simp only [Option.some.injEq] at h; subst h
          simp only [smKey, smKeyOf] <;> (repeat' split) <;>
            (try simp only [Prod.mk.injEq, and_true]) <;>
            first
            | decide +kernel
            | (revert hs; decide +kernel)
            | (exact nxt_succ_key _ ‹_›)
            | (exact nxt_last_key _ ‹_›)
            | simp_all))

/-- A successor of `none` or `some none` under `Option.map` stays so. -/
theorem map_inv {α β : Type} {f : α → β} {x : Option (Option α)} {b : β}
    (h : x.map (Option.map f) = some (some b)) : ∃ a, x = some (some a) ∧ f a = b := by
  cases x with
  | none => simp at h
  | some o =>
    cases o with
    | none => simp at h
    | some a => exact ⟨a, rfl, by simpa using h⟩

/-- **A silent step of the softmax region keeps the key.** -/
theorem sm_silent {L : Launch} {g : Nat} {d : Sm.D} {e : Event} {t : DComp.St}
    (h : DComp.smNext L g d e = some (some t)) (hs : smSy d = false) :
    dKey L g t = smKey L g d := by
  unfold DComp.smNext at h
  split at h
  · rename_i hl
    unfold DComp.exitNext at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact (epKey_entry L g d.e (DComp.exitIn L g d) rfl rfl).trans (sm_leaves_key hl hs)
    · simp at h
  · obtain ⟨a, ha, rfl⟩ := map_inv h
    simp only [dKey]
    exact sm_next_silent ha hs

/-! ### Two lanes at one synchronizing site -/

/-- The softmax region's sites other than the two families of bias loads. -/
def smSites : List Sm.Site :=
  [.setMaxReg, .bar0, .waitS, .shfl4, .ldS, .waitLd, .shfl5, .shfl6, .bar22, .shfl7, .shfl8,
    .shfl9, .shfl10, .store10, .bar23, .ldL, .shfl11, .shfl12, .waitO, .ldO, .waitLdO, .bar24,
    .stO, .waitStO, .bar20, .tmemSt, .tmemWait, .bar21, .arrive]

theorem mem_smSites {s : Sm.Site} (h : syAt s.pc 0 = true) : s ∈ smSites := by
  cases s <;> first
    | (simp [smSites]; done)
    | (rename_i j; first | (have := pre_notSy j; simp_all) | (have := nxt_notSy j; simp_all))

theorem smSites_inj : ∀ s ∈ smSites, ∀ s' ∈ smSites, syAt s.pc 0 = true → syAt s'.pc 0 = true →
    s.pc = s'.pc → s = s' := by
  decide +kernel

theorem sm_site_eq {d d' : Sm.D} (hs : smSy d = true) (hs' : smSy d' = true)
    (h : d.site.pc = d'.site.pc) : d.site = d'.site :=
  smSites_inj _ (mem_smSites hs) _ (mem_smSites hs') hs hs' h

/-- The step from `d` along `e` leaves for `bar20` (the lazy-rescale test found
`min(alpha) >= 1`). -/
def BranchBar20 (L : Launch) (g : Nat) (d : Sm.D) (e : Event) : Prop :=
  ∃ t, Sm.next L g d e = some (some t) ∧ t.site = .bar20

/-- What two lanes' values agree on at a softmax state: at `shfl12` both take the lazy-rescale
branch or neither does (`min(alpha) >= 1`, `D.p170`, computed from the words the last exchange
returned). -/
def SmAgree (L : Launch) (g h : Nat) (d d' : Sm.D) (e e' : Event) : Prop :=
  d.site = .shfl12 → (BranchBar20 L g d e ↔ BranchBar20 L h d' e')

theorem shfl12_next {L : Launch} {g : Nat} {d t : Sm.D} {e : Event}
    (h : Sm.next L g d e = some (some t)) (hs : d.site = .shfl12) :
    (t.site = .bar20 ∨ t.site = .ldO) ∧ t.e = d.e ∧ t.i = d.i := by
  obtain ⟨st, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  simp only [] at hs
  subst hs
  simp only [Sm.next] at h
  (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨Or.inr rfl, rfl, rfl⟩)
    | (obtain ⟨h1, h2, h3⟩ := toBar20_fields h; exact ⟨Or.inl h1, h2, h3⟩)

/-- **Two lanes at the lazy-rescale test have successors with one key**, given that both take the
same branch. -/
theorem sm_shfl12_step {L : Launch} {g h : Nat} {d d' : Sm.D} {t t' : Sm.D}
    (hs : d.site = .shfl12) (hs' : d'.site = .shfl12) (h1 : d.e.r26 = d'.e.r26)
    (h2 : d.i = d'.i) (h3 : d.e.r25 = d'.e.r25) (hag : t.site = .bar20 ↔ t'.site = .bar20)
    (ht : (t.site = .bar20 ∨ t.site = .ldO) ∧ t.e = d.e ∧ t.i = d.i)
    (ht' : (t'.site = .bar20 ∨ t'.site = .ldO) ∧ t'.e = d'.e ∧ t'.i = d'.i) :
    smKey L g t = smKey L h t' := by
  obtain ⟨hs1, he1, hi1⟩ := ht
  obtain ⟨hs2, he2, hi2⟩ := ht'
  have _ := hs
  have _ := hs'
  simp only [smKey, he1, he2, hi1, hi2]
  rcases hs1 with h4 | h4 <;> rcases hs2 with h5 | h5 <;>
    simp_all [smKeyOf]

/-- **Two lanes at one synchronizing site of the loop's own code have successors with one key**,
given one key, and the agreement on the lazy-rescale decision. -/
theorem sm_next_step {L : Launch} {g h : Nat} (hw : SameWarp L g h) {d d' : Sm.D}
    {e e' : Event} {t t' : Sm.D} (hs : smSy d = true) (hs' : smSy d' = true)
    (hk : smKey L g d = smKey L h d')
    (ha : SmAgree L g h d d' e e') (hn : Sm.next L g d e = some (some t))
    (hn' : Sm.next L h d' e' = some (some t')) : smKey L g t = smKey L h t' := by
  have hsite := sm_site_eq hs hs' (by rw [← sm_sy_key L g hs, ← sm_sy_key L h hs', hk])
  have hk' := hk
  simp only [smKey] at hk'
  have hw2 : g % L.block / 32 = h % L.block / 32 := hw.2
  by_cases hsh : d.site = .shfl12
  · have hsh' : d'.site = .shfl12 := by rw [← hsite]; exact hsh
    have hag : t.site = .bar20 ↔ t'.site = .bar20 := by
      have := ha hsh
      simp only [BranchBar20, hn, hn', Option.some.injEq, exists_eq_left'] at this
      exact this
    have hk2 : d.e.r26 = d'.e.r26 ∧ d.i = d'.i ∧ d.e.r25 = d'.e.r25 := by
      rw [hsh, hsh'] at hk'
      simp only [smKeyOf, Prod.mk.injEq] at hk'
      exact ⟨hk'.2.1, hk'.2.2.1, hk'.2.2.2⟩
    exact sm_shfl12_step hsh hsh' hk2.1 hk2.2.1 hk2.2.2 hag (shfl12_next hn hsh)
      (shfl12_next hn' hsh')
  obtain ⟨st, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  obtain ⟨st', e0', i', m', l', cw', cv', w', v', sv', pf', stg'⟩ := d'
  simp only [] at hsite hsh
  subst hsite
  simp only [smSy] at hs
  cases st <;> first
    | (exfalso; revert hs; decide +kernel)
    | exact absurd rfl hsh
    | (simp [pre_notSy] at hs)
    | (simp [nxt_notSy] at hs)
    | (simp only [smKey, smKeyOf, Prod.mk.injEq] at hk
       obtain ⟨-, h1, h2, h3⟩ := hk
       simp only [Sm.next, Sm.afterSetup, Sm.afterArrive, Sm.D.afterSum, Sm.D.afterMax,
         Sm.D.afterMaxT] at hn hn'
       (repeat' split at hn) <;> (repeat' split at hn') <;>
       first
       | (simp at hn; done)
       | (simp at hn'; done)
       | ((try simp only [Option.some.injEq] at hn hn'); subst hn hn'
          simp only [smKey, smKeyOf, exitKey] <;> (repeat' split) <;>
            (try simp only [Prod.mk.injEq, and_true]) <;>
            first
            | decide +kernel
            | (revert hs; decide +kernel)
            | (exfalso; omega)
            | (clear hw hw2 hk' ha; simp_all; done)
            | (clear hw hw2 hk' ha; simp_all; decide +kernel))
       | (simp_all; done)
       | (obtain ⟨h4, h5, h6⟩ := toBar20_fields hn; obtain ⟨h7, h8, h9⟩ := toBar20_fields hn'
          simp only [smKey, smKeyOf, h4, h7, h5, h8, h6, h9]; simp_all))

/-- Two synchronizing softmax states with one key are at one site with equal numbers. -/
theorem sm_key_comps {L : Launch} {g h : Nat} {d d' : Sm.D} (hs : smSy d = true)
    (hs' : smSy d' = true) (hk : smKey L g d = smKey L h d') :
    d.site = d'.site ∧ d.e.r26 = d'.e.r26 ∧ d.i = d'.i ∧ d.e.r25 = d'.e.r25 := by
  have hsite := sm_site_eq hs hs' (by rw [← sm_sy_key L g hs, ← sm_sy_key L h hs', hk])
  refine ⟨hsite, ?_⟩
  obtain ⟨st, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  obtain ⟨st', e0', i', m', l', cw', cv', w', v', sv', pf', stg'⟩ := d'
  simp only [] at hsite
  subst hsite
  simp only [smSy] at hs
  cases st <;> first
    | (exfalso; revert hs; decide +kernel)
    | (simp [pre_notSy] at hs)
    | (simp [nxt_notSy] at hs)
    | (simp only [smKey, smKeyOf, Prod.mk.injEq] at hk
       exact ⟨hk.2.1, hk.2.2.1, hk.2.2.2⟩)

theorem exit_key {L : Launch} {g : Nat} {d : Sm.D} {t : DComp.St}
    (h : DComp.exitNext L g d = some (some t)) : dKey L g t = exitKey L g d.e.r25 := by
  unfold DComp.exitNext at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact epKey_entry L g d.e (DComp.exitIn L g d) rfl rfl
  · simp at h

/-- **Two lanes at one synchronizing site of the softmax region have successors with one key.** -/
theorem sm_step {L : Launch} {g h : Nat} (hw : SameWarp L g h) {d d' : Sm.D} {e e' : Event}
    {t t' : DComp.St} (hs : smSy d = true) (hs' : smSy d' = true)
    (hk : smKey L g d = smKey L h d') (ha : SmAgree L g h d d' e e')
    (hn : DComp.smNext L g d e = some (some t)) (hn' : DComp.smNext L h d' e' = some (some t')) :
    dKey L g t = dKey L h t' := by
  obtain ⟨hsite, h1, h2, h3⟩ := sm_key_comps hs hs' hk
  have hw2 : g % L.block / 32 = h % L.block / 32 := hw.2
  unfold DComp.smNext at hn hn'
  split at hn <;> split at hn'
  · rename_i hl hl'
    rw [exit_key hn, exit_key hn', h3]
    simp only [exitKey]
    (repeat' split) <;> first | rfl | (exfalso; omega)
  · rename_i hl hl'
    rw [exit_key hn]
    obtain ⟨a, ha', rfl⟩ := map_inv hn'
    simp only [dKey]
    obtain ⟨st, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
    obtain ⟨st', e0', i', m', l', cw', cv', w', v', sv', pf', stg'⟩ := d'
    simp only [] at hsite h1 h2 h3
    subst hsite
    simp only [smSy] at hs
    cases st <;> first
      | (exfalso; revert hs; decide +kernel)
      | (simp [pre_notSy] at hs)
      | (simp [nxt_notSy] at hs)
      | (simp only [DComp.leaves] at hl hl' <;>
         simp only [Sm.next, Sm.afterSetup, Sm.afterArrive] at ha' <;>
         (repeat' split at ha') <;>
         first
         | (simp at ha'; done)
         | (simp only [Option.some.injEq] at ha'; subst ha'
            simp only [smKey, smKeyOf, exitKey] <;> (repeat' split) <;>
              first | (exfalso; omega) | (clear hw hw2 hk ha hn; simp_all; done)))
  · rename_i hl hl'
    rw [exit_key hn']
    obtain ⟨a, ha', rfl⟩ := map_inv hn
    simp only [dKey]
    obtain ⟨st, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
    obtain ⟨st', e0', i', m', l', cw', cv', w', v', sv', pf', stg'⟩ := d'
    simp only [] at hsite h1 h2 h3
    subst hsite
    simp only [smSy] at hs
    cases st <;> first
      | (exfalso; revert hs; decide +kernel)
      | (simp [pre_notSy] at hs)
      | (simp [nxt_notSy] at hs)
      | (simp only [DComp.leaves] at hl hl' <;>
         simp only [Sm.next, Sm.afterSetup, Sm.afterArrive] at ha' <;>
         (repeat' split at ha') <;>
         first
         | (simp at ha'; done)
         | (simp only [Option.some.injEq] at ha'; subst ha'
            simp only [smKey, smKeyOf, exitKey] <;> (repeat' split) <;>
              first | (exfalso; omega) | (clear hw hw2 hk ha hn'; simp_all; done)))
  · obtain ⟨a, ha', rfl⟩ := map_inv hn
    obtain ⟨b, hb', rfl⟩ := map_inv hn'
    exact sm_next_step hw hs hs' hk ha ha' hb'

end
end PTX.Kernels.InklingRelDecode.Proof.Lk
