-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LkSm

@[expose] public section

/-!
# Warp lockstep: the default partition's composed machine

The keys of the four regions (`dsKey`, `proKey`, `smKey`, `epKey`) put together (`dKey`), with
the transitions between the regions: the common start's last site hands over to the prologue's
first (`setmaxnreg.inc`, position 27 in both), the prologue's last site (`barrier.sync 1`) to the
softmax region's first state, whose numbers are the launch's, and the loop's exit (`exitKey`) to
the epilogue's first state.

`dAgree` is what two lanes must agree on at synchronizing states for their successors to have one
key: the prologue's three guards (`ProAgree`) and the lazy-rescale decision (`SmAgree`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

/-- The state's event is synchronizing (the common start's last site is the prologue's first
state, never a state of the common start). -/
def dSy : DComp.St → Bool
  | .dstart d => dsSy d && decide (d.site ≠ DStart.Site.toProA)
  | .pro d => proSy d
  | .sm d => smSy d
  | .epi d => epSy d

/-- What two lanes agree on at synchronizing states of one region. -/
def dAgree (L : Launch) (g h : Nat) : DComp.St → DComp.St → Event → Event → Prop
  | .pro d, .pro d', _, _ => ProAgree L g h d d'
  | .sm d, .sm d', e, e' => SmAgree L g h d d' e e'
  | _, _, _, _ => True

/-- The position of a default-partition state's key. -/
theorem d_sy_key (L : Launch) (g : Nat) {s : DComp.St} (h : dSy s = true) :
    (dKey L g s).1 = DComp.pc s := by
  cases s with
  | dstart d =>
    simp only [dSy, Bool.and_eq_true] at h
    exact ds_sy_key h.1
  | pro d => exact pro_sy_key L g h
  | sm d => exact sm_sy_key L g h
  | epi d => exact ep_sy_key h

/-! ### The regions' sites are in disjoint ranges of positions -/

theorem dstart_pc_lt_site (s : DStart.Site) (h1 : syAt s.pc s.sub = true)
    (h2 : s ≠ DStart.Site.toProA) : s.pc < 20 := by
  revert h1 h2
  cases s <;> decide +kernel

theorem dstart_pc_lt {d : DStart.D} (h : dSy (.dstart d) = true) : d.site.pc < 20 := by
  simp only [dSy, dsSy, Bool.and_eq_true, decide_eq_true_eq] at h
  exact dstart_pc_lt_site _ h.1 h.2

theorem pc_range_nat : ∀ n < 182, syAt (ProA.Site.ofNat n).pc (ProA.Site.ofNat n).sub = true →
    27 ≤ (ProA.Site.ofNat n).pc ∧ (ProA.Site.ofNat n).pc < 574 := by
  decide +kernel

theorem pro_pc_range {d : ProA.D} (h : proSy d = true) : 27 ≤ d.site.pc ∧ d.site.pc < 574 := by
  have := pc_range_nat d.site.ctorIdx (ctorIdx_lt _)
  rw [ofNat_ctorIdx] at this
  exact this h

theorem sm_pc_range : ∀ s ∈ smSites, syAt s.pc 0 = true → 574 ≤ s.pc ∧ s.pc < 2603 := by
  decide +kernel

theorem sm_pc_range' {d : Sm.D} (h : smSy d = true) : 574 ≤ d.site.pc ∧ d.site.pc < 2603 :=
  sm_pc_range _ (mem_smSites h) h

theorem ep_pc_range : ∀ s ∈ epSites, syAt s.pc 0 = true → 2603 ≤ s.pc := by
  decide +kernel

theorem ep_pc_lt : ∀ s ∈ epSites, s.pc < 100000 := by decide +kernel

theorem ep_pc_range' {d : Epi.D} (h : epSy d = true) : 2603 ≤ d.site.pc :=
  ep_pc_range _ (mem_epSites h) h

/-- A step of the common start, as a step of the composed machine, has the key of the common
start's successor. -/
theorem dstartMap_key (L : Launch) (g : Nat) (Q : Params) (a : DStart.D) :
    dKey L g (if a.site = DStart.Site.toProA then
        .pro (ProA.D.start (DStart.inh L g Q (ProA.shW a.w)) a.w)
      else .dstart a) = dsKey a := by
  split
  · rename_i h
    obtain ⟨s, tm⟩ := a
    simp only [] at h
    subst h
    exact rfl
  · rfl

theorem d_init {L : Launch} {g h : Nat} (Q : Params) (hw : SameWarp L g h) :
    dKey L g (DComp.code L g Q).init = dKey L h (DComp.code L h Q).init := by
  have hw2 : g % L.block / 32 = h % L.block / 32 := hw.2
  show dsKey (DStart.D.start L g) = dsKey (DStart.D.start L h)
  simp only [DStart.D.start]
  split <;> split <;> first | rfl | (exfalso; omega)

/-- **A silent step of the default partition's machine keeps the key.** -/
theorem d_silent {L : Launch} {g : Nat} {Q : Params} {s t : DComp.St} {e : Event}
    (h : DComp.next L g Q s e = some (some t)) (hs : dSy s = false) :
    dKey L g t = dKey L g s := by
  cases s with
  | dstart d =>
    simp only [DComp.next, DComp.dstartNext] at h
    obtain ⟨a, ha, rfl⟩ := map_inv h
    rw [dstartMap_key]
    by_cases hd : dsSy d = true
    · have hsite : d.site = DStart.Site.toProA := by
        by_contra hne
        simp [dSy, hd, hne] at hs
      obtain ⟨s0, tm⟩ := d
      simp only [] at hsite
      subst hsite
      simp [DStart.next] at ha
    · exact ds_silent ha (by simpa using hd)
  | pro d =>
    simp only [DComp.next, DComp.proNext] at h
    by_cases hb : d.site = ProA.Site.bar18
    · exfalso
      obtain ⟨s0, dt⟩ := d
      simp only [] at hb
      subst hb
      simp only [dSy, proSy] at hs
      revert hs
      decide +kernel
    · simp only [hb, ↓reduceIte] at h
      obtain ⟨a, ha, rfl⟩ := map_inv h
      exact congrArg (fun k => kOf k) (pro_silent ha hs)
  | sm d => exact sm_silent h hs
  | epi d =>
    simp only [DComp.next] at h
    obtain ⟨a, ha, rfl⟩ := map_inv h
    exact ep_silent ha hs

/-- The range of positions of the synchronizing states of a region. -/
def rangeOf : DComp.St → Nat × Nat
  | .dstart _ => (0, 20)
  | .pro _ => (27, 574)
  | .sm _ => (574, 2603)
  | .epi _ => (2603, 100000)

theorem d_pc_range {s : DComp.St} (h : dSy s = true) :
    (rangeOf s).1 ≤ DComp.pc s ∧ DComp.pc s < (rangeOf s).2 := by
  cases s with
  | dstart d => have := dstart_pc_lt h; simp only [rangeOf, DComp.pc]; omega
  | pro d => have := pro_pc_range h; simp only [rangeOf, DComp.pc]; omega
  | sm d => have := sm_pc_range' h; simp only [rangeOf, DComp.pc]; omega
  | epi d =>
    have := ep_pc_range' h
    have h2 : d.site.pc < 100000 := ep_pc_lt _ (mem_epSites h)
    simp only [rangeOf, DComp.pc]
    omega

theorem entOf_r26 (Q : Params) {L : Launch} {g h : Nat} (hc : g / L.block = h / L.block)
    (dt dt' : ProA.Dat) :
    (SmEntry.entOf Q L g dt).r26 = (SmEntry.entOf Q L h dt').r26 ∧
      (SmEntry.entOf Q L g dt).r25 = (SmEntry.entOf Q L h dt').r25 := by
  constructor <;> simp only [SmEntry.entOf, ProA.cta, hc]

/-- **Two lanes at one synchronizing state of the default partition's machine have successors
with one key**, given one key and what `dAgree` says. -/
theorem d_step {L : Launch} {g h : Nat} (Q : Params) (hw : SameWarp L g h) {s s' t t' : DComp.St}
    {e e' : Event} (hs : dSy s = true) (hs' : dSy s' = true) (hk : dKey L g s = dKey L h s')
    (ha : dAgree L g h s s' e e') (hn : DComp.next L g Q s e = some (some t))
    (hn' : DComp.next L h Q s' e' = some (some t')) : dKey L g t = dKey L h t' := by
  have hpc : DComp.pc s = DComp.pc s' := by rw [← d_sy_key L g hs, ← d_sy_key L h hs', hk]
  have r1 := d_pc_range hs
  have r2 := d_pc_range hs'
  cases s <;> cases s' <;> first
    | (exfalso; simp only [rangeOf, DComp.pc] at r1 r2 hpc; omega)
    | skip
  · -- both in the common start
    rename_i d d'
    simp only [DComp.next, DComp.dstartNext] at hn hn'
    obtain ⟨a, ha1, rfl⟩ := map_inv hn
    obtain ⟨b, hb1, rfl⟩ := map_inv hn'
    rw [dstartMap_key, dstartMap_key]
    simp only [dSy, Bool.and_eq_true] at hs hs'
    exact ds_step hw hs.1 hs'.1 hk ha1 hb1
  · -- both in the prologue
    rename_i d d'
    simp only [DComp.next, DComp.proNext] at hn hn'
    simp only [dAgree] at ha
    have hk' : proKey L g d = proKey L h d' := congrArg Prod.fst hk
    by_cases hb : d.site = ProA.Site.bar18
    · have hb' : d'.site = ProA.Site.bar18 := by
        have := pro_site_eq hs hs' (by rw [← pro_sy_key L g hs, ← pro_sy_key L h hs', hk'])
        rw [← this]; exact hb
      simp only [hb, hb', ↓reduceIte] at hn hn'
      split at hn <;> split at hn'
      · simp only [Option.some.injEq] at hn hn'
        subst hn hn'
        have hc : g / L.block = h / L.block := hw.1.2.2
        obtain ⟨c1, c2⟩ := entOf_r26 Q hc d.dt d'.dt
        simp only [dKey, smKey, smKeyOf, SmEntry.d0, c1, c2]
      all_goals simp_all
    · have hb' : ¬ d'.site = ProA.Site.bar18 := by
        intro hb''
        apply hb
        have := pro_site_eq hs hs' (by rw [← pro_sy_key L g hs, ← pro_sy_key L h hs', hk'])
        rw [this]; exact hb''
      simp only [hb, hb', ↓reduceIte] at hn hn'
      obtain ⟨a, ha1, rfl⟩ := map_inv hn
      obtain ⟨b, hb1, rfl⟩ := map_inv hn'
      exact congrArg (fun k => kOf k) (pro_step hs hs' hk' ha ha1 hb1)
  · -- both in the softmax region
    rename_i d d'
    simp only [dAgree] at ha
    exact sm_step hw hs hs' hk ha hn hn'
  · -- both in the epilogue
    rename_i d d'
    simp only [DComp.next] at hn hn'
    obtain ⟨a, ha1, rfl⟩ := map_inv hn
    obtain ⟨b, hb1, rfl⟩ := map_inv hn'
    exact ep_step hw hs hs' hk ha1 hb1

end
end PTX.Kernels.InklingRelDecode.Proof.Lk
