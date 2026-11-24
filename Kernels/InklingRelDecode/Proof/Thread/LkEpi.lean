-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LkBase

@[expose] public section

/-!
# Warp lockstep: the common start and the epilogue

A key is a program position and three control numbers (`Key`): the softmax region's `num_iters`,
its loop counter and `%r25`, in the epilogue the flags of the zero-iteration branch and of the
warp that frees the Tensor Memory. The common start and the epilogue run forward, so the position
of a state's key is the next synchronizing position at or after its own. The poll of `o_final`
(`Epi.Site.wait`) steers the successor by `d.sk` (`num_iters < 1`: the stores follow at once);
its key is the key of the branch taken. The common start's `bar.sync 0` after the base-word read
and the epilogue's last barrier steer by the warp (`g % block < 32`, `d.pr.p3`), which the keys
carry.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

/-- A key: the position of the next synchronizing state and three control numbers. -/
abbrev Key := Nat × Nat × Nat × Nat

/-- The key of a state with no control numbers. -/
def kOf (pc : Nat) : Key := (pc, 0, 0, 0)

/-! ### The common start -/

/-- The key of a common-start state: its position, past the allocation's second step. -/
def dsKey (d : DStart.D) : Key := kOf (keyPc d.site.pc d.site.sub)

/-- The state's event is synchronizing. -/
def dsSy (d : DStart.D) : Bool := syAt d.site.pc d.site.sub

theorem ds_sy_key {d : DStart.D} (h : dsSy d = true) : (dsKey d).1 = d.site.pc := by
  obtain ⟨s, tm⟩ := d
  simp only [dsSy] at h
  simp only [dsKey, kOf]
  cases s <;> first | (exfalso; revert h; decide +kernel) | (revert h; decide +kernel)

theorem ds_silent {L : Launch} {g : Nat} {d d' : DStart.D} {e : Event}
    (h : DStart.next L g d e = some (some d')) (hs : dsSy d = false) : dsKey d' = dsKey d := by
  obtain ⟨s, tm⟩ := d
  simp only [dsSy] at hs
  cases s <;> simp only [DStart.next] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; simp only [dsKey, kOf]
       (repeat' split) <;> (revert hs; decide +kernel))

theorem ds_site_eq {d d' : DStart.D} (hs : dsSy d = true) (hs' : dsSy d' = true)
    (h : d.site.pc = d'.site.pc) : d.site = d'.site := by
  obtain ⟨s, tm⟩ := d
  obtain ⟨s', tm'⟩ := d'
  simp only [dsSy] at hs hs'
  simp only [] at h ⊢
  revert hs hs' h
  cases s <;> cases s' <;> first
    | (intro _ _ _; rfl)
    | (intro hs hs' h; exfalso; revert hs hs' h; decide +kernel)

theorem ds_step {L : Launch} {g h : Nat} (hw : SameWarp L g h) {d d' : DStart.D}
    {e e' : Event} {t t' : DStart.D} (hs : dsSy d = true) (hs' : dsSy d' = true)
    (hk : dsKey d = dsKey d') (hn : DStart.next L g d e = some (some t))
    (hn' : DStart.next L h d' e' = some (some t')) : dsKey t = dsKey t' := by
  have hpc : d.site.pc = d'.site.pc := by
    rw [← ds_sy_key hs, ← ds_sy_key hs', hk]
  have hsite := ds_site_eq hs hs' hpc
  have hw2 : g % L.block / 32 = h % L.block / 32 := hw.2
  obtain ⟨s, tm⟩ := d
  obtain ⟨s', tm'⟩ := d'
  simp only [] at hsite
  subst hsite
  simp only [dsSy] at hs
  revert hs
  cases s <;> first | (intro hs; exfalso; revert hs; decide +kernel) | intro hs <;>
    simp only [DStart.next] at hn hn' <;> (repeat' split at hn) <;> (repeat' split at hn') <;>
    first
    | (simp at hn; done)
    | (simp at hn'; done)
    | (simp only [Option.some.injEq] at hn hn'; subst hn hn'; simp only [dsKey, kOf] <;>
       (repeat' split) <;> first | (revert hs; decide +kernel) | omega)

/-! ### The epilogue -/

/-- The position of the next synchronizing state of an epilogue state. The poll of `o_final`
leaves for the stores (`num_iters < 1`) or the broadcast. -/
def epK (d : Epi.D) : Nat :=
  if d.site = .wait then (if d.sk then keyPc Epi.Site.bar1.pc 0 else keyPc Epi.Site.shfl.pc 0)
  else keyPc d.site.pc 0

/-- The key of an epilogue state: the position, the zero-iteration flag and the flag of the
warp that frees the Tensor Memory. -/
def epKey (d : Epi.D) : Key := (epK d, if d.sk then 1 else 0, if d.pr.p3 then 1 else 0, 0)

/-- The state's event is synchronizing. -/
def epSy (d : Epi.D) : Bool := syAt d.site.pc 0

theorem ep_sy_key {d : Epi.D} (h : epSy d = true) : (epKey d).1 = d.site.pc := by
  obtain ⟨s, pr, o, sk⟩ := d
  simp only [epSy] at h
  cases s <;> simp only [epKey, epK, reduceCtorEq, ↓reduceIte] <;>
    first
    | (exfalso; revert h; decide +kernel)
    | (revert h; decide +kernel)
    | (rename_i k; exfalso; revert h k; decide +kernel)

theorem stO_succ_key : ∀ k : Fin 64, ∀ hk : k.val + 1 < 64,
    keyPc (Epi.Site.stO ⟨k.val + 1, hk⟩).pc 0 = keyPc (Epi.Site.stO k).pc 0 := by
  decide +kernel

theorem stO_last_key : ∀ k : Fin 64, ¬ (k.val + 1 < 64) →
    keyPc Epi.Site.bar1.pc 0 = keyPc (Epi.Site.stO k).pc 0 := by
  decide +kernel

theorem ep_silent {d d' : Epi.D} {e : Event} (h : Epi.next d e = some (some d'))
    (hs : epSy d = false) : epKey d' = epKey d := by
  obtain ⟨s, pr, o, sk⟩ := d
  simp only [epSy] at hs
  cases s <;> simp only [Epi.next] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h
       simp only [epKey, epK, Epi.D.stores, Epi.stNext] <;> (repeat' split) <;>
         first
         | (revert hs; decide +kernel)
         | (simp only [Prod.mk.injEq, and_true]
            first | exact stO_last_key _ ‹_› | exact stO_succ_key _ ‹_›)
         | (simp_all; done))

theorem stO_notSy : ∀ k : Fin 64, syAt (Epi.Site.stO k).pc 0 = false := by decide +kernel

/-- The epilogue's sites other than the stores of `OPart`. -/
def epSites : List Epi.Site :=
  [.wait, .shfl, .ld, .waitLd, .stLse, .bar1, .setMaxInc, .stTab, .bar2, .bar3, .dealloc, .exit]

theorem mem_epSites {s : Epi.Site} (h : syAt s.pc 0 = true) : s ∈ epSites := by
  cases s <;> first
    | (simp [epSites]; done)
    | (rename_i k; have := stO_notSy k; simp_all)

theorem epSites_inj : ∀ s ∈ epSites, ∀ s' ∈ epSites, syAt s.pc 0 = true → syAt s'.pc 0 = true →
    s.pc = s'.pc → s = s' := by
  decide +kernel

theorem ep_site_eq {d d' : Epi.D} (hs : epSy d = true) (hs' : epSy d' = true)
    (h : d.site.pc = d'.site.pc) : d.site = d'.site :=
  epSites_inj _ (mem_epSites hs) _ (mem_epSites hs') hs hs' h

theorem ep_step {L : Launch} {g h : Nat} (_hw : SameWarp L g h) {d d' : Epi.D} {e e' : Event}
    {t t' : Epi.D} (hs : epSy d = true) (hs' : epSy d' = true) (hk : epKey d = epKey d')
    (hn : Epi.next d e = some (some t)) (hn' : Epi.next d' e' = some (some t')) :
    epKey t = epKey t' := by
  have hpc : d.site.pc = d'.site.pc := by
    have := congrArg Prod.fst hk
    rw [← ep_sy_key hs, ← ep_sy_key hs']
    exact this
  have hsite := ep_site_eq hs hs' hpc
  have hsk : d.sk = d'.sk := by
    have := (congrArg (fun k => k.2.1) hk)
    simp only [epKey] at this
    cases h1 : d.sk <;> cases h2 : d'.sk <;> simp_all
  have hp3 : d.pr.p3 = d'.pr.p3 := by
    have := (congrArg (fun k => k.2.2.1) hk)
    simp only [epKey] at this
    cases h1 : d.pr.p3 <;> cases h2 : d'.pr.p3 <;> simp_all
  obtain ⟨s, pr, o, sk⟩ := d
  obtain ⟨s', pr', o', sk'⟩ := d'
  simp only [] at hsite hsk hp3
  subst hsite hsk
  simp only [epSy] at hs
  revert hs
  cases s <;> first | (intro hs; exfalso; revert hs; decide +kernel) | intro hs <;>
    simp only [Epi.next] at hn hn' <;> (repeat' split at hn) <;> (repeat' split at hn') <;>
    first
    | (simp at hn; done)
    | (simp at hn'; done)
    | (simp only [Option.some.injEq] at hn hn'; subst hn hn'
       simp only [epKey, epK, Epi.D.stores, Epi.stNext] <;>
       (repeat' split) <;> first | (revert hs; decide +kernel) | simp_all)

end
end PTX.Kernels.InklingRelDecode.Proof.Lk
