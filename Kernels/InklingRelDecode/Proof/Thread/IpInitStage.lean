-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ShapeBarOrd
public import Kernels.InklingRelDecode.Proof.Thread.LedgerB0

@[expose] public section

/-!
# The default partition's start and prologue as stages

The common start (`DStart`) and the prologue (`ProA`) of a default-partition thread never repeat a
site: every successor of `DStart.next` and of `ProA.next` is a later site (`pro_next_lt` is
`Bound.ProA.next_lt`, which this layer cannot import). Two measures follow.

* `stg`: the stage of a state, strictly increasing along the steps of the common start and of the
  prologue, non-decreasing after (the softmax region and the epilogue are one stage).
* `exb`: the *exact* number of barrier-0 events of the thread before the state's event, where it
  is known: 0 before the first `bar.sync 0`, 1 between the two, 2 at the other sites of the common
  start and at the prologue's sites up to its own `bar.sync 0, 128` (`ProA.Site.bar2`), 3 at the
  prologue's sites after it.

The closure `pro_next_le` (a successor of a site before `c` is at most `c`, for `c` the
elections, the proxy fence and `bar2`) lets a lemma over an execution find, from a state after
`bar2`, the earlier state at `bar2` and from a state after an election its elect event.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.IpInit
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {Q : Params}

/-! ### The prologue's sites -/

/-- **Every successor of the prologue is a later site.** -/
theorem pro_next_lt {d d' : ProA.D} {e : Event}
    (h : ProA.next L g d e = some (some d')) : d.site.ctorIdx < d'.site.ctorIdx := by
  obtain ⟨s, dt⟩ := d
  cases s <;> simp only [ProA.next] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; (try simp only [ProA.qSite])
       (repeat' split) <;> decide)

/-- The sites the closure lemma bounds the successors up to: the twelve elections, the proxy
fence, and the partition's barrier. -/
def closeSites : List ProA.Site :=
  [.el0, .el1, .el2, .el3, .el4, .el5, .el6, .el7, .el8, .el9, .el10, .el11, .fnc0, .bar2]

theorem closeSites_le : ∀ c ∈ closeSites, c.ctorIdx ≤ ProA.Site.bar2.ctorIdx := by decide

/-- **A successor of a site before `c` is at most `c`**, for `c` among `closeSites`. -/
theorem pro_next_le_all {d d' : ProA.D} {e : Event}
    (h : ProA.next L g d e = some (some d')) :
    ∀ c ∈ closeSites, d.site.ctorIdx < c.ctorIdx → d'.site.ctorIdx ≤ c.ctorIdx := by
  obtain ⟨s, dt⟩ := d
  by_cases hb : s.ctorIdx < ProA.Site.bar2.ctorIdx
  · cases s <;> first
      | (exfalso; revert hb; decide)
      | (simp only [ProA.next] at h
         (repeat' split at h) <;>
         first
         | (simp at h; done)
         | (simp only [Option.some.injEq] at h; subst h; dsimp only; decide))
  · intro c hc hlt
    have := closeSites_le c hc
    simp only at hlt
    omega

theorem pro_next_le {d d' : ProA.D} {e : Event}
    (h : ProA.next L g d e = some (some d')) {c : ProA.Site} (hc : c ∈ closeSites)
    (hlt : d.site.ctorIdx < c.ctorIdx) : d'.site.ctorIdx ≤ c.ctorIdx :=
  pro_next_le_all h c hc hlt

/-! ### The steps of the default-partition machine -/

/-- **The kinds of step**: inside the common start, from its last site into the prologue, inside
the prologue, from the prologue's last site into the softmax region, inside the softmax region,
from it into the epilogue, inside the epilogue. -/
theorem next_cases {s s' : DComp.St} {e : Event}
    (h : DComp.next L g Q s e = some (some s')) :
    (∃ d d', s = .dstart d ∧ s' = .dstart d' ∧ DStart.next L g d e = some (some d') ∧
      d'.site ≠ DStart.Site.toProA) ∨
    (∃ d d', s = .dstart d ∧ DStart.next L g d e = some (some d') ∧
      d'.site = DStart.Site.toProA ∧
        s' = .pro (ProA.D.start (DStart.inh L g Q (ProA.shW d'.w)) d'.w)) ∨
    (∃ d d', s = .pro d ∧ d.site ≠ ProA.Site.bar18 ∧ s' = .pro d' ∧
      ProA.next L g d e = some (some d')) ∨
    (∃ d d', s = .pro d ∧ d.site = ProA.Site.bar18 ∧ s' = .sm d') ∨
    (∃ d d', s = .sm d ∧ s' = .sm d') ∨ (∃ d d', s = .sm d ∧ s' = .epi d') ∨
    (∃ d d', s = .epi d ∧ s' = .epi d') := by
  cases s with
  | dstart d =>
    simp only [DComp.next, DComp.dstartNext] at h
    obtain ⟨a, ha, hs'⟩ := mapInv (f := fun d' => if d'.site = DStart.Site.toProA then
      DComp.St.pro (ProA.D.start (DStart.inh L g Q (ProA.shW d'.w)) d'.w) else DComp.St.dstart d') h
    by_cases hp : a.site = DStart.Site.toProA
    · simp only [hp, ↓reduceIte] at hs'
      exact .inr (.inl ⟨d, a, rfl, ha, hp, hs'.symm⟩)
    · simp only [hp, ↓reduceIte] at hs'
      exact .inl ⟨d, a, rfl, hs'.symm, ha, hp⟩
  | pro d =>
    simp only [DComp.next, DComp.proNext] at h
    by_cases hb : d.site = ProA.Site.bar18
    · simp only [hb, ↓reduceIte] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact .inr (.inr (.inr (.inl ⟨d, _, rfl, hb, rfl⟩)))
      · simp at h
    · simp only [hb, ↓reduceIte] at h
      obtain ⟨a, ha, rfl⟩ := mapInv (f := DComp.St.pro) h
      exact .inr (.inr (.inl ⟨d, a, rfl, hb, rfl, ha⟩))
  | sm d =>
    simp only [DComp.next, DComp.smNext] at h
    split at h
    · simp only [DComp.exitNext] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact .inr (.inr (.inr (.inr (.inr (.inl ⟨d, _, rfl, rfl⟩)))))
      · simp at h
    · obtain ⟨a, ha, rfl⟩ := mapInv (f := DComp.St.sm) h
      exact .inr (.inr (.inr (.inr (.inl ⟨d, a, rfl, rfl⟩))))
  | epi d =>
    simp only [DComp.next] at h
    obtain ⟨a, ha, rfl⟩ := mapInv (f := DComp.St.epi) h
    exact .inr (.inr (.inr (.inr (.inr (.inr ⟨d, a, rfl, rfl⟩)))))

/-! ### The stage -/

theorem site_idx_le (s : ProA.Site) : s.ctorIdx ≤ ProA.Site.bar18.ctorIdx := by
  cases s <;> decide

/-- The stage of a state: the sites of the common start, then the prologue's, then the rest. -/
def stg : DComp.St → Nat
  | .dstart d => d.site.ctorIdx
  | .pro d => 8 + d.site.ctorIdx
  | .sm _ => 100000
  | .epi _ => 100000

theorem dstart_next_lt {d d' : DStart.D} {e : Event} (h : DStart.next L g d e = some (some d')) :
    d.site.ctorIdx < d'.site.ctorIdx := by
  obtain ⟨site, tm⟩ := d
  cases site <;> simp only [DStart.next] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; dsimp only; decide)

/-- **The stage never decreases, and a step of the common start or of the prologue raises
it.** -/
theorem stg_next {s s' : DComp.St} {e : Event} (h : DComp.next L g Q s e = some (some s')) :
    stg s ≤ stg s' ∧ ((∃ d, s = .dstart d) ∨ (∃ d, s = .pro d) → stg s < stg s') := by
  have hb := site_idx_le
  rcases next_cases h with ⟨d, d', rfl, rfl, hn, -⟩ | ⟨d, d', rfl, hn, hp, rfl⟩ |
    ⟨d, d', rfl, -, rfl, hn⟩ | ⟨d, d', rfl, hb18, rfl⟩ | ⟨d, d', rfl, rfl⟩ |
    ⟨d, d', rfl, rfl⟩ | ⟨d, d', rfl, rfl⟩
  · have := dstart_next_lt hn
    simp only [stg]
    refine ⟨by omega, fun _ => by omega⟩
  · have h1 : d.site.ctorIdx < 8 := by
      obtain ⟨site, tm⟩ := d
      cases site <;> dsimp only <;> decide
    simp only [stg]
    have : ProA.D.start (DStart.inh L g Q (ProA.shW d'.w)) d'.w =
        ⟨.sMax, ProA.Dat.start _ _⟩ := rfl
    rw [this]
    refine ⟨by simp only; omega, fun _ => by simp only; omega⟩
  · have := pro_next_lt hn
    simp only [stg]
    refine ⟨by omega, fun _ => by omega⟩
  · have := hb d.site
    have h18 : ProA.Site.bar18.ctorIdx < 1000 := by decide
    simp only [stg]
    refine ⟨by omega, fun _ => by omega⟩
  · simp only [stg]
    refine ⟨le_rfl, fun h => ?_⟩
    rcases h with ⟨x, hx⟩ | ⟨x, hx⟩ <;> cases hx
  · have := hb
    simp only [stg]
    refine ⟨le_rfl, fun h => ?_⟩
    rcases h with ⟨x, hx⟩ | ⟨x, hx⟩ <;> cases hx
  · simp only [stg]
    refine ⟨le_rfl, fun h => ?_⟩
    rcases h with ⟨x, hx⟩ | ⟨x, hx⟩ <;> cases hx

/-! ### The barrier-0 count -/

/-- The prologue's sites before its first `bar.sync 0, 128` are no barrier. -/
theorem pro_b0_early (s : ProA.Site) (h : s.ctorIdx < ProA.Site.bar2.ctorIdx) :
    b0At s.pc = 0 := by
  cases s <;> first | (exfalso; revert h; decide) | decide +kernel

/-- The prologue's `bar2` is `bar.sync 0, 128`. -/
theorem pro_b0_bar2 : b0At ProA.Site.bar2.pc = 2 := by decide +kernel

/-- The exact number of barrier-0 events before a state's event, where it is known: at the
sites of the common start and of the prologue up to its first `bar.sync 0, 128`. -/
def exb : DComp.St → Option Nat
  | .dstart d => some (match d.site with
      | .alloc | .allocWr | .bar0 => 0
      | .ld0 | .bar1 => 1
      | _ => 2)
  | .pro d => if d.site.ctorIdx ≤ ProA.Site.bar2.ctorIdx then some 2 else none
  | _ => none

/-- The number of barrier-0 events the state's own event adds: one at a barrier-0 site, none
elsewhere. -/
def b0inc (s : DComp.St) : Nat := if b0At (DComp.pc s) = 0 then 0 else 1

theorem dstart_next_toPro {d d' : DStart.D} {e : Event}
    (h : DStart.next L g d e = some (some d')) (hp : d'.site = DStart.Site.toProA) :
    d.site = DStart.Site.shfl := by
  obtain ⟨site, tm⟩ := d
  cases site <;> simp only [DStart.next] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; first | rfl | (simp at hp))

/-- **The count is carried by the step**: the successor's exact count is the state's plus the
state's own increment. -/
theorem exb_next {s s' : DComp.St} {e : Event} (h : DComp.next L g Q s e = some (some s'))
    {n' : Nat} (hs' : exb s' = some n') : ∃ n, exb s = some n ∧ n' = n + b0inc s := by
  rcases next_cases h with ⟨d, d', rfl, rfl, hn, -⟩ | ⟨d, d', rfl, hn, hp, rfl⟩ |
    ⟨d, d', rfl, hb, rfl, hn⟩ | ⟨d, d', rfl, hb18, rfl⟩ | ⟨d, d', rfl, rfl⟩ |
    ⟨d, d', rfl, rfl⟩ | ⟨d, d', rfl, rfl⟩
  · obtain ⟨site, tm⟩ := d
    obtain ⟨site', tm'⟩ := d'
    have hb0 := dstart_b0 site
    simp only [exb, Option.some.injEq] at hs'
    subst hs'
    cases site <;> simp only [DStart.next] at hn <;> (repeat' split at hn) <;>
      first
      | (simp at hn; done)
      | (simp only [Option.some.injEq, DStart.D.mk.injEq] at hn
         obtain ⟨rfl, -⟩ := hn
         exact ⟨_, rfl, by simp [b0inc, DComp.pc, hb0]⟩)
  · have h0 := dstart_next_toPro hn hp
    obtain ⟨site, tm⟩ := d
    simp only at h0
    subst h0
    simp only [exb, ProA.D.start] at hs'
    have h2 : ProA.Site.sMax.ctorIdx ≤ ProA.Site.bar2.ctorIdx := by decide
    simp only [h2, ↓reduceIte, Option.some.injEq] at hs'
    subst hs'
    refine ⟨2, rfl, ?_⟩
    have := dstart_b0 DStart.Site.shfl
    simp [b0inc, DComp.pc, this]
  · have hlt := pro_next_lt hn
    simp only [exb] at hs'
    by_cases h1 : d'.site.ctorIdx ≤ ProA.Site.bar2.ctorIdx
    · simp only [h1, ↓reduceIte, Option.some.injEq] at hs'
      have h2 : d.site.ctorIdx < ProA.Site.bar2.ctorIdx := by omega
      have h3 := pro_b0_early d.site h2
      refine ⟨2, ?_, ?_⟩
      · simp [exb, h2.le]
      · simp [b0inc, DComp.pc, h3]
        omega
    · simp [h1] at hs'
  · simp [exb] at hs'
  · simp [exb] at hs'
  · simp [exb] at hs'
  · simp [exb] at hs'

end
end PTX.Kernels.InklingRelDecode.Proof.IpInit
