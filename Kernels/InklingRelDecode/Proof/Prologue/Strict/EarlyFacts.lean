-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Stable

@[expose] public section

/-! # The facts of the early sites

Before the first preload block every state holds the same data facts (the launch's constants), and
the control table of two sites of the stretch differs only in its live registers. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow Control

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

theorem tags_early {s s' : Site} (h : Data.early s = true) (h' : Data.early s' = true) :
    Data.tags s = Data.tags s' := by
  cases s <;> cases s' <;> simp_all [Data.early, Data.tags, Data.oldTags, Data.pos, Data.qTags]

/-- The data facts of two early states with the same words are equal. -/
theorem dF_early {d d' : Data.D} (h : Data.early d.c.site = true)
    (h' : Data.early d'.c.site = true) :
    Data.dF Q L g d = Data.dF Q L g d' := by
  simp only [Data.dF, tags_early h h']
  exact List.map_congr_left fun τ hτ => by
    have := plain_early h τ (by rw [tags_early h h']; exact hτ)
    cases τ <;> simp_all [Tag.plain, Data.Tag.val]

/-- Facts at a later site whose live registers are among the earlier ones. -/
theorem holds_dFacts_mono {R : Nat → Option Value} {d d' : Data.D} {pc pc' : Nat}
    (hd : Data.dF Q L g d = Data.dF Q L g d') (hv : valueOf Q L g w d.c = valueOf Q L g w d'.c)
    (hl : (ctlLive pc').isSublist (ctlLive pc)) :
    Holds R (Data.dF Q L g d ++ facts Q L g w d.c pc) →
      Holds R (Data.dF Q L g d' ++ facts Q L g w d'.c pc') := by
  intro h
  rw [holds_append] at h ⊢
  rw [← hd]
  simp only [facts, ← hv] at h ⊢
  exact ⟨h.1, holds_factsFrom_mono h.2 (List.isSublist_iff_sublist.mp hl).subset⟩

/-- The same for the machine's facts, the control table first. -/
theorem holds_code_mono {R : Nat → Option Value} {d d' : Data.D}
    (hd : Data.dF Q L g d = Data.dF Q L g d') (hv : valueOf Q L g w d.c = valueOf Q L g w d'.c)
    (hl : (ctlLive d'.c.site.pc).isSublist (ctlLive d.c.site.pc)) :
    Holds R ((Data.code Q L g w).facts d) → Holds R ((Data.code Q L g w).facts d') := by
  intro h
  change Holds R (facts Q L g w d.c d.c.site.pc ++ Data.dF Q L g d) at h
  change Holds R (facts Q L g w d'.c d'.c.site.pc ++ Data.dF Q L g d')
  rw [holds_append] at h ⊢
  rw [← hd]
  simp only [facts, ← hv]
  exact ⟨holds_factsFrom_mono h.1 (List.isSublist_iff_sublist.mp hl).subset, h.2⟩

theorem fresh_keys {d : Data.D} {r : Nat} (h1 : r ∉ ctlLive d.c.site.pc)
    (h2 : r ∉ (Data.tags d.c.site).map Data.Tag.reg) :
    r ∉ ((Data.code Q L g w).facts d).map Prod.fst := fun h => by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  exact fresh_reg h1 h2 p hp rfl

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
