-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Frame
public import Lemmas.Flow.SegQPre

@[expose] public section

/-! # Facts that a changed word does not touch

The kernel cannot compare the register values of two control states that differ in a word
(`valueOf` is a large match); these lemmas equate the facts of the live registers that do not
read the word, by the equation lemmas of `valueOf`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow Control

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

/-- The registers that read none of the words the three request loads and the elections change. -/
def keep : List Nat :=
  [3, 462, 463, 464, 478, 479, 480, 526, 527, 528, 532, 1949, 2018, 2019, 2020, 2021, 2055, 2056,
    2057, 2058]

private theorem keep_a {r : Nat} (h : r ∈ [3, 462, 463, 464, 478]) (d d' : Control.D) :
    valueOf Q L g w d r = valueOf Q L g w d' r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    (simp (disch := decide +kernel) only [valueOf_plain]; simp only [registerValue])

private theorem keep_b {r : Nat} (h : r ∈ [479, 480, 526, 527, 528]) (d d' : Control.D) :
    valueOf Q L g w d r = valueOf Q L g w d' r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    (simp (disch := decide +kernel) only [valueOf_plain]; simp only [registerValue])

private theorem keep_c {r : Nat} (h : r ∈ [532, 1949, 2018, 2019, 2020]) (d d' : Control.D) :
    valueOf Q L g w d r = valueOf Q L g w d' r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    (simp (disch := decide +kernel) only [valueOf_plain]; simp only [registerValue])

private theorem keep_d {r : Nat} (h : r ∈ [2021, 2055, 2056, 2057, 2058]) (d d' : Control.D) :
    valueOf Q L g w d r = valueOf Q L g w d' r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    (simp (disch := decide +kernel) only [valueOf_plain]; simp only [registerValue])

theorem valueOf_keep {r : Nat} (h : r ∈ keep) (d d' : Control.D) :
    valueOf Q L g w d r = valueOf Q L g w d' r := by
  have h' : r ∈ [3, 462, 463, 464, 478] ∨ r ∈ [479, 480, 526, 527, 528] ∨
      r ∈ [532, 1949, 2018, 2019, 2020] ∨ r ∈ [2021, 2055, 2056, 2057, 2058] := by
    simp only [keep, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    omega
  rcases h' with h | h | h | h
  exacts [keep_a h d d', keep_b h d d', keep_c h d d', keep_d h d d']

theorem valueOf_610 (d : Control.D) : valueOf Q L g w d 610 = d.first := by
  simp (disch := decide +kernel) only [valueOf_plain]; simp only [registerValue]

theorem valueOf_481 (d : Control.D) : valueOf Q L g w d 481 = subValue d.last d.first := by
  simp (disch := decide +kernel) only [valueOf_plain]; simp only [registerValue]

/-- The facts of two states at `pc` agree if the live registers read only what the states share. -/
theorem facts_congr {pc : Nat} {d d' : Control.D}
    (hall : (ctlLive pc).all fun r => decide (r ∈ keep ∨ r = 610 ∨ r = 481))
    (h610 : 610 ∈ ctlLive pc → d.first = d'.first)
    (h481 : 481 ∈ ctlLive pc → d.first = d'.first ∧ d.last = d'.last) :
    facts Q L g w d pc = facts Q L g w d' pc :=
  List.map_congr_left fun r hr => by
    rcases of_decide_eq_true (List.all_eq_true.mp hall r hr) with h | rfl | rfl
    · rw [valueOf_keep h d d']
    · rw [valueOf_610, valueOf_610, h610 hr]
    · rw [valueOf_481, valueOf_481, (h481 hr).1, (h481 hr).2]

/-- The tags whose values read neither the words nor the data of the state. -/
def Tag.plain : Data.Tag → Bool
  | .scale | .stride | .rows | .cols | .oy | .ox => true
  | _ => false

theorem dF_plain {d d' : Data.D} (h : d.c.site = d'.c.site)
    (hp : ∀ τ ∈ Data.tags d.c.site, Tag.plain τ = true) :
    Data.dF Q L g d = Data.dF Q L g d' :=
  by
    simp only [Data.dF, ← h]
    exact List.map_congr_left fun τ hτ => by
      have := hp τ hτ
      cases τ <;> simp_all [Tag.plain, Data.Tag.val]

theorem plain_early {s : Site} (h : Data.early s = true) :
    ∀ τ ∈ Data.tags s, Tag.plain τ = true := by
  cases s <;> simp_all [Data.early, Data.tags, Data.oldTags, Data.pos, Data.qTags, Tag.plain]

/-- The registers of the data facts of an early site. -/
theorem dF_keys_early {d : Data.D} (h : Data.early d.c.site = true) :
    ∀ p ∈ Data.dF Q L g d, p.1 ∈ [525, 529, 530, 531] := by
  intro p hp
  obtain ⟨⟨s, f, l, q, e, b⟩, v⟩ := d
  simp only [Data.dF, List.mem_map] at hp
  obtain ⟨τ, hτ, rfl⟩ := hp
  revert hτ
  simp only at h ⊢
  cases s <;> simp_all [Data.early, Data.tags, Data.oldTags, Data.pos, Data.qTags, Data.Tag.reg]
  all_goals (rintro (rfl | rfl | rfl | rfl) <;> simp)

/-- The machine's facts of two states at the same early site, whose live control registers agree. -/
theorem code_facts_early {d d' : Data.D} (h : d.c.site = d'.c.site)
    (hp : ∀ τ ∈ Data.tags d.c.site, Tag.plain τ = true)
    (hf : facts Q L g w d.c d.c.site.pc = facts Q L g w d'.c d'.c.site.pc) :
    (Data.code Q L g w).facts d = (Data.code Q L g w).facts d' := by
  change facts Q L g w d.c d.c.site.pc ++ _ = facts Q L g w d'.c d'.c.site.pc ++ _
  rw [hf, dF_plain h hp]

/-- A register that no fact of the state names. -/
theorem fresh_reg {d : Data.D} {r : Nat} (h1 : r ∉ ctlLive d.c.site.pc)
    (h2 : r ∉ (Data.tags d.c.site).map Data.Tag.reg) :
    ∀ p ∈ (Data.code Q L g w).facts d, p.1 ≠ r := by
  intro p hp hr
  simp only [Control.facts, List.mem_append, Data.dF, List.mem_map] at hp
  rcases hp with hp | ⟨τ, hτ, rfl⟩
  · have := List.mem_map_of_mem (f := Prod.fst) hp
    rw [factsFrom_keys] at this
    exact h1 (hr ▸ this)
  · exact h2 (hr ▸ List.mem_map_of_mem (f := Data.Tag.reg) hτ)

/-- The machine's facts at a request load do not read the word the load is about to set. -/
theorem code_facts_ld0 (c : Control.D) (hs : c.site = .ld 0) (v : Data.Vals) (a : Value) :
    (Data.code Q L g w).facts ⟨c, v⟩ = (Data.code Q L g w).facts ⟨{c with first := a}, v⟩ := by
  obtain ⟨s, f, l, q, e, b⟩ := c
  cases hs
  exact code_facts_early rfl (plain_early rfl) (facts_congr (pc := 34) (by decide +kernel)
    (fun h => absurd h (by decide +kernel)) (fun h => absurd h (by decide +kernel)))

theorem code_facts_ld1 (c : Control.D) (hs : c.site = .ld 1) (v : Data.Vals) (a : Value) :
    (Data.code Q L g w).facts ⟨c, v⟩ = (Data.code Q L g w).facts ⟨{c with last := a}, v⟩ := by
  obtain ⟨s, f, l, q, e, b⟩ := c
  cases hs
  exact code_facts_early rfl (plain_early rfl) (facts_congr (pc := 37) (by decide +kernel)
    (fun _ => rfl) (fun h => absurd h (by decide +kernel)))

theorem code_facts_ld2 (c : Control.D) (hs : c.site = .ld 2) (v : Data.Vals) (a : Value) :
    (Data.code Q L g w).facts ⟨c, v⟩ = (Data.code Q L g w).facts ⟨{c with seq := a}, v⟩ := by
  obtain ⟨s, f, l, q, e, b⟩ := c
  cases hs
  exact code_facts_early rfl (plain_early rfl) (facts_congr (pc := 41) (by decide +kernel)
    (fun _ => rfl) (fun _ => ⟨rfl, rfl⟩))

/-- An old exact stretch of the control machine as a strict stretch of an early site's value
machine: the data facts ride along (`SegQ.of_seg_pre`). -/
macro "pro_br" t:term : tactic => `(tactic|
  exact PTX.Flow.Havoc.SegQ.of_seg_pre (Dk := [525, 529, 530, 531])
  (dF_keys_early rfl) Lib.rulesFrame $t rfl (by decide +kernel) (by decide +kernel)
  (PTX.Flow.Havoc.PlainSegs.mono (plainSegs_pro (a := 27) (b := 574) le_rfl) (by decide +kernel)
    (by decide +kernel)) (by decide +kernel) (by decide +kernel))

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
