-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Epi

@[expose] public section

/-! # Tools of the epilogue's step lemmas

The continuation of a step (`Cont`) and what a step owes (`Step`), segments of some length
(`SegE`) and their composition, the assumptions at the epilogue's code (no software-`exp2`
segment, no other assumption names a move or a branch), and the generic step of each kind of
event instruction: a poll, a broadcast, an instruction that continues at the next instruction.
Each takes the segment from the instruction's successor to the next site as a hypothesis. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The value-table reduction used after evaluating a segment: the table's register ranges are
decided on the literal register. -/
macro "epi_values" : tactic =>
  `(tactic| simp only [valueOf, D.scalars, D.word, D.prod, PTX.Flow.lookupLit,
    Option.getD_some, Option.getD_none, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceSub, and_self,
    and_false, false_and, ↓reduceIte])

/-- Evaluate a segment from `h` and close the facts of its end state, with the given lemmas. -/
syntax "epi_seg " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| epi_seg $h $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      seg_fp $h using
        try epi_values
        all_goals seg_close [$extra,*]))

/-- `epi_seg` for segments with signed integer arithmetic (`mad.wide.s32`, signed compares):
equations the plain normal form does not close are closed by `norm_signed`. -/
syntax "epi_segs " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| epi_segs $h $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      seg_fp $h using
        try epi_values
        all_goals first
          | seg_close [$extra,*]
          | (show Value.bits _ _ = _; norm_signed [intOf, intBits, eq_self, $extra,*])
          | (show Value.pred _ = _; norm_signed [intOf, intBits, eq_self, $extra,*])))

/-- The continuation of a step of this machine: the thread stops following (`some none`), or
steps to `d'` at `t'` by a run of `Tau`. -/
def Cont (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) : Prop :=
  next d e = some none ∨ ∃ d' t', next d e = some (some d') ∧
    Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ At t' d'.site.pc (facts d') ∧ Inv d'

/-- A step of the machine: the thread continues to the successor state, or the event leaves a
fault the machine records as `none` (a pack, product or reciprocal that faults). -/
def Step (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) : Prop :=
  Cont L g d e u ∨ (next d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u)

theorem facts_ne {pc : Nat} {d : D} {r : Nat} (hr : r ∉ Flow.live pc) :
    ∀ p ∈ factsAt pc d, p.1 ≠ r := by
  intro p hp he
  simp only [factsAt, Flow.factsFrom, List.mem_map] at hp
  obtain ⟨r', hr', rfl⟩ := hp
  exact hr (he ▸ hr')

/-- Registers live at a pc are valued by the table of a state with the same table. -/
theorem holds_live {R : Nat → Option Value} {pc pc' : Nat} {d d' : D}
    (h : Holds R (factsAt pc d)) (hv : valueOf d = valueOf d')
    (hl : ∀ r ∈ Flow.live pc', r ∈ Flow.live pc) : Holds R (factsAt pc' d') := by
  rw [factsAt, ← hv]
  exact Flow.holds_factsFrom_mono h hl

/-- Some number of local steps from `s` with facts `F` reach `b` with facts `G`. -/
def SegE (L : Launch) (g s : Nat) (F : List (Nat × Value)) (b : Nat) (G : List (Nat × Value)) :
    Prop := ∃ n, Seg kernel asms L g n s F b G

theorem SegE.of_seg {L : Launch} {g n s b : Nat} {F G : List (Nat × Value)}
    (h : Seg kernel asms L g n s F b G) : SegE L g s F b G := ⟨n, h⟩

theorem SegE.comp {L : Launch} {g s p b : Nat} {F G H : List (Nat × Value)}
    (h1 : SegE L g s F p G) (h2 : SegE L g p G b H) : SegE L g s F b H := by
  obtain ⟨m, h1⟩ := h1
  obtain ⟨n, h2⟩ := h2
  exact ⟨m + n, h1.comp h2⟩

theorem SegE.weaken_end {L : Launch} {g s b : Nat} {F G G' : List (Nat × Value)}
    (h : SegE L g s F b G) (hG : ∀ R, Holds R G → Holds R G') : SegE L g s F b G' := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, h.weaken_end hG⟩

theorem SegE.weaken_start {L : Launch} {g s b : Nat} {F F' G : List (Nat × Value)}
    (h : SegE L g s F b G) (hF : ∀ R, Holds R F' → Holds R F) : SegE L g s F' b G := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, h.weaken_start hF⟩

theorem SegE.rtg {L : Launch} {g s b : Nat} {t : TState} {F G : List (Nat × Value)}
    (hs : SegE L g s F b G) (h : At t s F) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧ At t' b G := by
  obtain ⟨n, hn⟩ := hs
  exact hn.rtg h

/-- The facts of a site's state after an instruction that writes no register: the table's facts
at the next pc. -/
theorem at_next_live {pc pc' : Nat} {d d' : D} {t : TState} (h : At t pc (factsAt pc d))
    (hpc : pc' = pc + 1) (hv : valueOf d = valueOf d')
    (hl : ∀ r ∈ Flow.live pc', r ∈ Flow.live pc) : At (PTX.next t) pc' (factsAt pc' d') := by
  subst hpc
  exact (At.next h).mono (holds_live h.2.2.2.2 hv hl)

/-! ### The assumptions at the epilogue's code -/

/-- No assumption of the kernel takes a segment at a pc outside the software-`exp2` sites. -/
theorem asms_segFree {pc : Nat} (h : Assumptions.emuSites.contains pc = false) :
    Assumption.SegFreePc asms pc := by
  intro a ha L g t ht
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · rfl
  · rfl
  · have : pc ∉ Assumptions.emuSites := by simpa using h
    simp [Assumptions.swExp2, ht, this]
  all_goals rfl

/-- `SegFreePc asms pc` for a literal `pc` outside the software-`exp2` sites. -/
macro "asms_free" : tactic => `(tactic| exact asms_segFree (by decide +kernel))

/-- At the epilogue's code (from pc 2560) no assumption takes a segment. -/
theorem segFree {pc : Nat} (h : 2560 ≤ pc) : Assumption.SegFreePc asms pc :=
  asms_segFree (by
    have : Assumptions.emuSites.all (· < 2560) = true := by decide +kernel
    cases hc : Assumptions.emuSites.contains pc
    · rfl
    · exfalso
      have := List.all_eq_true.mp this pc (List.contains_iff_mem.mp hc)
      simp at this
      omega)

/-! ### The register table -/

theorem lookup_append' (l₁ l₂ : List (Nat × Value)) (r : Nat) :
    (l₁ ++ l₂).lookup r = (l₁.lookup r).or (l₂.lookup r) := by
  induction l₁ with
  | nil => simp
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.cons_append, List.lookup]
    cases r == k <;> simp [ih]

/-- A table of consecutive registers `a + k` holding `f k`, looked up. -/
theorem lookup_range_map (a : Nat) (f : Nat → Value) (n r : Nat) :
    ((List.range n).map (fun k => (a + k, f k))).lookup r =
      if a ≤ r ∧ r < a + n then some (f (r - a)) else none := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, lookup_append', ih]
    by_cases h1 : a ≤ r ∧ r < a + n
    · have h2 : a ≤ r ∧ r < a + (n + 1) := ⟨h1.1, by omega⟩
      simp [h1, h2]
    · by_cases h3 : r = a + n
      · subst h3
        simp
      · have h4 : ¬ (a ≤ r ∧ r < a + (n + 1)) := by omega
        have h5 : (r == a + n) = false := by simpa using h3
        simp [h1, h4, List.lookup, h5]

theorem scalars_keys (d : D) : (d.scalars).map Prod.fst =
    [3, 175, 176, 178, 174, 173, 462, 463, 464, 478, 491, 496, 497, 524, 533, 610, 624, 1760, 1761,
      1827, 1831, 1896, 1897, 1898, 1899, 1915, 1956, 2023, 2024, 2379, 2378] := rfl

/-- A register outside the arrays of the table. -/
def Free (r : Nat) : Prop :=
  ¬ (1763 ≤ r ∧ r < 1827) ∧ ¬ (2346 ≤ r ∧ r < 2378) ∧ ¬ (1832 ≤ r ∧ r < 1896) ∧
    ¬ (2380 ≤ r ∧ r < 2444) ∧ ¬ (2479 ≤ r ∧ r < 2511)

instance : DecidablePred Free := fun r => by unfold Free; infer_instance

theorem scalars_free (d : D) : ∀ r ∈ (d.scalars).map Prod.fst, Free r := by
  rw [scalars_keys]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [Free]
  omega

theorem lookup_none_of_not_mem (l : List (Nat × Value)) {r : Nat} (h : r ∉ l.map Prod.fst) :
    l.lookup r = none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have : (r == k) = false := by simpa using h.1
    simp only [List.lookup, this]
    exact ih h.2

/-- A register outside the arrays has the value of the scalar table. -/
theorem valueOf_free (d : D) {r : Nat} (h : Free r) :
    valueOf d r = ((d.scalars).lookup r).getD (b32 0) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [valueOf, D.table, lookup_append', lookup_range_map, h1, h2, h3, h4, h5,
    ↓reduceIte]
  cases (d.scalars).lookup r <;> simp

/-- A register outside the arrays is valued alike by two states of the same registers. -/
theorem valueOf_free_eq {d d' : D} (hp : d.pr = d'.pr) (hs : d.sk = d'.sk) {r : Nat}
    (h : Free r) :
    valueOf d' r = valueOf d r := by
  rw [valueOf_free d h, valueOf_free d' h]
  have : d'.scalars = d.scalars := by simp only [D.scalars, hp, hs]
  rw [this]

/-- The loaded word `k`. -/
theorem valueOf_o (d : D) {k : Nat} (hk : k < 64) :
    valueOf d (1763 + k) = d.o.getD k (b32 0) := by
  have hs : (d.scalars).lookup (1763 + k) = none := lookup_none_of_not_mem _ (fun hm => by
    have := scalars_free d _ hm
    simp only [Free] at this
    omega)
  have h1 : 1763 ≤ 1763 + k ∧ 1763 + k < 1763 + 64 := by omega
  have h2 : ¬ (2346 ≤ 1763 + k ∧ 1763 + k < 2346 + 32) := by omega
  have h3 : ¬ (1832 ≤ 1763 + k ∧ 1763 + k < 1832 + 64) := by omega
  have h4 : ¬ (2380 ≤ 1763 + k ∧ 1763 + k < 2380 + 64) := by omega
  have h5 : ¬ (2479 ≤ 1763 + k ∧ 1763 + k < 2479 + 32) := by omega
  simp [valueOf, D.table, lookup_append', lookup_range_map, hs, h1, h2, h3, h4, h5]

/-- The packed pair `q` of the loaded words. -/
theorem valueOf_pack (d : D) {q : Nat} (hq : q < 32) :
    valueOf d (2346 + q) =
      joinValue (d.o.getD (2 * q) (b32 0)) (d.o.getD (2 * q + 1) (b32 0)) := by
  have hs : (d.scalars).lookup (2346 + q) = none := lookup_none_of_not_mem _ (fun hm => by
    have := scalars_free d _ hm
    simp only [Free] at this
    omega)
  have h1 : ¬ (1763 ≤ 2346 + q ∧ 2346 + q < 1763 + 64) := by omega
  have h2 : 2346 ≤ 2346 + q ∧ 2346 + q < 2346 + 32 := by omega
  have h3 : ¬ (1832 ≤ 2346 + q ∧ 2346 + q < 1832 + 64) := by omega
  have h4 : ¬ (2380 ≤ 2346 + q ∧ 2346 + q < 2380 + 64) := by omega
  have h5 : ¬ (2479 ≤ 2346 + q ∧ 2346 + q < 2479 + 32) := by omega
  simp [valueOf, D.table, lookup_append', lookup_range_map, hs, h1, h2, h3, h4, h5]

/-- The pair `(inv_l, inv_l)`. -/
theorem valueOf_cpair (d : D) : valueOf d 2378 = d.pr.cpair := by
  have : (d.scalars).lookup 2378 = some d.pr.cpair := rfl
  simp [valueOf, D.table, lookup_append', this]

/-- The word `k` of the product. -/
theorem valueOf_word (d : D) {k : Nat} (hk : k < 64) : valueOf d (1832 + k) = d.word k := by
  have hs : (d.scalars).lookup (1832 + k) = none := lookup_none_of_not_mem _ (fun hm => by
    have := scalars_free d _ hm
    simp only [Free] at this
    omega)
  have h1 : ¬ (1763 ≤ 1832 + k ∧ 1832 + k < 1763 + 64) := by omega
  have h2 : ¬ (2346 ≤ 1832 + k ∧ 1832 + k < 2346 + 32) := by omega
  have h3 : 1832 ≤ 1832 + k ∧ 1832 + k < 1832 + 64 := by omega
  have h4 : ¬ (2380 ≤ 1832 + k ∧ 1832 + k < 2380 + 64) := by omega
  have h5 : ¬ (2479 ≤ 1832 + k ∧ 1832 + k < 2479 + 32) := by omega
  simp [valueOf, D.table, lookup_append', lookup_range_map, hs, h1, h2, h3, h4, h5]

/-- The address of word `k`. -/
theorem valueOf_addr (d : D) {k : Nat} (hk : k < 64) :
    valueOf d (2380 + k) = b64 ((d.pr.oAddr + 4 * k) % M64) := by
  have hs : (d.scalars).lookup (2380 + k) = none := lookup_none_of_not_mem _ (fun hm => by
    have := scalars_free d _ hm
    simp only [Free] at this
    omega)
  have h1 : ¬ (1763 ≤ 2380 + k ∧ 2380 + k < 1763 + 64) := by omega
  have h2 : ¬ (2346 ≤ 2380 + k ∧ 2380 + k < 2346 + 32) := by omega
  have h3 : ¬ (1832 ≤ 2380 + k ∧ 2380 + k < 1832 + 64) := by omega
  have h4 : 2380 ≤ 2380 + k ∧ 2380 + k < 2380 + 64 := by omega
  have h5 : ¬ (2479 ≤ 2380 + k ∧ 2380 + k < 2479 + 32) := by omega
  simp [valueOf, D.table, lookup_append', lookup_range_map, hs, h1, h2, h3, h4, h5]

/-- Product pair `k`. -/
theorem valueOf_prod (d : D) {k : Nat} (hk : k < 32) : valueOf d (2479 + k) = d.prod k := by
  have hs : (d.scalars).lookup (2479 + k) = none := lookup_none_of_not_mem _ (fun hm => by
    have := scalars_free d _ hm
    simp only [Free] at this
    omega)
  have h1 : ¬ (1763 ≤ 2479 + k ∧ 2479 + k < 1763 + 64) := by omega
  have h2 : ¬ (2346 ≤ 2479 + k ∧ 2479 + k < 2346 + 32) := by omega
  have h3 : ¬ (1832 ≤ 2479 + k ∧ 2479 + k < 1832 + 64) := by omega
  have h4 : ¬ (2380 ≤ 2479 + k ∧ 2479 + k < 2380 + 64) := by omega
  have h5 : 2479 ≤ 2479 + k ∧ 2479 + k < 2479 + 32 := by omega
  simp [valueOf, D.table, lookup_append', lookup_range_map, hs, h1, h2, h3, h4, h5]

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
