-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Schedule.Defs
public import Kernels.FlashKdaFwd.Proof.Ref.Kinds.Table

@[expose] public section

/-!
# Static facts about the sites of the thread machine, for the progress instance

Facts that hold of every site (`Thread.Site`: an event site of the program, or the second event
of an `ldmatrix` / `stmatrix`, or a later element of the vector load), read off the generated
tables. None of them mentions an execution.

* `base`, `base_kind_of_pc`: two sites at one instruction are events of that one instruction.
  `base s` is the site of the instruction's first event; the kind of the instruction at a
  position is a function of the position (`Ref.site_kind`, an evaluated scan of the program),
  so two sites with one instruction index have first-event sites of one kind. Every "which
  sites share this position" question below is answered by this, without a search.
* `sub_le`: a sub-step is at most 3.
* `siteCls_kind`: the class of a site (`siteCls`, `Defs.lean`) is a function of its kind.
* Barriers: `sub_of_bar_pc` (a site at the position of a `bar.sync` is that barrier, at
  sub-step 0).
* Shuffles and elections: `coll_pc` (their positions are `collAll`), `coll_of_pc` (a site at
  such a position is a shuffle or an election), `collOf_lt_length` (a thread at such a position
  has collectives left), `pc_le_of_collOf` (fewer collectives made means an earlier position).
* Matrix events: `matrix_pc` (the site of a matrix event is at one of the 182 matrix
  instructions `Top.matrixSites`, all of them in the compute loop before the named barrier),
  `matBefore_lt` (fewer than 182 matrix events of the tile precede it), `mat_order` (**the
  count `matBefore` orders the positions**: a site of the tile loops with at most as many
  matrix events as a matrix site is at an earlier instruction, or at the same instruction and
  then at the matrix event itself or at the row read before it).
* `matOp_laneClosed`: every matrix instruction of the program has results that read the 32
  lanes only.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Sched PTX.Flow PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Protocol
open PTX.Kernels.FlashKdaFwd.Proof.Thread (Site)
open PTX.Kernels.FlashKdaFwd.Proof.Ref (SiteKind)

/-! ### Sites at one instruction -/

/-- The kind of the first event of the instruction whose event has kind `κ`. -/
def baseKind : SiteKind → SiteKind
  | .matrixLoadMx => .matrixLoad
  | .matrixStoreWr => .matrixStore
  | .loadEl1 | .loadEl2 | .loadEl3 => .load
  | κ => κ

/-- The site of the first event of the instruction of a site. -/
def base : Site → Site
  | .matrixLoadMx j _ => .matrixLoad j
  | .matrixStoreWr j _ => .matrixStore j
  | .loadEl1 _ _ | .loadEl2 _ _ _ | .loadEl3 _ _ _ _ => .load 177
  | s => s

theorem base_pc (s : Site) : (base s).pc = s.pc := by
  cases s <;> first | rfl | exact (Ref.loadEl_pc _).symm

theorem base_sub (s : Site) : (base s).sub = 0 := by cases s <;> rfl

theorem base_kind (s : Site) : (base s).kind = baseKind s.kind := by cases s <;> rfl

/-- **Two sites at one instruction are events of one instruction**: their first-event kinds
agree. -/
theorem base_kind_of_pc {s s' : Site} (h : s.pc = s'.pc) :
    baseKind s.kind = baseKind s'.kind := by
  have h1 := Ref.site_kind (base s)
  have h2 := Ref.site_kind (base s')
  rw [base_sub, base_pc, base_kind] at h1 h2
  rw [h] at h1
  exact Option.some.inj (h1.symm.trans h2)

/-- A sub-step is at most 3. -/
theorem sub_le (s : Site) : s.sub ≤ 3 := by
  cases s <;> simp [Site.sub]

/-- The sub-step of a site by its kind. -/
def kindSub : SiteKind → Nat
  | .matrixLoadMx | .matrixStoreWr | .loadEl1 => 1
  | .loadEl2 => 2
  | .loadEl3 => 3
  | _ => 0

theorem sub_kind (s : Site) : s.sub = kindSub s.kind := by cases s <;> rfl

/-- The class of an event by the kind of its site. -/
def kindCls : SiteKind → Cls
  | .elect | .shfl => .coll
  | .mbarWait => .poll
  | .warpMma | .matrixMove | .matrixStore | .matrixLoadMx => .matrix
  | _ => .free

/-- The class of a site is a function of its kind. -/
theorem siteCls_kind (s : Site) : siteCls s = kindCls s.kind := by cases s <;> rfl

/-! ### Barriers -/

/-- Every position of a `bar.sync` is the position of a barrier site. -/
theorem bar_pc_site : ∀ p ∈ bar0Pcs ++ [2913], ∃ j : Fin 10, (Site.bar j).pc = p := by
  decide +kernel

/-- **A site at the position of a `bar.sync` is at sub-step 0.** -/
theorem sub_of_bar_pc {s : Site} (h : s.pc ∈ bar0Pcs ∨ s.pc = 2913) : s.sub = 0 := by
  obtain ⟨j, hj⟩ := bar_pc_site s.pc (by
    rcases h with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (by simp [h]))
  have hk := base_kind_of_pc hj.symm
  rw [sub_kind]
  revert hk
  cases s.kind <;> intro hk <;> first | rfl | cases hk

/-! ### Shuffles and elections -/

/-- The positions of the eight shuffles and elections of the program. -/
def collAll : List Nat := [32, 48, 52, 55, 61, 87, 93, 312]

theorem elect_pc : ∀ j : Fin 5, (Site.elect j).pc ∈ collAll := by decide +kernel

theorem shfl_pc : ∀ j : Fin 3, (Site.shfl j).pc ∈ collAll := by decide +kernel

/-- A shuffle or an election is at one of the eight positions, at sub-step 0. -/
theorem coll_pc {s : Site} (h : siteCls s = .coll) : s.pc ∈ collAll ∧ s.sub = 0 := by
  cases s <;> first | exact ⟨elect_pc _, rfl⟩ | exact ⟨shfl_pc _, rfl⟩ | cases h

theorem collAll_site : ∀ p ∈ collAll,
    (∃ j : Fin 5, (Site.elect j).pc = p) ∨ ∃ j : Fin 3, (Site.shfl j).pc = p := by
  decide +kernel

/-- **A site at the position of a shuffle or an election is one.** -/
theorem coll_of_pc {s : Site} (h : s.pc ∈ collAll) : siteCls s = .coll := by
  rw [siteCls_kind]
  rcases collAll_site s.pc h with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hk := base_kind_of_pc hj.symm
    revert hk
    cases s.kind <;> intro hk <;> first | rfl | cases hk
  · have hk := base_kind_of_pc hj.symm
    revert hk
    cases s.kind <;> intro hk <;> first | rfl | cases hk

/-- The positions of a warp's collectives are among the eight. -/
theorem collPcs_sub (w : Nat) : ∀ p ∈ collPcs w, p ∈ collAll := by
  unfold collPcs
  split_ifs <;> decide

/-- A thread at one of the eight positions has collectives left: the last collective of every
warp is the election at 312. -/
theorem collOf_lt_length {w pc : Nat} (h : pc ∈ collAll) : collOf w pc < (collPcs w).length := by
  have h312 : pc ≤ 312 := by
    revert pc
    decide
  unfold collOf collPcs
  split_ifs <;>
    exact List.length_filter_lt_length_iff_exists.mpr ⟨312, by simp, by simpa using h312⟩

/-- At the exit a thread has made all the collectives of its warp. -/
theorem collOf_exit (w : Nat) : collOf w 3835 = (collPcs w).length := by
  unfold collOf collPcs
  split_ifs <;> rfl

/-- In a list of positions, the count of those below a member is below the count of those
below a later position. -/
theorem filter_lt_succ_le {l : List Nat} {p p' : Nat} (hp : p ∈ l) (h : p < p') :
    (l.filter (· < p)).length + 1 ≤ (l.filter (· < p')).length := by
  induction l with
  | nil => cases hp
  | cons a l ih =>
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hp with rfl | hm
    · have h1 : ¬ p < p := Nat.lt_irrefl _
      have hsub : (l.filter (· < p)).length ≤ (l.filter (· < p')).length := by
        refine (List.Sublist.length_le ?_)
        exact List.monotone_filter_right _ fun x hx => by
          simp only [decide_eq_true_eq] at hx ⊢
          omega
      simp only [decide_eq_true_eq, h1, ite_false, h, ite_true, List.length_cons]
      omega
    · have ih := ih hm
      by_cases ha : a < p
      · have ha' : a < p' := by omega
        simp only [decide_eq_true_eq, ha, ha', ite_true, List.length_cons]
        omega
      · by_cases ha' : a < p'
        · simp only [decide_eq_true_eq, ha, ha', ite_true, ite_false, List.length_cons]
          omega
        · simp only [decide_eq_true_eq, ha, ha', ite_false]
          exact ih

/-- **Fewer collectives made means an earlier position**: a thread of warp `w` that has made at
most as many collectives as one at a collective position of `w` is at or before it. -/
theorem pc_le_of_collOf {w pc pc' : Nat} (hp : pc ∈ collPcs w)
    (h : collOf w pc' ≤ collOf w pc) : pc' ≤ pc := by
  by_contra hlt
  have := filter_lt_succ_le hp (Nat.lt_of_not_le hlt)
  unfold collOf at h
  omega

/-! ### Matrix instructions -/

/-- The position of every matrix instruction is in the compute loop before the named barrier,
and its results read the 32 lanes only. -/
theorem matrixSites_all : Top.matrixSites.all (fun e =>
    decide (2106 ≤ e.1) && decide (e.1 ≤ 2912) && decide e.2.LaneClosed) = true := by
  decide +kernel

/-- The operation of the `n`-th matrix instruction of the tile body (any operation for an
index out of range). -/
def matOp (n : Nat) : Nat × MatrixOp := Top.matrixSites.getD n (0, .transpose)

/-- Every matrix instruction of the program has results that read the 32 lanes only. -/
theorem matOp_laneClosed (n : Nat) : (matOp n).2.LaneClosed := by
  unfold matOp
  rw [List.getD_eq_getElem?_getD]
  cases h : Top.matrixSites[n]? with
  | none => trivial
  | some e =>
    have := List.all_eq_true.mp matrixSites_all e (List.mem_of_getElem? h)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2

set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
/-- An instruction whose event is a matrix event is a warp matrix instruction. -/
theorem op_of_matrix_kind {sub : Nat} {op : Op} {κ : SiteKind}
    (hκ : Ref.opKind sub op = some κ) (h : kindCls κ = .matrix) : ∃ i, op = .matrix i := by
  cases op
  case matrix i => exact ⟨i, rfl⟩
  case fence f =>
    exfalso
    cases f with
    | thread _ _ => cases hκ
    | proxy _ _ _ => cases hκ; cases h
  all_goals
    exfalso
    simp only [Ref.opKind] at hκ
    first
      | (cases hκ <;> cases h)
      | (split at hκ <;> first
          | (cases hκ <;> cases h)
          | (cases hκ; split at h <;> cases h))

/-- **The site of a matrix event is at a matrix instruction.** -/
theorem matrix_pc {s : Site} (h : siteCls s = .matrix) :
    ∃ op, (s.pc, op) ∈ Top.matrixSites := by
  have hk := Ref.site_kind s
  unfold Ref.kindAt at hk
  cases hc : kernel.code[s.pc]? with
  | none => rw [hc] at hk; cases hk
  | some ins =>
    rw [hc, Option.bind_some] at hk
    rw [siteCls_kind] at h
    obtain ⟨i, hi⟩ := op_of_matrix_kind hk h
    refine ⟨i.op, ?_⟩
    unfold Top.matrixSites
    refine List.mem_filterMap.mpr ⟨(ins, s.pc), List.mem_zipIdx_iff_getElem?.mpr hc, ?_⟩
    simp only [hi]

/-- A matrix site is in the compute loop, before the named barrier. -/
theorem matrix_pc_range {s : Site} (h : siteCls s = .matrix) : 2106 ≤ s.pc ∧ s.pc ≤ 2912 := by
  obtain ⟨op, hm⟩ := matrix_pc h
  have := List.all_eq_true.mp matrixSites_all _ hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2⟩

/-- The matrix events of the tile before a site of the tile loops: the matrix instructions
below it, and its own at the row write of an `stmatrix`. -/
theorem matBefore_eq {s : Site} (h : s.pc ≤ 3112) :
    matBefore s = (Top.matrixSites.filter (fun e => e.1 < s.pc)).length +
      (if s.kind = .matrixStoreWr then 1 else 0) := by
  unfold matBefore
  rw [ite_eq_right (by omega)]
  cases s <;> rfl

/-- The count of the entries of a list of pairs below a first component that is in the list is
below the count for a larger bound. -/
theorem filter_fst_lt_succ_le {α : Type} {l : List (Nat × α)} {p p' : Nat} {a : α}
    (hp : (p, a) ∈ l) (h : p < p') :
    (l.filter (fun e => e.1 < p)).length + 1 ≤ (l.filter (fun e => e.1 < p')).length := by
  have h1 := filter_lt_succ_le (l := l.map (·.1)) (List.mem_map.mpr ⟨_, hp, rfl⟩) h
  simpa [List.filter_map, Function.comp_def] using h1

/-- **Fewer than 182 matrix events of the tile precede a matrix event.** -/
theorem matBefore_lt {s : Site} (h : siteCls s = .matrix) : matBefore s < 182 := by
  obtain ⟨op, hm⟩ := matrix_pc h
  have hr := matrix_pc_range h
  rw [matBefore_eq (by omega), ← Top.matrixSites_length]
  have hk : s.kind ≠ .matrixStoreWr := by
    intro hk
    rw [siteCls_kind, hk] at h
    cases h
  rw [ite_eq_right hk, Nat.add_zero]
  exact List.length_filter_lt_length_iff_exists.mpr ⟨_, hm, by simp⟩

/-- Two matrix events at one instruction are preceded by the same matrix events. -/
theorem matBefore_eq_of_pc {s s' : Site} (hs : siteCls s = .matrix)
    (hs' : siteCls s' = .matrix) (h : s'.pc = s.pc) : matBefore s' = matBefore s := by
  have hr := matrix_pc_range hs
  have hk : ∀ {u : Site}, siteCls u = .matrix → u.kind ≠ .matrixStoreWr := by
    intro u hu hk
    rw [siteCls_kind, hk] at hu
    cases hu
  rw [matBefore_eq (by omega), matBefore_eq (by omega), ite_eq_right (hk hs),
    ite_eq_right (hk hs'), h]

/-- The sites that share the instruction of a matrix event: the matrix event itself, the row
write after it (of an `stmatrix`), or the row read before it (of an `ldmatrix`). -/
theorem kind_at_matrix {κ κ' : SiteKind} (h : kindCls κ = .matrix)
    (hb : baseKind κ' = baseKind κ) :
    kindCls κ' = .matrix ∨ κ' = .matrixStoreWr ∨ (κ' = .matrixLoad ∧ κ = .matrixLoadMx) := by
  cases κ <;> first | exact absurd h (by decide) | (cases κ' <;> revert hb <;> decide)

/-- **The count `matBefore` orders the positions.** A site of the startup or of the tile loops
with at most as many matrix events of the tile as a matrix site is at an earlier instruction,
or at the same instruction, and then it is that matrix event or the row read before it. -/
theorem mat_order {s s' : Site} (hs : siteCls s = .matrix) (hpc : s'.pc ≤ 3112)
    (hle : matBefore s' ≤ matBefore s) :
    s'.pc < s.pc ∨ (s'.pc = s.pc ∧ (siteCls s' = .matrix ∨ s'.sub < s.sub)) := by
  obtain ⟨op, hm⟩ := matrix_pc hs
  have hr := matrix_pc_range hs
  have hk : s.kind ≠ .matrixStoreWr := by
    intro hk
    rw [siteCls_kind, hk] at hs
    cases hs
  rw [matBefore_eq hpc, matBefore_eq (by omega), ite_eq_right hk, Nat.add_zero] at hle
  rcases Nat.lt_trichotomy s'.pc s.pc with hlt | heq | hgt
  · exact .inl hlt
  · refine .inr ⟨heq, ?_⟩
    rw [siteCls_kind] at hs ⊢
    rcases kind_at_matrix hs (base_kind_of_pc heq) with h | h | ⟨h1, h2⟩
    · exact .inl h
    · rw [ite_eq_left h, heq] at hle
      omega
    · refine .inr ?_
      rw [sub_kind, sub_kind, h1, h2]
      decide
  · have := filter_fst_lt_succ_le hm hgt
    omega

end PTX.Kernels.FlashKdaFwd.Proof.Progress
