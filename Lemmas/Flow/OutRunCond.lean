-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.OutLit

@[expose] public section

/-! # What a local path through a run of items says

`xRun` gives the end of a run under its condition and a dead thread otherwise. A state the local
steps reach in the middle of a run is another matter: the thread is not dead there, it has taken
the first steps. `XItem.tau` says that a local step of an item's instruction is the item's step
and the item's condition holds (otherwise the instruction faults and there is no local step).
`xRun_cond` is the condition of a run that succeeded; `xRun_path` says that every state the local
steps reach from the start of a run is the state after a prefix of the items (or goes on from the
end), with the prefix's condition and registers. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **A local step of an item's instruction** is the item's step, and its condition holds. -/
theorem XItem.tau (it : XItem) {V : Nat → Value} {dom : List Nat} {t c : TState}
    (hc : it.codeB K t.pc = true) (hf : t.fault = none)
    (hd : ∀ r ∈ dom, t.regs r = some (V r)) (hrd : ∀ r ∈ it.reads, r ∈ dom)
    (hq : it.req V = true) (hl : it.localB = true) (hS : SegFreePc A t.pc)
    (hR : it.Rule A L g t) (h : Tau K A L g t c) : it.cond V ∧ c = it.post V t := by
  have hex := it.exec hS hR (fun r hr => hd r (hrd r hr)) hq
  have hcode := OItem.instrB_eq hc
  by_cases hok : it.cond V
  · refine ⟨hok, ?_⟩
    have := tau_of_ok hcode hl hf (hex.1 hok)
    have h' : out K A L g t = .tau c := h
    rw [this] at h'
    exact (Out.tau.inj h').symm
  · obtain ⟨f, he⟩ := hex.2 hok
    have hl' : it.op.isLocal = true := hl
    have : out K A L g t = .ev (.ub f) := by
      simp [out, hf, hcode, guardHolds, hl', he, pure, Except.pure]
    have h' : out K A L g t = .tau c := h
    rw [this] at h'
    exact absurd h' (by simp)

/-- **A run that succeeded satisfies the condition of its items.** -/
theorem xRun_cond : ∀ (items : List XItem) (V : Nat → Value) (dom : List Nat) (t t' : TState),
    xCodeB K t.pc items = true → t.fault = none → (∀ r ∈ dom, t.regs r = some (V r)) →
    xReadsB dom items = true → xReq V items = true → xLocalB items = true →
    XRules A L g t.pc items → run K A L g items.length t = some t' → xCond V items
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | it :: its, V, dom, t, t', hc, hf, hd, hrd, hq, hl, hR, hr => by
    simp only [xCodeB, Bool.and_eq_true] at hc
    simp only [xLocalB, Bool.and_eq_true] at hl
    simp only [xReadsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hrd
    simp only [xReq, Bool.and_eq_true] at hq
    simp only [XRules] at hR
    simp only [List.length_cons, run] at hr
    cases hs : tauStep K A L g t with
    | none => simp [hs] at hr
    | some c =>
      rw [hs, Option.bind_some] at hr
      obtain ⟨hok, rfl⟩ := it.tau hc.1 hf hd hrd.1 hq.1 hl.1 hR.1.1 (hR.1.2 t rfl)
        (tauStep_iff.mp hs)
      obtain ⟨-, hpc1, -, -, hf1, -, hw1⟩ := (it.step hc.1 hf hd hrd.1 hq.1 hl.1 hR.1.1
        (hR.1.2 t rfl)).1 hok
      exact ⟨hok, xRun_cond its _ _ _ t' (by rw [hpc1]; exact hc.2) (hf1.trans hf) hw1 hrd.2
        hq.2 hl.2 (by rw [hpc1]; exact hR.2) hr⟩

/-- **The states local steps reach from the start of a run**: the state after a prefix of the
items (with the prefix's condition and registers), from which the steps go on if the prefix is
the whole run. -/
theorem xRun_path : ∀ (items : List XItem) (V : Nat → Value) (dom : List Nat) (t : TState),
    xCodeB K t.pc items = true → t.fault = none → (∀ r ∈ dom, t.regs r = some (V r)) →
    xReadsB dom items = true → xReq V items = true → xLocalB items = true →
    XRules A L g t.pc items → ∀ t', Relation.ReflTransGen (Tau K A L g) t t' →
    ∃ j ≤ items.length, ∃ t1, Relation.ReflTransGen (Tau K A L g) t1 t' ∧
      (j = items.length ∨ t1 = t') ∧ run K A L g j t = some t1 ∧ t1.pc = t.pc + j ∧
      t1.sub = t.sub ∧ t1.acc = t.acc ∧ t1.fault = t.fault ∧ xCond V (items.take j) ∧
      (∀ r, r ∉ xWrites (items.take j) → t1.regs r = t.regs r) ∧
      ∀ r ∈ xWrites (items.take j) ++ dom, t1.regs r = some (xFinal V (items.take j) r)
  | [], V, dom, t, _, _, hd, _, _, _, _, t', h =>
    ⟨0, le_rfl, t, h, .inl rfl, rfl, rfl, rfl, rfl, rfl, trivial, fun _ _ => rfl,
      fun r hr => hd r (by simpa [xWrites] using hr)⟩
  | it :: its, V, dom, t, hc, hf, hd, hrd, hq, hl, hR, t', h => by
    rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hcs, hct⟩
    · exact ⟨0, Nat.zero_le _, t, .refl, .inr rfl, rfl, rfl, rfl, rfl, rfl, trivial,
        fun _ _ => rfl, fun r hr => hd r (by simpa [xWrites] using hr)⟩
    simp only [xCodeB, Bool.and_eq_true] at hc
    simp only [xLocalB, Bool.and_eq_true] at hl
    simp only [xReadsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hrd
    simp only [xReq, Bool.and_eq_true] at hq
    simp only [XRules] at hR
    obtain ⟨hok, rfl⟩ := it.tau hc.1 hf hd hrd.1 hq.1 hl.1 hR.1.1 (hR.1.2 t rfl) hcs
    obtain ⟨hr1, hpc1, hsub1, hacc1, hf1, hfr1, hw1⟩ := (it.step hc.1 hf hd hrd.1 hq.1 hl.1
      hR.1.1 (hR.1.2 t rfl)).1 hok
    obtain ⟨j, hj, t1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := xRun_path its (it.upd V)
      (it.writes ++ dom) (it.post V t) (by rw [hpc1]; exact hc.2) (hf1.trans hf) hw1 hrd.2
      hq.2 hl.2 (by rw [hpc1]; exact hR.2) t' hct
    refine ⟨j + 1, Nat.succ_le_succ hj, t1, h1, by simpa using h2, ?_, by rw [h4, hpc1]; omega,
      h5.trans hsub1, h6.trans hacc1, h7.trans hf1, ⟨hok, h8⟩, fun r hr => ?_, fun r hr => ?_⟩
    · rw [Nat.add_comm]
      exact run_comp hr1 h3
    · simp only [List.take_succ_cons, xWrites, List.flatMap_cons, List.mem_append, not_or] at hr
      rw [h9 r hr.2, hfr1 r hr.1]
    · refine h10 r ?_
      simp only [List.take_succ_cons, xWrites, List.flatMap_cons, List.mem_append] at hr ⊢
      tauto

/-- The values after a run are those after its first `j` items and then the rest. -/
theorem xFinal_take_drop : ∀ (items : List XItem) (V : Nat → Value) (j : Nat),
    xFinal V items = xFinal (xFinal V (items.take j)) (items.drop j)
  | [], V, j => by simp [xFinal]
  | it :: its, V, 0 => by simp [xFinal]
  | it :: its, V, j + 1 => by
    simp only [List.take_succ_cons, List.drop_succ_cons, xFinal]
    exact xFinal_take_drop its _ j

theorem XItem.upd_other_of {V : Nat → Value} {it : XItem} {r : Nat} (h : r ∉ it.writes) :
    it.upd V r = V r := by
  unfold XItem.upd
  rw [← XItem.vals_keys V it] at h
  generalize it.vals V = l at h
  induction l generalizing V with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.foldl_cons]
    rw [ih h.2, Function.update_of_ne h.1]

/-- A register the rest of a run does not write has its value after the whole run already after
a prefix. -/
theorem xFinal_take_eq (items : List XItem) (V : Nat → Value) (j r : Nat)
    (h : r ∉ xWrites (items.drop j)) : xFinal V (items.take j) r = xFinal V items r := by
  rw [xFinal_take_drop items V j]
  generalize items.drop j = rest at h
  generalize xFinal V (items.take j) = W
  induction rest generalizing W with
  | nil => rfl
  | cons it its ih =>
    simp only [xWrites, List.flatMap_cons, List.mem_append, not_or] at h
    have h2 : xFinal (it.upd W) its r = it.upd W r := (ih (by simpa [xWrites] using h.2) _).symm
    have h3 : it.upd W r = W r := XItem.upd_other_of h.1
    simp only [xFinal]
    rw [h2, h3]

end
end PTX.Flow
