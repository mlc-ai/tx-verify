-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.Query
public import Kernels.InklingRelDecode.Proof.Prologue.Data.QueryReach
public import Kernels.InklingRelDecode.Proof.Prologue.Data.QueryPack
public import Kernels.InklingRelDecode.Proof.Prologue.Data.QuerySite
import Lemmas.Flow.RunFrame

@[expose] public section

/-! # The facts after a query load

The first event after a load holds the facts of the next query site: the halves loaded so far,
and the zero halves of the loads it skips. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

noncomputable section

theorem ldq_tags (j : Fin 64) : ∀ τ ∈ tags (.ldq j),
    τ = .scale ∨ τ = .zero ∨ ∃ k : Fin 64, k < j ∧ τ = .qh k := by
  intro τ hτ
  simp only [tags, oldTags, pos, early, qTags, qhs, List.mem_append, List.mem_cons,
    List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
    List.not_mem_nil, or_false, Bool.false_eq_true, ↓reduceIte] at hτ
  rcases hτ with h | h | ⟨k, ⟨-, hk⟩, rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨k, hk, rfl⟩)

/-- The facts of a state in terms of its tags. -/
theorem mem_dF {Q L g} {d : D} {τ : Tag} (h : τ ∈ tags d.c.site) :
    (τ.reg, τ.val Q L g d) ∈ dF Q L g d := List.mem_map.mpr ⟨τ, h, rfl⟩

/-- **A load changes only its half**: the data facts a load's successor keeps have their value. -/
theorem val_ldq {L g} {d d' : D} {j : Fin 64} {v : Value} {s' : Site}
    (hon : queryOn (g % L.block) (j.val / 16) d.c = true)
    (hcc : d'.c = {d.c with site := s'}) (hv : d'.v = ⟨d.v.pay, Function.update d.v.q j v⟩) :
    ∀ k : Fin 64, qv L g d' k = if k = j then v else qv L g d k := by
  intro k
  have hq : ∀ n, queryOn (g % L.block) n d'.c = queryOn (g % L.block) n d.c := fun n => by
    rw [hcc]; rfl
  by_cases hk : k = j
  · subst hk; simp [qv, hq, hon, hv]
  · simp [qv, hq, hv, hk, Function.update_of_ne]

theorem val_ldq_tags {L g Q} {d d' : D} {j : Fin 64} {v : Value} {s' : Site}
    (hon : queryOn (g % L.block) (j.val / 16) d.c = true)
    (hcc : d'.c = {d.c with site := s'}) (hv : d'.v = ⟨d.v.pay, Function.update d.v.q j v⟩)
    (hs : d.c.site = .ldq j) : ∀ τ ∈ tags d.c.site, τ.val Q L g d' = τ.val Q L g d := by
  intro τ hτ
  rw [hs] at hτ
  rcases ldq_tags j τ hτ with rfl | rfl | ⟨k, hk, rfl⟩
  · rfl
  · rfl
  · simp [Tag.val, val_ldq hon hcc hv, Fin.ne_of_lt hk]

/-- The facts after a load. -/
abbrev ldqF (Q : Params) (L : Launch) (g : Nat) (w : Value) (d : D) (j : Fin 64) (v : Value) :=
  (checkedCode Q L g w).facts d.c ++ dF Q L g d ++ [(qDst j, v)]

theorem query_later : ∀ j n : Fin 64, j < n → queryPred n ∈ ctlLive (queryPc j) := by
  decide +kernel

theorem tag_regs_lt : ∀ (j k : Fin 64), j < k → ∀ τ ∈ tags (.ldq j), τ.reg ≠ qDst k := by
  decide +kernel

/-- The registers of the facts after a load are not those of the later loads. -/
theorem ldqF_fresh {Q L g w} {d : D} {j : Fin 64} {v : Value} (hs : d.c.site = .ldq j)
    (k : Fin 64) (hk : j < k) : qDst k ∉ (ldqF Q L g w d j v).map Prod.fst := by
  have h1 : qDst k ∉ ctlLive d.c.site.pc := fun h => by
    have := (List.mem_filter.mp h).2
    rw [query_data k] at this; cases this
  have := fresh_facts (Q := Q) (L := L) (g := g) (w := w) (d := d) h1 (fun τ hτ => by
    rw [hs] at hτ; exact tag_regs_lt j k hk τ hτ)
  simp only [ldqF, List.map_append, List.mem_append, List.map_cons, List.map_nil,
    List.mem_singleton, not_or]
  refine ⟨?_, fun h => ?_⟩
  · simpa using this
  · have := qDst_inj _ _ h.symm; subst this; exact absurd hk (lt_irrefl _)

theorem ldq_mem : ∀ j : Fin 64, .scale ∈ tags (.ldq j) ∧ .zero ∈ tags (.ldq j) ∧
    ∀ k : Fin 64, k < j → .qh k ∈ tags (.ldq j) := by decide +kernel

theorem qv_off {L g} {d : D} {k : Fin 64} (h : queryOn (g % L.block) (k.val / 16) d.c = false) :
    qv L g d k = zeroV := by simp [qv, h, zeroV]

/-- The guard of a skipped load is a fact of the state. -/
theorem guard_mem {Q L g w} {d : D} {j n : Fin 64} {v : Value} (hs : d.c.site = .ldq j)
    (hj : j < n) (h : queryOn (g % L.block) (n.val / 16) d.c = false) :
    (queryPred n, Value.pred false) ∈ ldqF Q L g w d j v := by
  refine List.mem_append_left _ (List.mem_append_left _ ?_)
  have key : queryPred n ∈ ctlLive d.c.site.pc := by rw [hs]; exact query_later j n hj
  exact mem_factsFrom_eq (v := valueOf Q L g w d.c) key (by rw [query_value, h])

theorem ldq_zero {Q L g w} {d : D} {j : Fin 64} {v : Value} (hs : d.c.site = .ldq j) :
    (199, zeroV) ∈ ldqF Q L g w d j v :=
  List.mem_append_left _ (List.mem_append_right _
    (mem_dF (Q := Q) (L := L) (g := g) (d := d) (τ := .zero) (hs ▸ (ldq_mem j).2.1)))

/-- The halves loaded so far, and the one this load returned, are facts. -/
theorem ldq_half {Q L g w} {d d' : D} {j : Fin 64} {v : Value} {s' : Site}
    (hs : d.c.site = .ldq j) (hon : queryOn (g % L.block) (j.val / 16) d.c = true)
    (hcc : d'.c = {d.c with site := s'}) (hv : d'.v = ⟨d.v.pay, Function.update d.v.q j v⟩)
    (k : Fin 64) (hk : k ≤ j) : (qDst k, qv L g d' k) ∈ ldqF Q L g w d j v := by
  rcases hk.lt_or_eq with hk | rfl
  · have h1 : (qDst k, qv L g d k) ∈ dF Q L g d :=
      mem_dF (τ := .qh k) (Q := Q) (L := L) (g := g) (d := d) (hs ▸ (ldq_mem j).2.2 k hk)
    have e : qv L g d' k = qv L g d k := by simp [val_ldq hon hcc hv k, Fin.ne_of_lt hk]
    rw [e]
    exact List.mem_append_left _ (List.mem_append_right _ h1)
  · simp [val_ldq hon hcc hv, ldqF]

/-- **The facts of the next load after a load**, the loads between skipped. -/
theorem ldq_reach_lt {Q L g w} {d d' : D} {j : Fin 64} {v : Value} {hi : Nat}
    (hs : d.c.site = .ldq j) (hon : queryOn (g % L.block) (j.val / 16) d.c = true)
    (hcc : d'.c = {d.c with site := qSiteAt hi}) (hv : d'.v = ⟨d.v.pay, Function.update d.v.q j v⟩)
    (hhi : hi < 64) (hjh : j.val < hi)
    (hoff : ∀ n, j.val < n → n < hi → queryOn (g % L.block) (n / 16) d.c = false) :
    Reach kernel Assumptions.all L g ((Site.ldq j).pc + 1) (ldqF Q L g w d j v) (dF Q L g d') := by
  have hq : ∀ n, queryOn (g % L.block) n d'.c = queryOn (g % L.block) n d.c := fun n => by
    rw [hcc]; rfl
  have hd' : d'.c.site = .ldq ⟨hi, hhi⟩ := by rw [hcc]; simp [qSiteAt, hhi]
  have hz := ldq_zero hs (Q := Q) (L := L) (g := g) (w := w) (v := v)
  have hq' := fun k hk => ldq_half (Q := Q) (w := w) hs hon hcc hv k hk
  have hj63 : j.val < 63 := by omega
  have lt1 : (⟨j.val, by omega⟩ : Fin 64) < ⟨j.val + 1, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
  have m1 := move_next (L := L) (g := g) (S := ldqF Q L g w d j v) ⟨j.val, hj63⟩ hz
    (ldqF_fresh hs ⟨j.val + 1, by omega⟩ lt1)
  have sk := skip_data (L := L) (g := g) (S := ldqF Q L g w d j v) ⟨j.val + 1, by omega⟩
    ⟨hi, hhi⟩ (Fin.mk_le_mk.mpr (by omega)) hz
    (fun k hk => ldqF_fresh hs k
      (Fin.lt_def.mpr (by have := Fin.lt_def.mp hk; simp at this; omega)))
    (fun n h1 h2 => guard_mem hs
      (Fin.lt_def.mpr (by have := Fin.le_def.mp h1; simp at this; omega))
      (hoff n (by have := Fin.le_def.mp h1; simp at this; omega)
        (by have := Fin.lt_def.mp h2; simpa using this)))
  refine reach_tags d' (by rw [hd']; rfl) (by simp [Site.pc]; omega)
    (by simp [queryPc, Site.pc]; omega) (by simp [queryPc, Site.pc]; omega) (m1.comp sk)
    fun τ hτ => .inr ?_
  rw [hd'] at hτ
  have hkey : ∀ k : Fin 64, k.val < hi → (qDst k, qv L g d' k) ∈
      (qDst ⟨j.val + 1, by omega⟩, zeroV) :: ldqF Q L g w d j v ++ zs (j.val + 1 + 1) (hi + 1) := by
    intro k hk
    by_cases hkj : k ≤ j
    · exact List.mem_append_left _ (List.mem_cons_of_mem _ (hq' k hkj))
    · have hkj' : j.val < k.val := by have := not_le.mp hkj; exact Fin.lt_def.mp this
      have hz' : qv L g d' k = zeroV := qv_off (by rw [hq]; exact hoff k hkj' hk)
      rw [hz']
      by_cases hk1 : k.val = j.val + 1
      · exact List.mem_append_left _ (by
          rw [show k = ⟨j.val + 1, by omega⟩ from Fin.ext hk1]; exact List.mem_cons_self ..)
      · exact List.mem_append_right _ (mem_zs.mpr ⟨k, by omega, by omega, rfl⟩)
  rcases ldq_tags ⟨hi, hhi⟩ τ hτ with rfl | rfl | ⟨k, hk, rfl⟩
  · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_append_right _ (mem_dF (hs ▸ (ldq_mem j).1)))))
  · exact List.mem_append_left _ (List.mem_cons_of_mem _ hz)
  · exact hkey k hk

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
