-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProAFlow

@[expose] public section

/-! # The step lemmas of the query loads and stores, once for every site

`step_ldq` is the step of a query load `k` (a guarded scalar load into one register whose value
the table names `dt.q k`): an event fired at the site takes the thread to the successor's state,
or the machine leaves it on a value that is not one 16-bit value. `step_stq` is the step of an
element of a four-element vector store of the packed rows. Each site's lemma in `ProAStep*`
instantiates them with the site's instruction, its frame and its segment. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- The step obligation of site `s`. -/
abbrev StepAt (L : Launch) (g : Nat) (s : Site) : Prop :=
  ∀ {d : D} {t u : TState} {e : Event} {ins : Instr}, d.site = s → Inv L g d → AtS L g d t →
    kernel.code[d.site.pc]? = some ins →
    Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) → Step L g d e u

/-- The frame of a query load: the facts after the load, from those before it. -/
macro "ldq_frame" : tactic => `(tactic| (
  intro dt v R R' hR hfr hrv
  frame_fp hR, hfr
  simp only [Flow.factsFrom, List.map_cons, List.map_nil]
  simp [hrv, valueOf, table, PTX.Flow.lookupLit, qUpd, Site.qIdx]))

/-- **The query load `k` at site `s`** into register `r` under the guard `gr`: on a 16-bit value
`v` the thread continues at `nx` of the data `qUpd dt k v` by the segment `hnx` gives. -/
theorem step_ldq {s : Site} {nx : Dat → Site} {k r gr : Nat}
    {sp : Option StateSpace} {sm : Sem} {el : DType} {ad : Addr}
    (hcode : kernel.code[s.pc]? = some ⟨some (gr, false),
      .mem { kind := .load, space := sp, sem := sm, elem := el, addr := ad, dsts := [some r] }⟩)
    (hnx : ∀ dt v, Inv L g ⟨s, dt⟩ → (∀ j, k + 1 ≤ j → (qUpd dt k v).q j = qZero) →
      (∀ j, ((qUpd dt k v).q j).bytes = 2) →
      Inv L g ⟨nx (qUpd dt k v), qUpd dt k v⟩ ∧ (nx (qUpd dt k v)).sub = 0 ∧
      ∃ n, Seg kernel asms L g n (s.pc + 1) (factsAt L g (s.pc + 1) (qUpd dt k v))
        (nx (qUpd dt k v)).pc (factsAt L g (nx (qUpd dt k v)).pc (qUpd dt k v)))
    (hk : s.qIdx = k := by rfl) (hs0 : s.sub = 0 := by rfl)
    (hn : ∀ dt x bs, next L g ⟨s, dt⟩ ⟨s.pc, .rd x bs⟩ = match rebuild 3 bs with
      | .ok v => if v.bytes = 2 then some (some ⟨nx (qUpd dt k v), qUpd dt k v⟩) else some none
      | .error _ => some none := by intros; rfl)
    (hfr : ∀ dt v (R R' : Nat → Option Value), Holds R (factsAt L g s.pc dt) →
      (∀ x, x ∉ [r] → R' x = R x) → R' r = some v →
      Holds R' (factsAt L g (s.pc + 1) (qUpd dt k v)) := by ldq_frame) :
    StepAt L g s := by
  intro d t u e ins hs hi h hc hf
  obtain ⟨site, dt⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load rfl rfl hf rfl
  have h := h.at hs0 rfl
  have hn := hn dt x bs
  simp only [MemAccess.regs, List.filterMap_cons, id, List.filterMap_nil]
  cases hv : rebuild 3 bs with
  | error f => exact .inl (by simp only [hv] at hn; exact hn)
  | ok v =>
    by_cases hb2 : v.bytes = 2
    · have hU : At (afterLoad t [r] bs) (site.pc + 1)
          (factsAt L g (site.pc + 1) (qUpd dt k v)) := by
        rw [afterLoad_ok h.2.1 h.2.2.1 hv]
        refine ⟨by simp [h.1], rfl, rfl, h.2.2.2.1, hfr dt v _ _ h.2.2.2.2 (fun y hy => ?_) ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          simp [setReg, Function.update_of_ne hy]
        · simp [setReg]
      have hqz : ∀ j, k + 1 ≤ j → (qUpd dt k v).q j = qZero := by
        intro j hj
        simp only [qUpd, Function.update_of_ne (show j ≠ k by omega)]
        exact hi.qz j (by simp only; omega)
      have hqb : ∀ j, ((qUpd dt k v).q j).bytes = 2 := by
        intro j
        by_cases hj : j = k
        · subst hj; simpa [qUpd] using hb2
        · simp only [qUpd, Function.update_of_ne hj]; exact hi.qb j
      obtain ⟨hi', hs0, hseg⟩ := hnx dt v hi hqz hqb
      exact step_of_seg (d' := ⟨nx (qUpd dt k v), qUpd dt k v⟩)
        (by simp only [hv, hb2, ↓reduceIte] at hn; exact hn) hi' hs0 hU hseg
    · exact .inl (by simp only [hv, hb2, ↓reduceIte] at hn; exact hn)

/-- The last query load of the group before `G`: the thread continues at the first load of a
valid group from `G` on, else at the first store (`qSite`), by the segment `hseg`. -/
theorem step_ldq_grp {s : Site} {G k r gr : Nat}
    {sp : Option StateSpace} {sm : Sem} {el : DType} {ad : Addr}
    (hcode : kernel.code[s.pc]? = some ⟨some (gr, false),
      .mem { kind := .load, space := sp, sem := sm, elem := el, addr := ad, dsts := [some r] }⟩)
    (hseg : ∀ dt, (∀ j, 16 * G ≤ j → dt.q j = qZero) → (∀ j, (dt.q j).bytes = 2) →
      ∃ n, Seg kernel asms L g n (s.pc + 1) (factsAt L g (s.pc + 1) dt) (qSite L g dt G).pc
        (factsAt L g (qSite L g dt G).pc dt))
    (hk : s.qIdx = k := by rfl) (hG : G ≤ 3 := by decide) (hkG : k + 1 = 16 * G := by rfl)
    (hs0 : s.sub = 0 := by rfl)
    (hn : ∀ dt x bs, next L g ⟨s, dt⟩ ⟨s.pc, .rd x bs⟩ = match rebuild 3 bs with
      | .ok v => if v.bytes = 2 then some (some ⟨qSite L g (qUpd dt k v) G, qUpd dt k v⟩)
        else some none
      | .error _ => some none := by intros; rfl)
    (hfr : ∀ dt v (R R' : Nat → Option Value), Holds R (factsAt L g s.pc dt) →
      (∀ x, x ∉ [r] → R' x = R x) → R' r = some v →
      Holds R' (factsAt L g (s.pc + 1) (qUpd dt k v)) := by ldq_frame) :
    StepAt L g s :=
  step_ldq (nx := fun dt => qSite L g dt G) hcode (fun dt v hi hqz hqb =>
    ⟨Inv.mv hi _ _ rfl (qSite_prop G hG).2.1
      (fun j hj => hqz j (by
        have := (qSite_prop (L := L) (g := g) (dt := qUpd dt k v) G hG).2.2; omega)) hqb,
      qSite_sub G, hseg _ (fun j hj => hqz j (by omega)) hqb⟩) hk hs0 hn hfr

/-- The last element of a vector store of the packed rows: the thread continues after it, by the
segment `hseg`, to the next site `s'`. -/
theorem step_stq_last {s s' : Site} {pc : Nat} {a : MemAccess}
    (hcode : kernel.code[pc]? = some ⟨none, .mem a⟩)
    (hseg : ∀ dt, (∀ j, (dt.q j).bytes = 2) →
      ∃ n, Seg kernel asms L g n (pc + 1) (factsAt L g (pc + 1) dt) s'.pc (factsAt L g s'.pc dt))
    (hpc : s.pc = pc := by rfl)
    (hn : ∀ dt e, next L g ⟨s, dt⟩ e = some (some ⟨s', dt⟩) := by intros; rfl)
    (ha : a.kind = .store ∧ a.srcs.length = 4 := by exact ⟨rfl, rfl⟩)
    (hsub : s.sub = 3 := by rfl) (hs' : s'.sub = 0 := by rfl)
    (hl : ∀ r ∈ Flow.live (pc + 1), r ∈ Flow.live pc := by table_decide)
    (hinv : ∀ dt, Inv L g ⟨s, dt⟩ → Inv L g ⟨s', dt⟩ := by intro _ hi; exact inv_to hi) :
    StepAt L g s := by
  intro d t u e ins hs hi h hc hf
  obtain ⟨site, dt⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans (hpc ▸ hcode))
  obtain ⟨x, bs, rfl, rfl⟩ := fires_st ha.1 hf
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [afterStore_last (by rw [ha.2, h2]; simp [sub, hsub])]
  have hU : At { t with pc := t.pc + 1, sub := 0 } (pc + 1) (factsAt L g (pc + 1) dt) :=
    ⟨by simp [h1, hpc], rfl, h3, h4, holds_factsFrom_mono (hpc ▸ h5) hl⟩
  have hi' := hinv dt hi
  exact step_of_seg (d' := ⟨s', dt⟩) (hn _ _) hi' hs' hU (hseg dt hi'.qb)

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
