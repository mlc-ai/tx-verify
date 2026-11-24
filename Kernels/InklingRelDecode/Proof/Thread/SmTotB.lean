-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmTotA

@[expose] public section

/-! # The row maximum on any words (pcs 1764-1837)

The tree of `SmMax` with the values of `SmTot`: after `c` instructions the facts are the live
registers valued by the register-value list `rvSt w c` (the unpacked words `w` and the `maxE`
outcomes) in front of the mask's table of the state `d1` at pc 1764. The unpack of a pair register
faults where its value is not two four-byte words, a maximum where `maxE` faults; the thread is
dead there (`SegD`). The condition of the whole tree is `RvOk`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Classical

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

/-- **One instruction that writes `lo` and `hi` with the outcome `E`**, between facts by the
table `v` and facts by a table `v'` that gives them the outcome's values and agrees with `v`
elsewhere. -/
theorem SegD.twoT {K : Kernel} {A : List Assumption} {pc lo hi : Nat} {op : Op}
    {liveS liveT : List Nat} {v v' : Nat → Value} {E : Exec (Value × Value)}
    (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ t, At t pc (factsFrom liveS v) →
      execLocalA A L g t op = E.map fun x => PTX.next (setReg (setReg t lo x.1) hi x.2))
    (hne : lo ≠ hi)
    (hd : ∀ x, E = .ok x → v' lo = x.1 ∧ v' hi = x.2)
    (hcov : ∀ r ∈ liveT, r = lo ∨ r = hi ∨ (r ≠ lo ∧ r ≠ hi ∧ r ∈ liveS ∧ v' r = v r)) :
    SegD K A L g 1 pc (factsFrom liveS v) (pc + 1) (factsFrom liveT v') (E.toBool = true) := by
  intro t ht
  have he := hex t ht
  refine ⟨fun hok => ?_, fun hno => ?_⟩
  · rcases hE : E with e | x
    · rw [hE] at hok; cases hok
    rw [hE] at he
    refine ⟨_, run_local hc hl ht he, by simp [PTX.next, setReg, ht.1], ht.2.1, ht.2.2.1,
      ht.2.2.2.1, holds_of_pointwise fun r hr => ?_⟩
    rcases hcov r hr with rfl | rfl | ⟨h1, h2, hrS, hv⟩
    · simp [PTX.next, setReg, Function.update_of_ne hne, (hd x hE).1]
    · simp [PTX.next, setReg, (hd x hE).2]
    · simp only [PTX.next, setReg, Function.update_of_ne h1, Function.update_of_ne h2, hv]
      exact holds_mem ht.2.2.2.2 (mem_factsFrom hrS)
  · rcases hE : E with e | x
    · rw [hE] at he
      exact dead_of_error (hc.symm ▸ by rw [ht.1]) hl ht.2.2.2.1 he
    · rw [hE] at hno; exact absurd rfl hno

/-- `mov.b64 {a, b}, r` on any value: its two halves, or a fault. -/
theorem exec_unpackET {t : TState} {a b r : Nat} {v : Value}
    (hS : Assumption.SegFreePc asms t.pc) (hr : t.regs r = some v) :
    execLocalA asms L g t (.move ⟨.unpack, .int .b 64, [some a, some b], [.reg r]⟩) =
      (unpackE 64 v).map fun x => PTX.next (setReg (setReg t a x.1) b x.2) := by
  rw [hS.exec rfl, execLocalRule_of_none (asms_none (by simp) (by simp))]
  by_cases h1 : v.bytes = 8 <;>
  by_cases h2 : (splitValue 64 v).1.bytes = 4 ∧ (splitValue 64 v).2.bytes = 4 <;>
  simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, hr,
    unpackE, h1, h2, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    Except.map]

/-! ### The register-value list -/

theorem rvSt_succ {w : Nat → Value} {c : Nat} {i : RI} (h : rmCode[c]? = some i) :
    rvSt w (c + 1) = i.updV w (rvSt w c) := by
  unfold rvSt
  rw [List.take_succ, h]
  simp [List.foldl_append]

theorem upd_keys (w : Nat → Value) (i : RI) (st : List (Nat × Value)) (sm : List (Nat × Nat))
    (h : st.map Prod.fst = sm.map Prod.fst) :
    (i.updV w st).map Prod.fst = (i.upd sm).map Prod.fst := by
  cases i <;> simp [RI.updV, RI.upd, h]

/-- The value list and the mask list have the same registers. -/
theorem rvSt_keys (w : Nat → Value) : ∀ c, (rvSt w c).map Prod.fst = (rmSt c).map Prod.fst := by
  intro c
  induction c with
  | zero => rfl
  | succ c ih =>
    rcases h : rmCode[c]? with _ | i
    · have hl : rmCode.length ≤ c := List.getElem?_eq_none_iff.mp h
      have e1 : rmCode.take (c + 1) = rmCode.take c := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      simp only [rvSt, rmSt, e1]
      exact ih
    · rw [rvSt_succ h, rmSt_succ h]
      exact upd_keys w i _ _ ih

theorem lookup_isSome_of_keys {st : List (Nat × Value)} {sm : List (Nat × Nat)} {r : Nat}
    (h : st.map Prod.fst = sm.map Prod.fst) (hs : (sm.lookup r).isSome = true) :
    ∃ v, st.lookup r = some v := by
  induction st generalizing sm with
  | nil =>
    cases sm with
    | nil => simp at hs
    | cons p sm => simp at h
  | cons p st ih =>
    cases sm with
    | nil => simp at h
    | cons q sm =>
      obtain ⟨k, v⟩ := p
      obtain ⟨k', m⟩ := q
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [List.lookup] at hs ⊢
      split
      · exact ⟨v, rfl⟩
      · rename_i hne
        simp only [hne] at hs
        exact ih h hs

theorem lookup_none_of_keys' {st : List (Nat × Value)} {sm : List (Nat × Nat)} {r : Nat}
    (h : st.map Prod.fst = sm.map Prod.fst) (hs : sm.lookup r = none) : st.lookup r = none := by
  induction st generalizing sm with
  | nil => rfl
  | cons p st ih =>
    cases sm with
    | nil => simp at h
    | cons q sm =>
      obtain ⟨k, v⟩ := p
      obtain ⟨k', m⟩ := q
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [List.lookup] at hs ⊢
      split
      · rename_i heq
        simp [heq] at hs
      · rename_i hne
        simp only [hne] at hs
        exact ih h hs

theorem valueEx_lkV {B : Nat → Value} {st : List (Nat × Value)} {r : Nat} {v : Value}
    (h : st.lookup r = some v) : valueEx B st r = lkV st r := by
  simp [valueEx, lkV, h]

/-! ### The steps -/

variable {d1 : D}

theorem valueZ_sP (d1 : D) {q : Nat} (hq : q < 32) :
    valueZ L g d1 (2447 + q) = d1.sP q := by
  rw [valueZ_pair _ hq, valueOf_svp _ hq]
  rfl

theorem seg_rv_unp {c a b q : Nat} (hi : rmCode[c]? = some (.unp a b q))
    (hck : (RI.unp a b q).chk (1764 + c) (rmSt c) = true) :
    SegD kernel asms L g 1 (1764 + c)
      (factsFrom (Flow.live (1764 + c)) (valueEx (valueZ L g d1) (rvSt (colW d1) c)))
      (1764 + c + 1)
      (factsFrom (Flow.live (1764 + c + 1)) (valueEx (valueZ L g d1) (rvSt (colW d1) (c + 1))))
      (((RI.unp a b q).okV d1.sP (rvSt (colW d1) c)) = true) := by
  simp only [RI.chk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.contains_iff_mem] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨hu, hq⟩, hab⟩, hn⟩, hl⟩, hsub⟩, hemu⟩, hzk⟩ := hck
  have hn' : (rmSt c).lookup (2447 + q) = none := Option.isNone_iff_eq_none.mp hn
  have hnv : (rvSt (colW d1) c).lookup (2447 + q) = none :=
    lookup_none_of_keys' (rvSt_keys _ c) hn'
  rw [rvSt_succ hi]
  simp only [RI.okV]
  refine SegD.twoT (lo := a) (hi := b) (unpackAt_spec hu) rfl (fun t h => ?_) (by simpa using hab)
    (fun x hx => ?_) (fun r hr => ?_)
  · have hS : Assumption.SegFreePc asms t.pc := by
      rw [h.1]; exact segFree (by simpa using hemu)
    have hr := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueZ L g d1)
      (rvSt (colW d1) c)) hl)
    rw [show valueEx (valueZ L g d1) (rvSt (colW d1) c) (2447 + q) = d1.sP q by
      simp [valueEx, hnv, valueZ_sP d1 hq]] at hr
    exact exec_unpackET hS hr
  · have hx' := unpackE_eq hx
    subst hx'
    have hab' : a ≠ b := by simpa using hab
    simp only [RI.updV, valueEx_cons_ne _ _ hab', valueEx_cons_self]
    simp [colW, hW, show (2 * q) / 2 = q by omega, show (2 * q + 1) / 2 = q by omega]
  · rcases subX_cov2 hsub r hr with h | h | ⟨h1, h2, h3⟩
    · exact .inl h
    · exact .inr (.inl h)
    · refine .inr (.inr ⟨h1, h2, h3, ?_⟩)
      simp only [RI.updV, valueEx_cons_ne _ _ h1, valueEx_cons_ne _ _ h2]

theorem seg_rv_mx2 {c d a b : Nat} (hi : rmCode[c]? = some (.mx2 d a b))
    (hc : c < 74) (hck : (RI.mx2 d a b).chk (1764 + c) (rmSt c) = true) :
    SegD kernel asms L g 1 (1764 + c)
      (factsFrom (Flow.live (1764 + c)) (valueEx (valueZ L g d1) (rvSt (colW d1) c)))
      (1764 + c + 1)
      (factsFrom (Flow.live (1764 + c + 1)) (valueEx (valueZ L g d1) (rvSt (colW d1) (c + 1))))
      (((RI.mx2 d a b).okV d1.sP (rvSt (colW d1) c)) = true) := by
  simp only [RI.chk, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hck
  obtain ⟨⟨⟨⟨⟨⟨hm, hsa⟩, hsb⟩, hla⟩, hlb⟩, hsub⟩, hemu⟩ := hck
  obtain ⟨va, hva⟩ := lookup_isSome_of_keys (rvSt_keys (colW d1) c) hsa
  obtain ⟨vb, hvb⟩ := lookup_isSome_of_keys (rvSt_keys (colW d1) c) hsb
  rw [rvSt_succ hi]
  simp only [RI.okV]
  refine SegD.oneT (d := d) (maxAt_spec hm) rfl (fun t h => ?_) (fun x hx _ => ?_)
    (fun r hr => ?_)
  · have hE : Assumptions.emuSites.contains t.pc = false := by simpa [h.1] using hemu
    have ra := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueZ L g d1)
      (rvSt (colW d1) c)) hla)
    have rb := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueZ L g d1)
      (rvSt (colW d1) c)) hlb)
    rw [valueEx_lkV hva] at ra
    rw [valueEx_lkV hvb] at rb
    have hp : t.pc = 1764 + c := h.1
    exact exec_maxE2 (idealAtSc (L := L) (g := g) (by decide) hE)
      (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega)) ra rb
  · simp only [RI.updV, valueEx_cons_self, hx]
    rfl
  · by_cases hd : r = d
    · exact .inl hd
    · refine .inr ⟨hd, ((subX_sound hsub r hr).resolve_left (by simpa using hd)).2, ?_⟩
      simp only [RI.updV, valueEx_cons_ne _ _ hd]

theorem seg_rv_mx3 {c d a b e : Nat} (hi : rmCode[c]? = some (.mx3 d a b e))
    (hc : c < 74) (hck : (RI.mx3 d a b e).chk (1764 + c) (rmSt c) = true) :
    SegD kernel asms L g 1 (1764 + c)
      (factsFrom (Flow.live (1764 + c)) (valueEx (valueZ L g d1) (rvSt (colW d1) c)))
      (1764 + c + 1)
      (factsFrom (Flow.live (1764 + c + 1)) (valueEx (valueZ L g d1) (rvSt (colW d1) (c + 1))))
      (((RI.mx3 d a b e).okV d1.sP (rvSt (colW d1) c)) = true) := by
  simp only [RI.chk, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hm, hsa⟩, hsb⟩, hse⟩, hla⟩, hlb⟩, hle⟩, hsub⟩, hemu⟩ := hck
  obtain ⟨va, hva⟩ := lookup_isSome_of_keys (rvSt_keys (colW d1) c) hsa
  obtain ⟨vb, hvb⟩ := lookup_isSome_of_keys (rvSt_keys (colW d1) c) hsb
  obtain ⟨ve, hve⟩ := lookup_isSome_of_keys (rvSt_keys (colW d1) c) hse
  rw [rvSt_succ hi]
  simp only [RI.okV]
  refine SegD.oneT (d := d) (maxAt_spec hm) rfl (fun t h => ?_) (fun x hx _ => ?_)
    (fun r hr => ?_)
  · have hE : Assumptions.emuSites.contains t.pc = false := by simpa [h.1] using hemu
    have ra := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueZ L g d1)
      (rvSt (colW d1) c)) hla)
    have rb := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueZ L g d1)
      (rvSt (colW d1) c)) hlb)
    have re := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueZ L g d1)
      (rvSt (colW d1) c)) hle)
    rw [valueEx_lkV hva] at ra
    rw [valueEx_lkV hvb] at rb
    rw [valueEx_lkV hve] at re
    have hp : t.pc = 1764 + c := h.1
    exact exec_maxE3 (idealAtSc (L := L) (g := g) (by decide) hE)
      (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega)) ra rb re
  · simp only [RI.updV, valueEx_cons_self, hx]
    rfl
  · by_cases hd : r = d
    · exact .inl hd
    · refine .inr ⟨hd, ((subX_sound hsub r hr).resolve_left (by simpa using hd)).2, ?_⟩
      simp only [RI.updV, valueEx_cons_ne _ _ hd]

/-- **One instruction of the tree on any words.** -/
theorem seg_rv1 {c : Nat} (hc : c < 74) {i : RI} (hi : rmCode[c]? = some i) :
    SegD kernel asms L g 1 (1764 + c)
      (factsFrom (Flow.live (1764 + c)) (valueEx (valueZ L g d1) (rvSt (colW d1) c)))
      (1764 + c + 1)
      (factsFrom (Flow.live (1764 + c + 1)) (valueEx (valueZ L g d1) (rvSt (colW d1) (c + 1))))
      ((i.okV d1.sP (rvSt (colW d1) c)) = true) := by
  have hck := rm_chk c hc
  unfold rmChk at hck
  rw [hi] at hck
  cases i with
  | unp a b q => exact seg_rv_unp hi hck
  | mx2 d a b => exact seg_rv_mx2 hi hc hck
  | mx3 d a b e => exact seg_rv_mx3 hi hc hck

/-- The condition of the first `c` instructions of the tree. -/
def RvOkN (P w : Nat → Value) (c : Nat) : Prop :=
  ∀ j < c, ∀ i, rmCode[j]? = some i → i.okV P (rvSt w j) = true

/-- **The first `c` instructions of the tree on any words.** -/
theorem seg_rvN : ∀ c, c ≤ 74 →
    SegD kernel asms L g c 1764 (factsZ L g 1764 d1) (1764 + c)
      (factsFrom (Flow.live (1764 + c)) (valueEx (valueZ L g d1) (rvSt (colW d1) c)))
      (RvOkN d1.sP (colW d1) c) := by
  intro c
  induction c with
  | zero =>
    intro _
    have e : factsZ L g 1764 d1 =
        factsFrom (Flow.live (1764 + 0)) (valueEx (valueZ L g d1) (rvSt (colW d1) 0)) := rfl
    rw [← e]
    exact (SegD.of_seg (Seg.refl _ _)).iff ⟨fun _ j hj => absurd hj (by omega), fun _ => trivial⟩
  | succ c ih =>
    intro hc
    have hi : rmCode[c]? = some rmCode[c] :=
      List.getElem?_eq_getElem (by rw [rmCode_length]; omega)
    refine ((ih (by omega)).comp (seg_rv1 (d1 := d1) (by omega) hi)).iff
      ⟨fun h j hj i hj' => ?_, fun h => ⟨fun j hj i hj' => h j (by omega) i hj',
        h c (by omega) _ hi⟩⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact h.1 j hj i hj'
    · rw [hi] at hj'
      cases hj'
      exact h.2

/-- **The row maximum on any words** (pcs 1764 to 1837): the thread reaches the shuffle with the
tree's registers, or is dead where an unpack or a maximum faults. -/
theorem seg_rowmaxT :
    SegD kernel asms L g 74 1764 (factsZ L g 1764 d1) 1838
      (factsFrom (Flow.live 1838) (valueEx (valueZ L g d1) (rvSt (colW d1) 74)))
      (RvOk d1.sP (colW d1)) :=
  (seg_rvN 74 (le_refl _)).iff ⟨fun h c hc i hi => h c hc i hi, fun h c hc i hi => h c hc i hi⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
