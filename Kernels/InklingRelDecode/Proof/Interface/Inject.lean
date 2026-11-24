-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Reads

@[expose] public section

/-!
# The output stores' addresses

Distinct output elements have disjoint words: the footprint of `OPart[split, token, head, col]`
or `LsePart[split, token, head]` determines its coordinates (`oLoc_overlap`, `lseLoc_overlap`),
and an `OPart` word and an `LsePart` word never overlap (`oLoc_lseLoc_apart`, from
`Pre.oApartLse`). So two global writes of an execution whose footprints overlap are stores of the
same element (`global_writes_same_element`): the coordinates the epilogue's registers give
(`Epi.outSplit`, `Epi.outToken`, `Epi.outHead`, the column) agree.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Mixed radix: `n * m + a` determines `n` and `a` for `a < m`. -/
theorem mix {n n' a b m : Nat} (ha : a < m) (hb : b < m) (h : n * m + a = n' * m + b) :
    n = n' ∧ a = b := by
  rcases Nat.lt_trichotomy n n' with hlt | rfl | hgt
  · exfalso
    have := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at this
    omega
  · exact ⟨rfl, by omega⟩
  · exfalso
    have := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hgt)
    rw [Nat.succ_mul] at this
    omega

/-- **The element index of `OPart` determines its coordinates.** -/
theorem oIdx_inj {s t h d s' t' h' d' : Nat} (ht : t < Q.nTok) (ht' : t' < Q.nTok)
    (hh : h < heads) (hh' : h' < heads) (hd : d < headDim) (hd' : d' < headDim)
    (e : ((s * Q.nTok + t) * heads + h) * headDim + d =
      ((s' * Q.nTok + t') * heads + h') * headDim + d') :
    s = s' ∧ t = t' ∧ h = h' ∧ d = d' := by
  obtain ⟨e1, e2⟩ := mix hd hd' e
  obtain ⟨e3, e4⟩ := mix hh hh' e1
  obtain ⟨e5, e6⟩ := mix ht ht' e3
  exact ⟨e5, e6, e4, e2⟩

/-- **Two `OPart` words that overlap are the same element.** -/
theorem oLoc_overlap {s t h d s' t' h' d' : Nat} (ht : t < Q.nTok)
    (ht' : t' < Q.nTok) (hh : h < heads) (hh' : h' < heads) (hd : d < headDim)
    (hd' : d' < headDim) {x : Nat}
    (h1 : (oLoc Q s t h d).addr ≤ x ∧ x < (oLoc Q s t h d).addr + 4)
    (h2 : (oLoc Q s' t' h' d').addr ≤ x ∧ x < (oLoc Q s' t' h' d').addr + 4) :
    s = s' ∧ t = t' ∧ h = h' ∧ d = d' := by
  apply oIdx_inj ht ht' hh hh' hd hd'
  simp only [oLoc] at h1 h2
  omega

/-- **Two `LsePart` words that overlap are the same element.** -/
theorem lseLoc_overlap {s t h s' t' h' : Nat} (ht : t < Q.nTok) (ht' : t' < Q.nTok)
    (hh : h < heads) (hh' : h' < heads) {x : Nat}
    (h1 : (lseLoc Q s t h).addr ≤ x ∧ x < (lseLoc Q s t h).addr + 4)
    (h2 : (lseLoc Q s' t' h').addr ≤ x ∧ x < (lseLoc Q s' t' h').addr + 4) :
    s = s' ∧ t = t' ∧ h = h' := by
  simp only [lseLoc] at h1 h2
  have e : (s * Q.nTok + t) * heads + h = (s' * Q.nTok + t') * heads + h' := by omega
  obtain ⟨e3, e4⟩ := mix hh hh' e
  obtain ⟨e5, e6⟩ := mix ht ht' e3
  exact ⟨e5, e6, e4⟩

/-- **An `OPart` word and an `LsePart` word do not overlap.** -/
theorem oLoc_lseLoc_apart (hpre : Pre Q L mem0) {s t h d s' t' h' : Nat} (hs : s < Q.splits)
    (ht : t < Q.nTok) (hh : h < heads) (hd : d < headDim) (hs' : s' < Q.splits)
    (ht' : t' < Q.nTok) (hh' : h' < heads) {x : Nat}
    (h1 : (oLoc Q s t h d).addr ≤ x ∧ x < (oLoc Q s t h d).addr + 4)
    (h2 : (lseLoc Q s' t' h').addr ≤ x ∧ x < (lseLoc Q s' t' h').addr + 4) : False := by
  have a1 := oLoc_range (Q := Q) s t h d hs ht hh hd
  have a2 := lseLoc_range (Q := Q) s' t' h' hs' ht' hh'
  have ap := hpre.oApartLse
  unfold Apart at ap
  omega

theorem col_lt (L : Launch) (g : Nat) (j : Fin 64) : Epi.outCol0 L g + j.val < headDim := by
  have : Epi.halfM (g % L.block) ≤ 1 := by unfold Epi.halfM; omega
  have := j.isLt
  unfold Epi.outCol0 headDim
  omega

/-- **Two global writes of an execution whose footprints overlap are stores of the same output
element**: both are `OPart` stores with the same split, token, head and column, or both are
`LsePart` stores with the same split, token and head. -/
theorem global_writes_same_element (hpre : Pre Q L mem0) (hf : ThreadFacts Q L mem0 X)
    {g k g' k' pc pc' : Nat} {a a' : Acc} {bs bs' : List Byte} (hg : g < L.threads)
    (hg' : g' < L.threads) (he : X.get (g, k) = some ⟨pc, .wr a bs⟩)
    (he' : X.get (g', k') = some ⟨pc', .wr a' bs'⟩) (hsp : a.loc.space = .global)
    (hsp' : a'.loc.space = .global) {l : Loc} (hc : a.Covers l) (hc' : a'.Covers l) :
    ∃ d d' : Epi.D, St Q L X g k = some (some (.d (.epi d))) ∧
      St Q L X g' k' = some (some (.d (.epi d'))) ∧
      ((∃ j j' : Fin 64, d.site = .stO j ∧ d'.site = .stO j' ∧
          Epi.outSplit L g = Epi.outSplit L g' ∧ Epi.outToken Q L g = Epi.outToken Q L g' ∧
          Epi.outHead L g = Epi.outHead L g' ∧
          Epi.outCol0 L g + j.val = Epi.outCol0 L g' + j'.val) ∨
        (d.site = .stLse ∧ d'.site = .stLse ∧ Epi.outSplit L g = Epi.outSplit L g' ∧
          Epi.outToken Q L g = Epi.outToken Q L g' ∧ Epi.outHead L g = Epi.outHead L g')) := by
  obtain ⟨d, hσ, -, hm, hrv, hcase⟩ := hf.global_wr hg he hsp
  obtain ⟨d', hσ', -, hm', hrv', hcase'⟩ := hf.global_wr hg' he' hsp'
  obtain ⟨hx, -, ht, hh⟩ := Epi.row_coords hpre hg hm hrv
  obtain ⟨hx', -, ht', hh'⟩ := Epi.row_coords hpre hg' hm' hrv'
  have hn : Epi.outToken Q L g < Q.nTok := ht
  have hn' : Epi.outToken Q L g' < Q.nTok := ht'
  have hhh : Epi.outHead L g < heads := hh
  have hhh' : Epi.outHead L g' < heads := hh'
  have hxx : Epi.outSplit L g < Q.splits := hx
  have hxx' : Epi.outSplit L g' < Q.splits := hx'
  refine ⟨d, d', hσ, hσ', ?_⟩
  obtain ⟨-, -, h1, h2⟩ := hc
  obtain ⟨-, -, h1', h2'⟩ := hc'
  rcases hcase with ⟨j, hj, v, -, -, hacc⟩ | ⟨hj, v, -, -, hacc⟩
  · rcases hcase' with ⟨j', hj', v', -, -, hacc'⟩ | ⟨hj', v', -, -, hacc'⟩
    · subst hacc
      subst hacc'
      simp only [EvD.wordAcc] at h1 h2 h1' h2'
      obtain ⟨e1, e2, e3, e4⟩ := oLoc_overlap hn hn' hhh hhh' (col_lt L g j) (col_lt L g' j')
        ⟨h1, h2⟩ ⟨h1', h2'⟩
      exact .inl ⟨j, j', hj, hj', e1, e2, e3, e4⟩
    · subst hacc
      subst hacc'
      simp only [EvD.wordAcc] at h1 h2 h1' h2'
      exact (oLoc_lseLoc_apart hpre hxx hn hhh (col_lt L g j) hxx' hn' hhh'
        ⟨h1, h2⟩ ⟨h1', h2'⟩).elim
  · rcases hcase' with ⟨j', hj', v', -, -, hacc'⟩ | ⟨hj', v', -, -, hacc'⟩
    · subst hacc
      subst hacc'
      simp only [EvD.wordAcc] at h1 h2 h1' h2'
      exact (oLoc_lseLoc_apart hpre hxx' hn' hhh' (col_lt L g' j') hxx hn hhh
        ⟨h1', h2'⟩ ⟨h1, h2⟩).elim
    · subst hacc
      subst hacc'
      simp only [EvD.wordAcc] at h1 h2 h1' h2'
      obtain ⟨e1, e2, e3⟩ := lseLoc_overlap hn hn' hhh hhh' ⟨h1, h2⟩ ⟨h1', h2'⟩
      exact .inr ⟨hj, hj', e1, e2, e3⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
