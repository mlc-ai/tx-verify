-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrValues
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrCross

@[expose] public section

/-! # The correction warps' staging writes and their staged arrivals

* A correction thread's write of staging bytes is in its row's line of the stage, after one more
  successful poll of the stage's free barrier than staged arrivals of the stage; the first staged
  arrival of the stage after it follows the stage's proxy fence and the O-free arrival
  (`Counts.fenced`), with no staged arrival between, so every later staged arrival comes after a
  fence that follows the write (`Facts.Corr.staging_access`).
* At its staged arrival of a stage, the thread has written, in the item, every element of the
  stage's sixteen chunks (`Counts.wrote`); the element of byte `off` of the line of half `hh` is
  element `(off % 16) / 4` of store `c % 2` of chunk `4 hh + c / 2`, with `c` the swizzled chunk
  `off / 16 ^^^ lane % 8` (`OutputFacts_corr_cover`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem stagedBar_own (L : Launch) (g st : Nat) :
    stagedBar L (ctaOf L g) st = Correction.ownLoc L g (256 + 8 * st) := by
  simp only [stagedBar, Correction.ownLoc, Correction.sb]

theorem freeBar_own (L : Launch) (g st : Nat) :
    freeBar L (ctaOf L g) st = Correction.ownLoc L g (272 + 8 * st) := by
  simp only [freeBar, Correction.ownLoc, Correction.sb]

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **`OutputFacts.corr_cover`**: at its staged arrival of a stage, a correction thread has written
every byte of its row's two lines of the stage since its previous staged arrival of the stage. -/
theorem OutputFacts_corr_cover {g x pc tx cnt st : Nat} {rel : Bool} {sc : MbarScope}
    (_hg : g < L.threads) (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (hst : st < 2)
    (he : X.get (g, x) = some ⟨pc, .arrive (stagedBar L (ctaOf L g) st) tx cnt rel sc⟩) :
    ∀ hh < 2, ∀ l : Loc, l.space = .shared → l.cta = ctaOf L g →
      lineBase L st hh (rowOf L g) ≤ l.addr → l.addr < lineBase L st hh (rowOf L g) + 128 →
      ∃ i a bs, i < x ∧ X.Writes (g, i) a bs ∧ a.Covers l ∧
        arrivals (stagedBar L (ctaOf L g) st) ((X.tr g).take i) =
          arrivals (stagedBar L (ctaOf L g) st) ((X.tr g).take x) := by
  intro hh hhh l hsp hct hl1 hl2
  obtain ⟨-, -, d, -, hc, -, -, hs⟩ := corr_arrive hpre hX ht hw hw' he
  rcases hs with ⟨a, -, hm⟩ | ⟨st', hsd, hm⟩ | ⟨st', -, hm⟩
  · simp only [Correction.ownLoc, stagedBar, Correction.sb, Loc.mk.injEq] at hm; omega
  rotate_left
  · simp only [Correction.leadLoc, stagedBar, Correction.sb, Loc.mk.injEq] at hm; omega
  simp only [Correction.ownLoc, stagedBar, Correction.sb, Loc.mk.injEq] at hm
  obtain rfl : st = st'.val := by omega
  -- the element of the byte
  have hkk : Correction.kOf L g < 4 := Nat.mod_lt _ (by decide)
  have hln : Correction.lnOf L g < 32 := Nat.mod_lt _ (by decide)
  have hrow : rowOf L g = 32 * Correction.kOf L g + Correction.lnOf L g := by
    simp only [rowOf, Correction.kOf, Correction.lnOf, Correction.tidOf]; omega
  set off := l.addr - lineBase L st'.val hh (rowOf L g) with hoff
  set c := off / 16 ^^^ Correction.lnOf L g % 8 with hcdef
  have hc8 : c < 8 := Nat.xor_lt_two_pow (n := 3) (by omega) (by omega)
  have hcx : Correction.lnOf L g % 8 ^^^ c = off / 16 := by
    rw [hcdef, Nat.xor_comm (off / 16), ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  let j : Fin 8 := ⟨4 * hh + c / 2, by omega⟩
  let h : Fin 2 := ⟨c % 2, by omega⟩
  let el : Fin 4 := ⟨off % 16 / 4, by omega⟩
  have hjc : 2 * (j.val % 4) + h.val = c := by simp only [j, h]; omega
  have hdone : Correction.wDone d st' j h el := by
    simp only [Correction.wDone, hsd]
  obtain ⟨r, hr, pcw, ac, bs, hgw, hloc, hsz, hcnt⟩ := hc.wrote st' j h el hdone
  have hlen : x < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  rw [List.length_take] at hr
  have hrx : r < x := by omega
  rw [take_get hrx] at hgw
  rw [take_take_le hrx.le] at hcnt
  refine ⟨r, ac, bs, hrx, ⟨pcw, hgw⟩, ?_, ?_⟩
  · have hxor : Correction.lnOf L g % 8 ^^^ (2 * (j.val % 4) + h.val) = off / 16 := by
      rw [hjc, hcx]
    have hA : (Correction.fstLoc L g st' j h el).addr =
        lineBase L st'.val hh (rowOf L g) + 16 * (off / 16) + 4 * (off % 16 / 4) := by
      show Correction.stage L g st'.val (2 * (j.val % 4) + h.val) + 16384 * (j.val / 4) +
        4 * el.val = _
      unfold Correction.stage
      rw [hxor]
      simp only [Correction.sb, lineBase, hrow, j, el]
      omega
    rw [Acc.Covers, hloc, hsz]
    refine ⟨hsp, hct, ?_, ?_⟩ <;> rw [hA] <;> omega
  · rw [stagedBar_own, hcnt, hc.staged st'.val st'.isLt]
    obtain ⟨site, i', t', aw, aa, o⟩ := d
    simp only at hsd ⊢
    subst hsd
    fin_cases st' <;> simp [Correction.stagedPos]

/-- **`OutputFacts.staging_access`, correction part**: an access of a staging byte by a correction
thread is a write of its row's line of a stage, after one more free poll than staged arrivals of
the stage, and every later staged arrival of the stage follows a fence after the write. -/
theorem Facts.Corr.staging_access {g i : Nat} {a : Acc} {w : Bool} {l : Loc}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (hacc : X.Access (g, i) a w)
    (hcov : a.Covers l) (hin : InStaging L l) :
    8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ w = true ∧ ∃ st < 2, CorrStage L X g i a st := by
  rcases hacc with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨_, _, pc, he⟩
  rotate_right
  · exact (TmemFacts_no_rmw hX he).elim
  · exfalso
    obtain ⟨_, _, -, -, -, -, -, hl, hs, -⟩ := corr_rd hpre hX ht hw hw' he
    obtain ⟨-, -, h1, h2⟩ := hcov
    rw [hl] at h1 h2
    rw [hs] at h2
    have hr := rowOf_lt L g
    obtain ⟨-, h3, -⟩ := hin
    simp only [statsWord] at h1 h2
    omega
  obtain ⟨d, st, j, h, el, -, hc, -, hs, hloc, hsz, -⟩ := corr_wr hpre hX ht hw hw' he
  refine ⟨hw, hw', rfl, st.val, st.isLt, ⟨j.val / 4, by omega, fst_inLine st j h el hloc hsz⟩,
    ?_, ?_⟩
  · rw [freeBar_own, stagedBar_own, hc.oFree st.val st.isLt, hc.staged st.val st.isLt]
    obtain ⟨site, i', t', aw, aa, o⟩ := d
    simp only at hs ⊢
    subst hs
    fin_cases st <;> simp [Correction.fPos, Correction.stagedPos]
  · intro e pce tx cnt rel sc hie hee
    set m := stagedBar L (ctaOf L g) st.val
    have harr : ∀ es, arrivals m es = es.countP (arrivesOn m) := fun _ => rfl
    set c0 := arrivals m ((X.tr g).take i) with hc0
    have hmono := countP_take_mono (arrivesOn m) (X.tr g) (show i ≤ e by omega)
    have hsucc := countP_take_succ (p := arrivesOn m) hee (by simp [arrivesOn, sourceArrive])
    obtain ⟨e', ev, he'e, hge', hpe', hce'⟩ :=
      exists_nthEv (X := X) (g := g) (p := arrivesOn m) (n := c0) (k := e + 1)
        (by rw [hc0, harr]; omega)
    -- the first staged arrival after the write
    have hie' : i < e' := by
      by_contra hle
      rcases Nat.lt_or_ge e' i with hlt | hge
      · have h1 := countP_take_succ (p := arrivesOn m) hge' hpe'
        have h2 := countP_take_mono (arrivesOn m) (X.tr g) (show e' + 1 ≤ i by omega)
        rw [hc0, harr] at hce'
        omega
      · obtain rfl : e' = i := by omega
        rw [he] at hge'
        injection hge' with hge'
        subst hge'
        simp [arrivesOn, sourceArrive] at hpe'
    obtain ⟨epc, ek⟩ := ev
    have hk : ∃ tx' cnt' rel' sc', ek = .arrive m tx' cnt' rel' sc' := by
      cases ek <;> simp only [arrivesOn, sourceArrive, Bool.false_eq_true,
        decide_eq_true_eq] at hpe'
      subst hpe'
      exact ⟨_, _, _, _, rfl⟩
    obtain ⟨tx', cnt', rel', sc', rfl⟩ := hk
    obtain ⟨-, -, d', -, hc', -, -, hs'⟩ := corr_arrive hpre hX ht hw hw' hge'
    rcases hs' with ⟨a0, -, hm⟩ | ⟨st'', hsd, hm⟩ | ⟨st'', -, hm⟩
    · simp only [m, Correction.ownLoc, stagedBar, Correction.sb, Loc.mk.injEq] at hm; omega
    rotate_left
    · simp only [m, Correction.leadLoc, stagedBar, Correction.sb, Loc.mk.injEq] at hm; omega
    simp only [m, Correction.ownLoc, stagedBar, Correction.sb, Loc.mk.injEq] at hm
    obtain ⟨pcf, pco, relo, sco, hf1, hf2⟩ := (hc'.fenced st'').2 hsd
    have hlen' : e' < (X.tr g).length := (List.getElem?_eq_some_iff.mp hge').1
    simp only [List.length_take, Nat.min_eq_left hlen'.le] at hf1 hf2
    have he2 : 2 ≤ e' := by
      rcases Nat.lt_or_ge e' 2 with hlt | hge
      · interval_cases e'
        · simp at hf1
        · simp only [Nat.sub_self] at hf1 hf2
          rw [hf1] at hf2
          simp at hf2
      · exact hge
    rw [take_get (by omega)] at hf1 hf2
    rw [show e' - 1 = e' - 2 + 1 by omega] at hf2
    refine ⟨e' - 2, pcf, ?_, by omega, hf1, ?_⟩
    · rcases Nat.lt_or_ge i (e' - 2) with hlt | hge
      · exact hlt
      · exfalso
        rcases (show i = e' - 2 ∨ i = e' - 2 + 1 by omega) with rfl | rfl
        · rw [he] at hf1; injection hf1 with hf1; cases hf1
        · rw [he] at hf2; injection hf2 with hf2; cases hf2
    · have h1 := countP_take_succ_false (p := arrivesOn m) hf1 (by simp [arrivesOn, sourceArrive])
      have h2 := countP_take_succ_false (p := arrivesOn m) hf2 (by
        simp only [arrivesOn, sourceArrive, m, Correction.leadLoc, stagedBar, Correction.sb,
          decide_eq_false_iff_not, Loc.mk.injEq, not_and]
        intro _; omega)
      rw [show e' - 2 + 1 + 1 = e' by omega] at h2
      rw [harr]
      omega

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
