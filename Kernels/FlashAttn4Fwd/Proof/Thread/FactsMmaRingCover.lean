-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaCoverUse
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaCoverBytes
public import Lemmas.Tcgen05.MmaObservedReads

@[expose] public section

/-! # The MMAs of a released use cover its ring region

Before the leader MMA lane's commit to a ring empty barrier, the eight steps of a block of the
released use come, with as many earlier commits to the barrier (`commit_use`); a byte of the
partner full barrier's region, in either CTA of the pair, is the operand byte of one of the steps
(`Mma.k_cover`, `Mma.q_cover`, `Mma.v_cover`); a wait observing that MMA's completion finds the
read performed (`observed_mmaRead`; `RingFacts.cover`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An MMA's operand byte at a location covers it. -/
theorem covers_of_byteLoc {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {isB : Bool} {idx : Nat} {l : Loc} (hi : X.MmaIssue i d s acc mask)
    (hl : s.byteLoc (if isB then .b else .a) idx = some l) :
    AsyncCovers X i (.mmaRead isB idx) l :=
  ⟨{ loc := l, size := 1 }, false, ⟨rfl, rfl, .inl ⟨d, s, acc, mask, hi, hl⟩⟩,
    ⟨rfl, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩⟩

/-- **The field `RingFacts.cover`.** -/
theorem RingFacts_cover (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g jc pc c : Nat} {b : FBar} {sp : TcCommit.Spec} {l : Loc}
    (_ : g < L.threads) (he : X.get (g, jc) = some ⟨pc, .tc (.commit sp)⟩) (hb : b.isFull)
    (hm : sp.mbar = b.partner.loc L (ctaOf L g)) (hr : InRegion L c b l)
    (hc : c / 2 = ctaOf L g / 2) :
    ∃ kR isB idx, kR < jc ∧ X.TcAsync (g, kR) ∧
      ((X.tr g).take kR).countP (commitsTo sp.mbar) =
        ((X.tr g).take jc).countP (commitsTo sp.mbar) ∧
      AsyncCovers X (g, kR) (.mmaRead isB idx) l ∧
      ∀ w ws, AsyncCopy.AsyncObserved X (g, kR) .mmaDone w true ws →
        X.AsyncPresent (g, kR) (.mmaRead isB idx) := by
  obtain ⟨b', isB, hA, huse⟩ := commit_use hpre hX ht he hb hm
  obtain ⟨hsp, hcta, hlo, hhi⟩ := hr
  have hal := hpre.sharedAlignment
  have hp : Mma.pairLo L g = g / L.block / 2 * 2 := rfl
  have hc' : c / 2 = g / L.block / 2 := hc
  have hr2 : c - Mma.pairLo L g < 2 := by rw [hp]; omega
  have hcr : c = if c - Mma.pairLo L g = 0 then Mma.pairLo L g else Mma.pairLo L g + 1 := by
    rw [hp]
    split_ifs <;> omega
  have hl : l = ⟨.shared, c, L.sharedBase + b.regionOff +
      (l.addr - (L.sharedBase + b.regionOff))⟩ := by
    obtain ⟨sp', c', a'⟩ := l
    simp only at hsp hcta hlo hhi ⊢
    subst hsp hcta
    simp only [Loc.mk.injEq, true_and]
    omega
  have ha : l.addr - (L.sharedBase + b.regionOff) < b.regionSize := by omega
  generalize l.addr - (L.sharedBase + b.regionOff) = a at hl ha
  subst hl
  cases b <;> simp [FBar.isFull] at hb
  · -- a Q stage: the A operand of a QK block
    rename_i st
    cases isB
    · have hpv := hA rfl
      obtain ⟨j, idx, hcov⟩ := Mma.q_cover hal st (a := a) (r := c - Mma.pairLo L g) ha hr2
      obtain ⟨kR, hk, d', h, hrb, hcnt⟩ := huse j
      simp only [Mma.readBar, Bool.false_eq_true, ↓reduceIte, FBar.qFull.injEq] at hrb
      have hbl := hcov (Mma.mmaSpec L g d' b' j) (mmaSpec_qkDesc hpv)
        (by simp [Mma.mmaSpec, hpv]) (by simp [Mma.mmaSpec, hpv, hrb])
      simp only [Mma.mmaSpec, hpv, Bool.false_eq_true, ↓reduceIte, ← hcr] at hbl
      exact ⟨kR, false, idx, hk, .inl ⟨_, _, _, _, h.issue⟩, hcnt,
        covers_of_byteLoc h.issue (by simpa [Mma.mmaSpec, hpv] using hbl),
        fun w ws hobs => observed_mmaRead hX h.issue (by simpa [Mma.mmaSpec, hpv] using hbl) hobs⟩
    · obtain ⟨kR, -, d', -, hrb, -⟩ := huse 0
      simp only [Mma.readBar, ↓reduceIte] at hrb
      split_ifs at hrb
  · -- a KV slot: the B operand of a QK or a PV block
    rename_i sl
    cases isB
    · obtain ⟨kR, -, d', -, hrb, -⟩ := huse 0
      simp [Mma.readBar] at hrb
    cases hpv : Mma.isPv b'
    · obtain ⟨j, idx, hcov⟩ := Mma.k_cover hal sl (a := a) (r := c - Mma.pairLo L g) ha hr2
      obtain ⟨kR, hk, d', h, hrb, hcnt⟩ := huse j
      simp only [Mma.readBar, hpv, Bool.false_eq_true, ↓reduceIte, FBar.kvFull.injEq] at hrb
      have hbl := hcov (Mma.mmaSpec L g d' b' j) (mmaSpec_qkDesc hpv)
        (by simp [Mma.mmaSpec, hpv, hrb])
      simp only [Mma.mmaSpec, hpv, Bool.false_eq_true, ↓reduceIte, ← hcr] at hbl
      exact ⟨kR, true, idx, hk, .inl ⟨_, _, _, _, h.issue⟩, hcnt,
        covers_of_byteLoc h.issue (by simpa [Mma.mmaSpec, hpv] using hbl),
        fun w ws hobs => observed_mmaRead hX h.issue (by simpa [Mma.mmaSpec, hpv] using hbl) hobs⟩
    · obtain ⟨j, idx, hcov⟩ := Mma.v_cover hal sl (a := a) (r := c - Mma.pairLo L g) ha hr2
      obtain ⟨kR, hk, d', h, hrb, hcnt⟩ := huse j
      simp only [Mma.readBar, hpv, ↓reduceIte, FBar.kvFull.injEq] at hrb
      have hbl := hcov (Mma.mmaSpec L g d' b' j) (mmaSpec_pvDesc hpv)
        (by simp [Mma.mmaSpec, hpv, hrb])
      simp only [Mma.mmaSpec, hpv, ↓reduceIte, ← hcr] at hbl
      exact ⟨kR, true, idx, hk, .inl ⟨_, _, _, _, h.issue⟩, hcnt,
        covers_of_byteLoc h.issue (by simpa [Mma.mmaSpec, hpv] using hbl),
        fun w ws hobs => observed_mmaRead hX h.issue (by simpa [Mma.mmaSpec, hpv] using hbl) hobs⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
