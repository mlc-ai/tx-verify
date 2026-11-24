-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.ElectTot
public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.SuPick
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's elections, by the site and the packets

`ld_els`: at a state of a block, the elections of warp 14 are the block's (12 in the first block,
6 per warm round before, group 6 when it is taken) and the ones in the block before the
site (`blkEl`); at the second pass and the drain they are the tile's. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Arith32

noncomputable section
set_option maxRecDepth 100000

/-- The elections of a group before a site of it. -/
def grpEl : Site → Nat
  | .te _ e => e.val
  | .ta _ => 1
  | .tc _ c => 2 + c.val
  | _ => 0

/-- The elections of a block before a site of it. -/
def blkEl : Site → Nat
  | .tw t => if t.val < 4 then 3 * t.val else if t.val < 6 then 3 * (t.val - 4) else 0
  | .te t e => (if t.val < 4 then 3 * t.val else if t.val < 6 then 3 * (t.val - 4) else 0) + e.val
  | .ta t => (if t.val < 4 then 3 * t.val else if t.val < 6 then 3 * (t.val - 4) else 0) + 1
  | .tc t c =>
    (if t.val < 4 then 3 * t.val else if t.val < 6 then 3 * (t.val - 4) else 0) + 2 + c.val
  | .slot per v | .ptP per v _ | .ptR per v _ | .ptS per v _ | .lw per v _ | .xl per v _
  | .xh per v _ | .cp per v _ _ | .commit per v | .arrive per v =>
    if v then (match per with | .prime => 12 | .warm => 6 | .steady => 0) else 0
  | _ => 0

/-- The forms' value at a site of a warm block or the last Bias group. -/
def warmChk (s : Site) : Bool :=
  match biasForm false s, biasForm true s with
  | some (true, a), some (true, b) =>
    3 * (2 * inBlk s + a + b) == 2 * (blkEl s + elRem s : Nat) &&
      qAcq 14 s 1 16 == 1 && qAcq 14 s 1 24 == 1
  | _, _ => false

/-- The forms' value at a site of the first block, of a warm block or the last Bias group, and the
Q polls after the first block. -/
def elChk' (s : Site) : Bool :=
  match bc s with
  | some .prime => match biasForm false s, biasForm true s with
    | some (false, a), some (false, b) =>
      3 * ((qAcq 14 s 1 16 + qAcq 14 s 1 24 : Nat) + a + b) == (blkEl s + elRem s : Nat) &&
        qAcq 14 s 0 16 == qAcq 14 s 1 16 && qAcq 14 s 0 24 == qAcq 14 s 1 24
    | _, _ => false
  | some .warm | some .tma6 => warmChk s
  | some .steady => s.aft && qAcq 14 s 1 16 == 1 && qAcq 14 s 1 24 == 1 && elRem s == 0
  | none => true

theorem elChk_ok : AllSites fun s => elChk' s = true := by unfold AllSites; decide +kernel

/-- The elections of the drain before a site of it. -/
def drainEl : Site → Nat
  | .da | .exit => 1
  | _ => 0

/-- The elections of a tile, on warp 14. -/
def totEl (v : V) : Nat := 12 + 6 * w0 v.su.r28 + 3 * (if Last v then 1 else 0)

theorem biasTot_sum (v : V) : 3 * (biasTot v false + biasTot v true) = 6 + 6 * w0 v.su.r28 +
    3 * (if Last v then 1 else 0) := by
  unfold biasTot
  by_cases h : Last v <;> simp [h] <;> omega

/-- The elections of the drain, and none to come at the second pass. -/
def lateChk (s : Site) : Bool :=
  match lc s with
  | .drain => 3 * (qAcq 14 s 1 16 + qAcq 14 s 1 24) == 6 + drainEl s + elRem s &&
      3 * (qAcq 14 s 0 16 + qAcq 14 s 0 24) == drainEl s + elRem s && s.aft
  | .p2 => qAcq 14 s 1 16 + qAcq 14 s 1 24 == 2 && elRem s == 0 && s.aft
  | .early | .p1 | .req => qAcq 14 s 0 16 + qAcq 14 s 0 24 == 0 && elRem s == 0 &&
      biasForm false s == some (false, 0) && biasForm true s == some (false, 0)
  | .blk => true

theorem late_ok : AllSites fun s => lateChk s = true := by unfold AllSites; decide +kernel

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

theorem pkts_ge (b : BitVec 64) : 2 ≤ pkts b := by
  unfold pkts
  rw [Nat.add_assoc]
  exact Nat.le_add_right _ _

/-- The fact after the warm rounds. -/
private theorem BiasNum.late {dn : D × (Cnt → Nat)} (h : BiasNum L g dn) (st : Bool)
    (ha : dn.1.site.aft = true) : lc dn.1.site = .drain ∧ dn.2 .commit = 0 ∧
      dn.2 (nE L g st) = 0 ∨ dn.2 (nE L g st) = biasTot dn.1.v st := by
  obtain ⟨-, -, -, h4⟩ := h st
  exact h4 ha

/-- The steps to the drain. -/
def drChk (_ : Bool) (s s' : Site) : Bool :=
  lc s' != .drain || (lc s == .drain || lc s == .p1 || lc s == .p2) &&
    tag s s' != .acq 336 && tag s s' != .acq 344

theorem dr_edges : Edges drChk := by unfold Edges AllSites; decide +kernel

private theorem nE_bump {w : Nat} {d d' : D} {n : Cnt → Nat} {e : Event} {st : Bool}
    (hm : Move L g w (d, n) e d') (h : tag d.site d'.site ≠ .acq (if st then 344 else 336)) :
    Code.bump (cls L g) n e (nE L g st) = n (nE L g st) := by
  rw [bump_tag hm]
  cases hT : tag d.site d'.site <;>
    simp only [Tag.cnt, reduceCtorEq, Option.some.injEq, Cnt.acquire.injEq, ↓reduceIte,
      bl, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff, Nat.add_zero]
  case acq o =>
    rw [hT] at h
    have : ¬ o = if st then 344 else 336 := fun hc => h (by rw [hc])
    simp [this]
  case acqRing δ =>
    have := Nat.mod_lt (n .commit + δ) (show 0 < 3 by decide)
    have hne : ¬ 56 + 8 * ((n .commit + δ) % 3) = if st then 344 else 336 := by
      cases st <;> simp <;> omega
    simp [hne]

/-- **A drain with no packets had no Bias polls.** -/
private theorem drain_zero (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 14) {b : Bool} {d : D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) : lc d.site = .drain → LdWarp.lcn n .commit = 0 →
      ∀ st, LdWarp.lcn n (nE L g st) = 0 := by
  refine LdWarp.step_at (w := 14) (I := fun _ dn => lc dn.1.site = .drain → dn.2 .commit = 0 →
    ∀ st, dn.2 (nE L g st) = 0) ?_ ?_ ?_ hp hX hg (.inl rfl) hw k b d n hσ hub
  · intro b k n _ _ _ _ _ _; rfl
  · intro k b n d e d' _ hσ hub _ hF _ _ _ _ hm h hl hz st
    simp only at h hl hz ⊢
    have hz0 : LdWarp.lcn n .commit = 0 := by
      rw [bump_tag hm] at hz; exact (Nat.add_eq_zero_iff.mp hz).1
    rcases hm.edge with hs | hs
    · simp only at hs
      have h1 := h (by rw [← hs]; exact hl) hz0 st
      rwa [nE_bump hm (by rw [hs, tag_self]; simp)]
    · have hc := dr_edges.ok hs
      simp only [drChk, hl, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
        beq_iff_eq, bne_iff_ne] at hc
      rw [nE_bump hm (by cases st <;> simp [hc.1.2, hc.2])]
      rcases hc.1.1 with (h0 | h0) | h0
      · exact h h0 hz0 st
      · have hb := (bias_num hp hX hg hw hσ hub st).1 0 (by
          have := late_ok.ok d.site
          simp only [lateChk, h0, Bool.and_eq_true, beq_iff_eq] at this
          cases st
          · exact this.1.2
          · exact this.2)
        simpa using hb
      · exfalso
        simp only [LFits, h0] at hF
        obtain ⟨-, -, -, h1⟩ := hF
        change n (.load .commit) = 0 at hz0
        rw [hz0] at h1
        exact absurd (pkts_ge d.v.su.r28) (by rw [← h1]; decide)
  · intro _ _ _ h; exact h

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
  (hw : Prologue.warpIndex L g = 14) {b : Bool} {d : D} {n : Cls → Nat}
  (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
  (hub : n .ub = 0)
include hp hX hg hw hσ hub

/-- The polls behind the elections. -/
private theorem els_polls : ∃ q0 q1 b0 b1, els X g k + elRem d.site = 3 * (q0 + q1 + b0 + b1) ∧
    q0 = qAcq 14 d.site (n (.load .commit)) 16 ∧ q1 = qAcq 14 d.site (n (.load .commit)) 24 ∧
    b0 = LdWarp.lcn n (nE L g false) ∧ b1 = LdWarp.lcn n (nE L g true) := by
  have h1 := (elect_tot hp hX hg (.inl hw) hσ hub).1 hw
  have hb : wOf b = 14 := by
    have := (LdWarp.good hp hX (.inl rfl) hg hw k).2 _ hσ
    exact this.1
  have h2 := q_acq hp hX hg (.inl hw) hσ hub
  rw [hb] at h2
  refine ⟨_, _, _, _, h1, h2 16 (by simp), h2 24 (by simp), rfl, rfl⟩

/-- **The elections of a block's state.** -/
theorem ld_els_blk {nc : Nat} (hnc : n (.load .commit) = nc) :
    (bc d.site = some .prime → els X g k = blkEl d.site) ∧
    (bc d.site = some .warm ∨ bc d.site = some .tma6 → ∀ u, nc = 2 + 2 * u + inBlk d.site →
      els X g k = 12 + 6 * u + blkEl d.site) ∧
    (bc d.site = some .steady → nc ≠ 0 → els X g k = totEl d.v) := by
  obtain ⟨q0, q1, b0, b1, h, e1, e2, e3, e4⟩ := els_polls hp hX hg hw hσ hub
  have hc := elChk_ok.ok d.site
  have hN := bias_num hp hX hg hw hσ hub
  have hn0 := hN false
  have hn1 := hN true
  have hcm : LdWarp.lcn n .commit = nc := hnc
  rw [hnc] at e1 e2
  refine ⟨fun hbc => ?_, fun hbc u hu => ?_, fun hbc hz => ?_⟩
  · simp only [elChk', hbc] at hc
    split at hc
    · rename_i a b' ha hb'
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨c1, c2⟩, c3⟩ := hc
      have f0 := hn0.1 a ha
      have f1 := hn1.1 b' hb'
      simp only at f0 f1
      rw [qAcq_one] at e1 e2
      have q01 : q0 = qAcq 14 d.site 1 16 := by rw [e1]; split <;> simp [c2]
      have q11 : q1 = qAcq 14 d.site 1 24 := by rw [e2]; split <;> simp [c3]
      rw [← q01, ← q11] at c1
      rw [← e3] at f0
      rw [← e4] at f1
      omega
    · cases hc
  · have hc' : warmChk d.site = true := by
      rcases hbc with hbc | hbc <;> simpa only [elChk', hbc] using hc
    unfold warmChk at hc'
    split at hc'
    · rename_i a b' ha hb'
      simp only [Bool.and_eq_true, beq_iff_eq] at hc'
      obtain ⟨⟨c1, c2⟩, c3⟩ := hc'
      have f0 := hn0.2.1 a ha
      have f1 := hn1.2.1 b' hb'
      simp only [hcm] at f0 f1
      rw [qAcq_one, ite_eq_right (by omega : ¬ nc = 0)] at e1 e2
      rw [c2] at e1
      rw [c3] at e2
      rw [← e3] at f0
      rw [← e4] at f1
      omega
    · cases hc'
  · simp only [elChk', hbc, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨c0, c2⟩, c3⟩, c4⟩ := hc
    have hlc : lc d.site = .blk := lc_blk.mpr (by simp [Site.blk, hbc])
    have f0 := (hN.late false c0).resolve_left (by simp [hlc])
    have f1 := (hN.late true c0).resolve_left (by simp [hlc])
    simp only at f0 f1
    rw [qAcq_one, ite_eq_right hz] at e1 e2
    have := biasTot_sum d.v
    unfold totEl
    rw [← e3] at f0
    rw [← e4] at f1
    omega

/-- **The elections outside the blocks.** -/
theorem ld_els_out {nc : Nat} (hnc : n (.load .commit) = nc) :
    (lc d.site = .early ∨ lc d.site = .p1 ∨ lc d.site = .req → nc = 0 → els X g k = 0) ∧
    (lc d.site = .p2 → nc ≠ 0 → els X g k = totEl d.v) ∧
    (lc d.site = .drain → (nc = 0 → els X g k = drainEl d.site) ∧
      (nc ≠ 0 → els X g k = totEl d.v + drainEl d.site)) := by
  obtain ⟨q0, q1, b0, b1, h, e1, e2, e3, e4⟩ := els_polls hp hX hg hw hσ hub
  have hc := late_ok.ok d.site
  have hN := bias_num hp hX hg hw hσ hub
  have hn0 := hN false
  have hn1 := hN true
  have hcm : LdWarp.lcn n .commit = nc := hnc
  rw [hnc] at e1 e2
  have hsum := biasTot_sum d.v
  refine ⟨fun hl hz => ?_, fun hl hz => ?_, fun hl => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · have hc' : (qAcq 14 d.site 0 16 + qAcq 14 d.site 0 24 == 0 && elRem d.site == 0 &&
        biasForm false d.site == some (false, 0) && biasForm true d.site == some (false, 0)) =
        true := by
      rcases hl with hl | hl | hl <;> simpa only [lateChk, hl] using hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hc'
    have f0 := hn0.1 0 c3
    have f1 := hn1.1 0 c4
    simp only at f0 f1
    rw [hz] at e1 e2
    rw [← e3] at f0
    rw [← e4] at f1
    omega
  · simp only [lateChk, hl, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨c1, c2⟩, c3⟩ := hc
    have f0 := (hN.late false c3).resolve_left (by simp [hl])
    have f1 := (hN.late true c3).resolve_left (by simp [hl])
    simp only at f0 f1
    rw [qAcq_one, ite_eq_right hz] at e1 e2
    rw [← e3] at f0
    rw [← e4] at f1
    unfold totEl
    omega
  · simp only [lateChk, hl, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨c1, c2⟩, c3⟩ := hc
    have hz2 := drain_zero hp hX hg hw hσ hub hl (hcm.trans hz)
    have z0 := hz2 false
    have z1 := hz2 true
    rw [hz] at e1 e2
    omega
  · simp only [lateChk, hl, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨c1, c2⟩, c3⟩ := hc
    have f0 := (hN.late false c3).resolve_left (fun h => hz (hcm.symm.trans h.2.1))
    have f1 := (hN.late true c3).resolve_left (fun h => hz (hcm.symm.trans h.2.1))
    simp only at f0 f1
    rw [qAcq_one, ite_eq_right hz] at e1 e2
    rw [← e3] at f0
    rw [← e4] at f1
    unfold totEl
    omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
