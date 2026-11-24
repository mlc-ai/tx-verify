-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.BiasAcq
public import Kernels.TmlFa4Fwd.Proof.LdWarp.StepAt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's Bias groups, counted

Standalone fact. On warp 14 the successful polls of a Bias empty barrier (`336` for stage 0, `344`
for stage 1) are one in the first block and one per warm round, and for stage 0 one more in the last
Bias group (`BiasNum`): in a warm round a function of the commits and the site, after the warm
rounds the tile's number (`biasTot`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Arith32

noncomputable section
set_option maxRecDepth 100000

/-- The last Bias group is taken. -/
def Last (v : V) : Prop := 10 < sv v.su.r28 ∧ sv v.su.r29 < 0

instance (v : V) : Decidable (Last v) := by unfold Last; infer_instance

/-- **The Bias groups of stage `st`** of a tile with setup words `v`. -/
def biasTot (v : V) (st : Bool) : Nat :=
  1 + w0 v.su.r28 + if st = false ∧ Last v then 1 else 0

/-- The sites after the warm rounds and the last Bias group. -/
def Site.aft : Site → Bool
  | .pgLd per _ | .pgSt per _ | .rwSt per _ | .slot per _ | .ptP per _ _ | .ptR per _ _
  | .ptS per _ _ | .lw per _ _ | .xl per _ _ | .xh per _ _ | .cp per _ _ _ | .commit per _
  | .arrive per _ => per == .steady
  | .word k | .down k | .up k _ | .total k => k.late
  | .vote l | .pre l | .tiles l => l
  | .dw _ | .dq | .de | .da | .exit => true
  | _ => false

/-- The sites of the last Bias group. -/
def Site.lastGrp : Site → Bool
  | .tw t | .te t _ | .ta t | .tc t _ => t.val == 6
  | _ => false

/-- The sites whose successor is chosen by the round's end. -/
def Site.ends : Site → Bool
  | .arrive per v => per != .steady && v
  | _ => false

/-- The polls of stage `st` before a site not after the warm rounds: `(false, c)` if they are `c`,
`(true, e)` if twice them are the commits plus `e`. -/
def biasForm (st : Bool) : Site → Option (Bool × Int)
  | .pgLd per _ | .pgSt per _ | .rwSt per _ =>
    match per with | .prime => some (false, 0) | .warm => some (true, 0) | .steady => none
  | .slot per v | .ptP per v _ | .ptR per v _ | .ptS per v _ | .lw per v _ | .xl per v _
  | .xh per v _ | .cp per v _ _ | .commit per v =>
    match per with
    | .prime => some (false, if v then 1 else 0)
    | .warm => some (true, if v then 1 else 0)
    | .steady => none
  | .arrive per v =>
    match per with
    | .prime => some (false, if v then 1 else 0)
    | .warm => some (true, if v then 0 else -1)
    | .steady => none
  | .tw t =>
    if t.val < 4 then some (false, if (if st then 3 else 1) < t.val then 1 else 0)
    else if t.val = 4 then some (true, -1)
    else if t.val = 5 then some (true, if st then -1 else 1) else some (true, 0)
  | .te t _ | .ta t | .tc t _ =>
    if t.val < 4 then some (false, if (if st then 3 else 1) ≤ t.val then 1 else 0)
    else if t.val = 4 then some (true, if st then -1 else 1)
    else if t.val = 5 then some (true, 1) else some (true, if st then 0 else 2)
  | .word k | .down k | .up k _ | .total k => if k.late then none else some (false, 0)
  | .vote l | .pre l | .tiles l => if l then none else some (false, 0)
  | .setmax | .q0 | .q1 | .uk => some (false, 0)
  | _ => none

/-- The edge check (warp 14). -/
def numChk (b : Bool) (s s' : Site) : Bool :=
  b || [false, true].all fun st =>
    let t : Int := if tag s s' = .acq (if st then 344 else 336) then 1 else 0
    let m : Int := if tag s s' = .commit then 1 else 0
    (!s.lastGrp || s'.lastGrp || s'.aft) && (s.lastGrp || s.ends || !s'.lastGrp) &&
    if s'.aft then
      t == 0 && (!(s.aft && lc s == .drain) || (lc s' == .drain && m == 0)) &&
        (s.aft || s.lastGrp && biasForm st s == some (true, if st then 0 else 2) ||
        s.ends || (lc s == .p1 && lc s' == .drain && m == 0 && biasForm st s == some (false, 0)))
    else match biasForm st s', biasForm st s with
      | some (true, e'), some (true, e) => e + 2 * t == m + e' && !(s.ends && (e != 0 || m != 0))
      | some (false, c'), some (false, c) => c' == c + t
      | some (true, e'), some (false, c) => e' == 0 && c == 1 && t == 0 && m == 0 &&
          s == .arrive .prime true
      | _, _ => false

/-- The sites whose step keeps the setup words. -/
def Site.blkS : Site → Bool
  | .uk => false
  | _ => true

/-- A site after the warm rounds is of a steady block, the second pass or the drain. -/
def aftChk (s : Site) : Bool :=
  (s.aft == (biasForm false s).isNone) && (s.aft == (biasForm true s).isNone) &&
    (!s.lastGrp || bc s == some .tma6 && inBlk s == 0) && !(s.aft && s.lastGrp) &&
    (!s.ends || s == .arrive .prime true ||
      s == .arrive .warm true)

theorem num_self : AllSites fun s => aftChk s = true := by
  unfold AllSites; decide +kernel

theorem num_edges : Edges numChk := by unfold Edges AllSites; decide +kernel

/-- The count of stage `st` in a ledger. -/
abbrev nE (L : Launch) (g : Nat) (st : Bool) : Cnt := .acquire (bl L g (if st then 344 else 336))

/-- The fact at a state with counts. -/
def BiasNum (L : Launch) (g : Nat) (dn : D × (Cnt → Nat)) : Prop :=
  ∀ st : Bool,
    (∀ c, biasForm st dn.1.site = some (false, c) → (dn.2 (nE L g st) : Int) = c) ∧
    (∀ e, biasForm st dn.1.site = some (true, e) →
      2 * (dn.2 (nE L g st) : Int) = dn.2 .commit + e) ∧
    (dn.1.site.lastGrp = true → Last dn.1.v) ∧
    (dn.1.site.aft = true → lc dn.1.site = .drain ∧ dn.2 .commit = 0 ∧ dn.2 (nE L g st) = 0 ∨
      dn.2 (nE L g st) = biasTot dn.1.v st)

variable {p : Params} {L : Launch} {g w : Nat}

theorem biasTot_su {v v' : V} (h : v'.su = v.su) (st : Bool) : biasTot v' st = biasTot v st := by
  simp only [biasTot, Last, h]; congr

theorem passStart_aft (d : D) : (passStart p L g true d).site.aft = true ∧
    (passStart p L g true d).site.lastGrp = false := by
  refine ite_ind (P := fun s _ => s.aft = true ∧ s.lastGrp = false) ?_ ?_ <;> exact ⟨rfl, rfl⟩

theorem afterTail_aft (d : D) : (afterTail p L g d).site.aft = true ∧
    (afterTail p L g d).site.lastGrp = false := by
  refine iteS_ind (P := fun s _ => s.aft = true ∧ s.lastGrp = false) (passStart_aft _)
    (pgEnter_ind (P := fun s _ => s.aft = true ∧ s.lastGrp = false) ?_ ?_) <;> exact ⟨rfl, rfl⟩

/-- After the warm rounds: the last Bias group when it is taken. -/
theorem afterWarm_cases (d : D) :
    ((afterWarm p L g 14 d).site.lastGrp = true ∧ (afterWarm p L g 14 d).site.aft = false ∧
      Last d.v) ∨
    ((afterWarm p L g 14 d).site.lastGrp = false ∧ (afterWarm p L g 14 d).site.aft = true ∧
      ¬ Last d.v) := by
  rw [afterWarm_eq]
  have hl : (not14 14 || !(scmpi .gt .s d.v.su.r28 10 && scmpi .lt .s d.v.su.r29 0)) =
      !decide (Last d.v) := by
    rw [scmpi_gt_s _ (by decide) (by decide), scmpi_lt_s _ (by decide) (by decide)]
    simp only [Last, show not14 14 = false from rfl, Bool.false_or, Bool.decide_and]
  rw [hl]
  by_cases h : Last d.v
  · rw [iteS_neg (by simp [h]) rfl]
    exact .inl ⟨rfl, rfl, h⟩
  · rw [iteS_pos (by simp [h]) (afterTail_k _)]
    exact .inr ⟨(afterTail_aft d).2, (afterTail_aft d).1, h⟩

/-- The end of a warm round. -/
theorem warmEnd_cases {d : D} {nc r : Nat} (h31 : d.v.su.r31 = addi d.v.su.r28 (-1))
    (hr : d.v.rnd = W r) (h2 : 2 ≤ sv d.v.su.r28) (hlt : r < wRn d.v.su.r28)
    (hnc : nc = 2 + 2 * r + 2) :
    ((warmEnd p L g 14 d).site.lastGrp = false ∧ (warmEnd p L g 14 d).site.aft = false) ∨
    (nc = 2 + 2 * w0 d.v.su.r28 ∧
      (((warmEnd p L g 14 d).site.lastGrp = true ∧ (warmEnd p L g 14 d).site.aft = false ∧
        Last d.v) ∨ ((warmEnd p L g 14 d).site.lastGrp = false ∧
        (warmEnd p L g 14 d).site.aft = true ∧ ¬ Last d.v))) := by
  have h9 := wRn_le d.v.su.r28
  have ha : addi d.v.rnd 1 = W (r + 1) := by rw [hr]; exact addi1_W (by omega)
  rw [warmEnd_eq, ha, warmRounds_eq h31, scmp_ne_b_W (by omega) (by omega)]
  by_cases hc : r + 1 = wRn d.v.su.r28
  · rw [iteS_neg (decide_eq_false (not_not.mpr hc)) (afterWarm_k _)]
    refine .inr ⟨by rw [w0_of h2, hnc]; omega, ?_⟩
    exact afterWarm_cases _
  · rw [iteS_pos (decide_eq_true hc) (pgEnter_k _ _ _)]
    left
    refine pgEnter_ind (P := fun s _ => s.lastGrp = false ∧ s.aft = false) ?_ ?_ <;>
      exact ⟨rfl, rfl⟩

/-- **The end of a block of the first block or a warm round**: not past the rounds; the last group
when it is taken; or past the rounds without it, when the block was the last. -/
theorem ends_cases {d d' : D} {e : Event} {nc : Nat}
    (hs : d.site.ends = true) (hR : Rounds d.site d.v nc)
    (hn : succ p L g 14 d e = some (some d')) :
    (d'.site.lastGrp = false ∧ d'.site.aft = false) ∨
    (nc = 2 + 2 * w0 d.v.su.r28 ∧
      ((d'.site.lastGrp = true ∧ d'.site.aft = false ∧ Last d.v) ∨
        (d'.site.lastGrp = false ∧ d'.site.aft = true ∧ ¬ Last d.v))) := by
  obtain ⟨h31, hB⟩ := hR
  obtain ⟨site, v, kk⟩ := d
  cases site <;> simp only [Site.ends, Bool.false_eq_true] at hs
  rename_i per vv
  obtain ⟨rfl, hper⟩ : vv = true ∧ per ≠ .steady := by
    cases per <;> cases vv <;> simp at hs ⊢
  simp only [succ, Option.some.injEq] at hn
  subst hn
  cases per
  · simp only [afterArrive]
    simp only [RoundsB, bc, inBlk, ↓reduceIte] at hB
    rw [afterPrime_eq]
    by_cases hc : sv v.su.r28 < 2
    · rw [iteS_pos (by rw [scmpi_lt_s _ (by decide) (by decide)]; exact decide_eq_true hc)
        (afterWarm_k _)]
      refine .inr ⟨by simp [w0, hc, hB], ?_⟩
      exact afterWarm_cases _
    · rw [iteS_neg (by rw [scmpi_lt_s _ (by decide) (by decide)]; exact decide_eq_false hc)
        (pgEnter_k _ _ _)]
      left
      refine pgEnter_ind (P := fun s _ => s.lastGrp = false ∧ s.aft = false) ?_ ?_ <;>
        exact ⟨rfl, rfl⟩
  · simp only [afterArrive]
    simp only [RoundsB, bc, inBlk, ↓reduceIte] at hB
    obtain ⟨r, hr, h2, hlt, hnc⟩ := hB
    exact warmEnd_cases (d := ⟨.arrive .warm true, v, kk⟩) h31 hr h2 hlt (by omega)
  · exact absurd rfl hper

theorem num_step {d d' : D} {n : Cnt → Nat} {e : Event} {ns nv : Nat}
    (hF : LFits p L g d ns nv (n .commit))
    (hn : succ p L g 14 d e = some (some d')) (hm : Move L g 14 (d, n) e d')
    (h : BiasNum L g (d, n)) : BiasNum L g (d', Code.bump (cls L g) n e) := by
  intro st
  obtain ⟨h1, h2, h3, h4⟩ := h st
  simp only at h1 h2 h3 h4
  have hb : Code.bump (cls L g) n e (nE L g st) = n (nE L g st) +
      if tag d.site d'.site = .acq (if st then 344 else 336) then 1 else 0 := by
    rw [bump_tag hm]
    cases tag d.site d'.site <;>
      simp only [Tag.cnt, reduceCtorEq, Option.some.injEq, Cnt.acquire.injEq, ↓reduceIte,
        Tag.acq.injEq, bl, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff]
    case acqRing δ =>
      have := Nat.mod_lt (n .commit + δ) (show 0 < 3 by decide)
      have hne : ¬ L.sharedBase + (56 + 8 * ((n .commit + δ) % 3)) =
          L.sharedBase + if st then 344 else 336 := by
        cases st <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      have hne' : ¬ 56 + 8 * ((n .commit + δ) % 3) = if st then 344 else 336 := fun h =>
        hne (by omega)
      simp [hne']
  have hcm : Code.bump (cls L g) n e .commit = n .commit +
      if tag d.site d'.site = .commit then 1 else 0 := by
    rw [bump_tag hm]
    cases tag d.site d'.site <;> simp [Tag.cnt]
  -- a step keeps the setup words, but at the used-K read
  have hsu : d.site ≠ .uk → d'.v.su = d.v.su := fun hs => hm.keep .su (by
    revert hs; cases d.site <;> simp [wr])
  have hself := AllSites.ok num_self d.site
  have hself' := AllSites.ok num_self d'.site
  simp only [aftChk, Bool.and_eq_true, beq_iff_eq] at hself hself'
  obtain ⟨⟨⟨⟨s1, s2⟩, s3⟩, s4⟩, s5⟩ := hself
  obtain ⟨⟨⟨⟨s1', s2'⟩, s3'⟩, s4'⟩, s5'⟩ := hself'
  have hnone : d'.site.aft = (biasForm st d'.site).isNone := by cases st <;> assumption
  have haft : d.site.aft = true → d'.v.su = d.v.su := fun h' => hsu (by
    rintro h''; rw [h''] at h'; cases h')
  have hlast : d.site.lastGrp = true → d'.v.su = d.v.su := fun h' => hsu (by
    rintro h''; rw [h''] at h'; cases h')
  have hends : d.site.ends = true → d'.v.su = d.v.su := fun h' => hsu (by
    rintro h''; rw [h''] at h'; cases h')
  have hLast : ∀ {v v' : V}, v'.su = v.su → Last v → Last v' := by
    intro v v' h' hl; unfold Last at hl ⊢; rw [h']; exact hl
  have hsite : d.site.ends = true → d.site = .arrive .prime true ∨ d.site = .arrive .warm true := by
    intro h'
    simp only [h', Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at s5
    exact s5
  -- the counts at the end of a block
  have hendR : d.site.ends = true → Rounds d.site d.v (n .commit) := fun h' =>
    (lfits_blk_of (by rcases hsite h' with h'' | h'' <;> rw [h''] <;> rfl) hF).2.2.2.1
  have hprime : d.site = .arrive .prime true → n .commit = 2 := fun h' => by
    have := (hendR (by rw [h']; rfl)).2
    rw [h'] at this
    simpa [RoundsB, bc, inBlk] using this
  simp only
  rw [hb, hcm]
  rcases hm.edge with hs | hs
  · rw [hs, tag_self]
    simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero]
    refine ⟨h1, h2, fun h' => hLast (hlast h') (h3 h'), fun h' => ?_⟩
    rw [biasTot_su (haft h')]
    exact h4 h'
  have hc := num_edges.ok hs
  simp only [numChk, show not14 14 = false from rfl, Bool.false_or] at hc
  have hc := List.all_eq_true.mp hc st (by cases st <;> simp)
  generalize ht : (if tag d.site d'.site = Tag.acq (if st then 344 else 336) then 1 else 0 : Nat)
    = t
  generalize hmm : (if tag d.site d'.site = Tag.commit then 1 else 0 : Nat) = m
  have ht' : (if tag d.site d'.site = Tag.acq (if st then 344 else 336) then 1 else 0 : Int) = t :=
    by rw [← ht]; simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hm' : (if tag d.site d'.site = Tag.commit then 1 else 0 : Int) = m := by
    rw [← hmm]; simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [ht', hm'] at hc
  clear ht ht' hmm hm' hb hcm
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨hc0, hc1⟩, hc2⟩ := hc
  by_cases ha : d'.site.aft = true
  · -- past the warm rounds
    rw [ite_eq_left ha] at hc2
    have hnf : biasForm st d'.site = none := by
      rw [ha] at hnone; exact Option.isNone_iff_eq_none.mp hnone.symm
    have hnl : d'.site.lastGrp = false := by
      rw [ha] at s4'; simpa using s4'
    refine ⟨fun c h' => (by rw [hnf] at h'; cases h'), fun c h' => (by rw [hnf] at h'; cases h'),
      fun h' => (by rw [hnl] at h'; cases h'), fun _ => ?_⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hc2
    obtain ⟨⟨ht0, hdr⟩, hcase⟩ := hc2
    obtain rfl : t = 0 := by omega
    rcases hcase with ((hcase | hcase) | hcase) | hcase
    · rw [biasTot_su (haft hcase)]
      rcases h4 hcase with ⟨q1, q2, q3⟩ | q
      · left
        rcases hdr with hdr | ⟨hdr, hm0⟩
        · rw [hcase, q1] at hdr; simp at hdr
        · exact ⟨hdr, by omega, (by omega)⟩
      · exact .inr (by omega)
    · obtain ⟨hl, hf⟩ := hcase
      have hbk := s3
      simp only [hl, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hbk
      obtain ⟨-, -, -, ⟨-, hR⟩, -⟩ := lfits_blk_of (by rw [Site.blk, hbk.1]; rfl) hF
      rw [hbk.1, hbk.2] at hR
      obtain ⟨-, hR2, hR3⟩ := hR
      have hk := h2 _ hf
      right
      rw [biasTot_su (hlast hl), biasTot, w0_of hR2]
      have := h3 hl
      cases st <;> simp [this] at hk ⊢ <;> omega
    · right
      rcases ends_cases hcase (hendR hcase) hn with ⟨-, q⟩ | ⟨q, ⟨q1, -⟩ | ⟨-, -, q2⟩⟩
      · rw [ha] at q; cases q
      · rw [hnl] at q1; cases q1
      · rw [biasTot_su (hends hcase), biasTot]
        simp only [q2, and_false, ↓reduceIte]
        rcases hsite hcase with hst | hst
        · have := h1 1 (by rw [hst]; rfl)
          have := hprime hst
          omega
        · have := h2 0 (by rw [hst]; rfl)
          omega
    · left
      obtain ⟨⟨⟨q1, q2⟩, q3⟩, q4⟩ := hcase
      have := h1 0 q4
      simp only [LFits, q1] at hF
      exact ⟨q2, by omega, by omega⟩
  · rw [ite_eq_right ha] at hc2
    refine ⟨fun c h' => ?_, fun c h' => ?_, fun h' => ?_, fun h' => absurd h' ha⟩
    · rw [h'] at hc2
      cases hf : biasForm st d.site with
      | none => rw [hf] at hc2; cases hc2
      | some x =>
        obtain ⟨b, c0⟩ := x
        rw [hf] at hc2
        cases b
        · have := h1 _ hf
          simp only [beq_iff_eq] at hc2
          push_cast; omega
        · cases hc2
    · rw [h'] at hc2
      cases hf : biasForm st d.site with
      | none => rw [hf] at hc2; cases hc2
      | some x =>
        obtain ⟨b, c0⟩ := x
        rw [hf] at hc2
        cases b
        · have := h1 _ hf
          simp only [Bool.and_eq_true, beq_iff_eq] at hc2
          obtain ⟨⟨⟨⟨q1, q2⟩, q3⟩, q4⟩, q5⟩ := hc2
          have := hprime q5
          push_cast; omega
        · have := h2 _ hf
          simp only [Bool.and_eq_true, beq_iff_eq] at hc2
          push_cast; omega
    · rcases hc1 with (hc1 | hc1) | hc1
      · exact hLast (hlast hc1) (h3 hc1)
      · rcases ends_cases hc1 (hendR hc1) hn with ⟨q, -⟩ | ⟨-, ⟨-, -, q⟩ | ⟨q, -⟩⟩
        · rw [h'] at q; cases q
        · exact hLast (hends hc1) q
        · rw [h'] at q; cases q
      · rw [h'] at hc1; cases hc1

/-- **The Bias empty barriers' polls** at every state of a lane of warp 14. -/
theorem bias_num {m : Mem0} {X : Execution} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) : BiasNum L g (d, LdWarp.lcn n) := by
  refine LdWarp.step_at (w := 14) (I := fun _ dn => BiasNum L g dn) ?_ ?_ ?_ hp hX hg (.inl rfl) hw
    k b d n hσ hub
  · intro b k n _ _ _ st
    refine ⟨fun c h => ?_, fun c h => ?_, fun h => absurd h (by simp [Site.lastGrp]),
      fun h => absurd h (by simp [Site.aft])⟩
    · have : biasForm st (Site.setmax) = some (false, c) := h
      simp only [biasForm, Option.some.injEq, Prod.mk.injEq, true_and] at this
      simp [← this]
    · have : biasForm st (Site.setmax) = some (true, c) := h
      simp [biasForm] at this
  · intro k b n d e d' _ _ _ _ hF _ _ _ hn hm h
    exact num_step hF hn hm h
  · intro _ _ _ h; exact h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
