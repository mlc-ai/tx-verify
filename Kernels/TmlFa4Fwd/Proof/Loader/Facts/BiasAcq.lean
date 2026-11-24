-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.CountFact
public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.TmaArr
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's polls of the Bias empty barriers and its Bias parities

Standalone fact. On warp 14 the first block's groups poll each Bias empty barrier once, at parity 1;
in the warm rounds the Bias parities `%r6117`, `%r6118` are the parities of the lane's next polls of
barriers 336 and 344, which count the successful ones so far plus one (`BiasAcq`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Arith32

noncomputable section
set_option maxRecDepth 100000

/-- The polls of barrier 336 (`st = 0`) or 344 before a site of the first block, on warp 14. -/
def biasCnt (st : Bool) : Site → Option Nat
  | .tw t => if t.val < 4 then some (if (if st then 3 else 1) < t.val then 1 else 0) else none
  | .te t _ | .ta t | .tc t _ =>
    if t.val < 4 then some (if (if st then 3 else 1) ≤ t.val then 1 else 0) else none
  | .pgLd per _ | .pgSt per _ | .rwSt per _ => if per = .prime then some 0 else none
  | .slot per v | .ptP per v _ | .ptR per v _ | .ptS per v _ | .lw per v _ | .xl per v _
  | .xh per v _ | .cp per v _ _ | .commit per v | .arrive per v =>
    if per = .prime then some (if v then 1 else 0) else none
  | .word sk | .down sk | .up sk _ | .total sk => if sk.late then none else some 0
  | .vote l | .pre l | .tiles l => if l then none else some 0
  | .setmax | .q0 | .q1 | .uk => some 0
  | _ => none

/-- In a warm round (and at the last Bias group), one when the lane has polled the barrier since the
parity register's last flip. -/
def biasDbl (st : Bool) : Site → Option Nat
  | .tw t => if t.val = 4 then some 0 else if t.val = 5 then some (if st then 0 else 1)
      else if t.val = 6 ∧ st = false then some 0 else none
  | .te t _ | .ta t | .tc t _ =>
    if t.val = 4 then some (if st then 0 else 1) else if t.val = 5 then some 1 else none
  | .pgLd per _ | .pgSt per _ | .rwSt per _ | .slot per _ | .ptP per _ _ | .ptR per _ _
  | .ptS per _ _ | .lw per _ _ | .xl per _ _ | .xh per _ _ | .cp per _ _ _ | .commit per _
  | .arrive per _ => if per = .warm then some 0 else none
  | _ => none

/-- The sites whose step may write a Bias parity. -/
def bqWr : Site → Bool
  | .arrive _ _ | .te _ _ | .tc _ _ => true
  | _ => false

theorem bqWr_wr {s : Site} (h : bqWr s = false) : wr s .bq0 = false ∧ wr s .bq1 = false := by
  cases s <;> simp_all [bqWr, wr]

/-- The edge check (warp 14). -/
def biasChk (b : Bool) (s s' : Site) : Bool :=
  b || [false, true].all fun st =>
    let t := if tag s s' = .acq (if st then 344 else 336) then 1 else 0
    (match biasCnt st s' with
      | none => true
      | some c => match biasCnt st s with | none => false | some c0 => c == c0 + t) &&
    (bqWr s || match biasDbl st s' with
      | none => true
      | some δ => match biasDbl st s with | none => false | some δ0 => (δ + t) % 2 == δ0 % 2) &&
    (!bqWr s || t == 0)

theorem bias_self : AllSites fun s => biasChk false s s = true := by unfold AllSites; decide +kernel

theorem bias_edges : Edges biasChk := by unfold Edges AllSites; decide +kernel

/-- The Bias parity register of stage `st`. -/
def bq (st : Bool) (v : V) : BitVec 64 := if st then v.bq1 else v.bq0

/-- The fact at a counted state. -/
def BiasAcq (L : Launch) (g w : Nat) (dn : D × (Cnt → Nat)) : Prop :=
  w = 14 → ∀ st : Bool,
    (∀ c, biasCnt st dn.1.site = some c →
      dn.2 (.acquire (bl L g (if st then 344 else 336))) = c) ∧
    ∀ δ, biasDbl st dn.1.site = some δ → bq st dn.1.v = BitVec.ofNat 64
      ((dn.2 (.acquire (bl L g (if st then 344 else 336))) + 1 + δ) % 2)

variable {p : Params} {L : Launch} {g w : Nat}

theorem xori_par (a : Nat) : r32 (BitVec.ofNat 64 (a % 2)) ^^^ i32 1 =
    BitVec.ofNat 64 ((a + 1) % 2) := by
  rcases Nat.mod_two_eq_zero_or_one a with h | h
  · rw [h, show (a + 1) % 2 = 1 by omega]; decide
  · rw [h, show (a + 1) % 2 = 0 by omega]; decide

/-- A successor by cases of a predicate of the site and the values. -/
theorem ite_ind {P : Site → V → Prop} {c : Bool} {a b : D} (ha : P a.site a.v)
    (hb : P b.site b.v) : P (D.ite c a b).site (D.ite c a b).v := by
  cases c
  · exact hb
  · exact ha

theorem iteS_ind {P : Site → V → Prop} {c : Bool} {a b : D} (ha : P a.site a.v)
    (hb : P b.site b.v) : P (D.iteS c a b).site (D.iteS c a b).v := by
  cases c
  · exact hb
  · exact ha

theorem pgEnter_ind {P : Site → V → Prop} {d : D} {per : Per} {it : Fin 2}
    (ha : P (.pgSt per it) { d.v with pw := i32 0 }) (hb : P (.pgLd per it) d.v) :
    P (pgEnter p L g d per it).site (pgEnter p L g d per it).v :=
  iteS_ind ha hb

/-- A successor with no Bias obligation, or with the parities of `v`. -/
def Keep (v : V) (s : Site) (v' : V) : Prop :=
  ∀ st δ, biasDbl st s = some δ → δ = 0 ∧ bq st v' = bq st v

theorem passStart_keep {v : V} {d : D} :
    Keep v (passStart p L g true d).site (passStart p L g true d).v := by
  refine ite_ind (P := Keep v) ?_ ?_ <;> intro st δ h <;> simp [biasDbl] at h

theorem afterTail_keep {v : V} {d : D} :
    Keep v (afterTail p L g d).site (afterTail p L g d).v := by
  refine iteS_ind (P := Keep v) passStart_keep (pgEnter_ind (P := Keep v) ?_ ?_) <;>
    intro st δ h <;> simp [biasDbl] at h

theorem afterWarm_keep {v : V} {d : D} (h0 : d.v.bq0 = v.bq0) :
    Keep v (afterWarm p L g w d).site (afterWarm p L g w d).v := by
  refine iteS_ind (P := Keep v) afterTail_keep ?_
  intro st δ h
  cases st <;> simp [biasDbl] at h
  exact ⟨h.symm, by simpa [bq] using h0⟩

theorem afterArrive_keep {d : D} {per : Per} {vv : Bool} :
    Keep (if per = .prime ∧ vv = true then { d.v with bq1 := d.v.bq0 } else d.v)
      (afterArrive p L g w d per vv).site (afterArrive p L g w d per vv).v := by
  cases per <;> cases vv <;> simp only [afterArrive, reduceCtorEq, Bool.false_eq_true, and_false,
    and_self, false_and, ↓reduceIte]
  · refine ite_ind (P := Keep _) ?_ ?_ <;> intro st δ h <;> simp [biasDbl] at h
  · unfold afterPrime
    refine iteS_ind (P := Keep _) (afterWarm_keep rfl) (pgEnter_ind (P := Keep _) ?_ ?_) <;>
      intro st δ h <;> cases st <;> simp [biasDbl] at h <;> exact ⟨h.symm, rfl⟩
  · refine ite_ind (P := Keep _) ?_ ?_ <;> intro st δ h <;> cases st <;> simp [biasDbl] at h <;>
      exact ⟨h.symm, rfl⟩
  · unfold warmEnd
    refine iteS_ind (P := Keep _) (pgEnter_ind (P := Keep _) ?_ ?_) (afterWarm_keep rfl) <;>
      intro st δ h <;> cases st <;> simp [biasDbl] at h <;> exact ⟨h.symm, rfl⟩
  · intro st δ h; simp [biasDbl] at h
  · unfold steadyEnd
    refine iteS_ind (P := Keep _) (pgEnter_ind (P := Keep _) ?_ ?_) passStart_keep <;>
      intro st δ h <;> simp [biasDbl] at h

/-- A successor of an election or a copy: group 5's end flips the parities, the rest keep them. -/
def Flip (t : Fin 7) (v : V) (s : Site) (v' : V) : Prop :=
  ∀ st δ, biasDbl st s = some δ → (t.val = 4 ∧ δ = (if st then 0 else 1) ∧ bq st v' = bq st v) ∨
    t.val = 5 ∧ ((δ = 1 ∧ bq st v' = bq st v) ∨ δ = 0 ∧ bq st v' = r32 (bq st v) ^^^ i32 1)

theorem groupEnd_flip {v : V} {d : D} {t : Fin 7} (hv : t.val ≠ 3 → d.v = v) :
    Flip t v (groupEnd p L g d t).site (groupEnd p L g d t).v := by
  intro st δ h
  fin_cases t
  · simp [groupEnd, biasDbl] at h
  · simp [groupEnd, biasDbl] at h
  · simp [groupEnd, biasDbl] at h
  · simp [groupEnd, biasDbl] at h
  · have hv := hv (by simp)
    subst hv
    cases st <;> simp [groupEnd, biasDbl] at h <;> exact .inl ⟨rfl, h.symm, rfl⟩
  · have hv := hv (by simp)
    subst hv
    cases st <;> simp [groupEnd, biasDbl] at h <;> exact .inr ⟨rfl, .inr ⟨h.symm, rfl⟩⟩
  · exfalso
    have := (afterTail_keep (p := p) (L := L) (g := g) (v := v) (d := d))
    revert h
    change biasDbl st (afterTail p L g d).site = some δ → False
    refine iteS_ind (P := fun s _ => biasDbl st s = some δ → False)
      (ite_ind (P := fun s _ => biasDbl st s = some δ → False) ?_ ?_)
      (pgEnter_ind (P := fun s _ => biasDbl st s = some δ → False) ?_ ?_) <;>
      intro h <;> simp [biasDbl] at h

theorem te_flip {d : D} {t : Fin 7} {i : Fin 3} {c : Bool} :
    Flip t d.v (if c then teElected d t i else teNext p L g d t i).site
      (if c then teElected d t i else teNext p L g d t i).v := by
  have aux : ∀ s v', (s = .te t 1 ∨ s = .te t 2 ∨ s = .ta t ∨ s = .tc t 0 ∨ s = .tc t 1) →
      (t.val ≠ 3 → v' = d.v) → Flip t d.v s v' := by
    intro s v' hs hv st δ h
    have h4 : biasDbl st s = if t.val = 4 then some (if st then 0 else 1)
        else if t.val = 5 then some 1 else none := by
      rcases hs with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [h4] at h
    by_cases ht : t.val = 4
    · simp only [ht, ↓reduceIte, Option.some.injEq] at h
      exact .inl ⟨ht, h.symm, by rw [hv (by omega)]⟩
    · by_cases ht5 : t.val = 5
      · simp only [ht5, Nat.reduceEqDiff, ↓reduceIte, Option.some.injEq] at h
        exact .inr ⟨ht5, .inl ⟨h.symm, by rw [hv (by omega)]⟩⟩
      · simp [ht, ht5] at h
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fin_cases i
  · exact aux _ _ (.inl rfl) fun _ => rfl
  · exact aux _ _ (.inr (.inl rfl)) fun _ => rfl
  · exact groupEnd_flip fun h => by simp [h]
  · exact aux _ _ (.inr (.inr (.inl rfl))) fun _ => rfl
  · exact aux _ _ (.inr (.inr (.inr (.inl rfl)))) fun _ => rfl
  · refine aux _ _ (.inr (.inr (.inr (.inr rfl)))) fun h => ?_
    show (if t.val = 3 then { d.v with bq0 := i32 0 } else d.v) = d.v
    simp [h]

theorem bias_step {dn : D × (Cnt → Nat)} {e : Event} {d' : D} (hJ : Ref p L g w dn)
    (hev : Ev p L g w dn.1 e) (hn : succ p L g w dn.1 e = some (some d'))
    (hm : Move L g w dn e d') (h : BiasAcq L g w dn) :
    BiasAcq L g w (d', Code.bump (cls L g) dn.2 e) := by
  obtain ⟨d, n⟩ := dn
  intro hw st
  obtain ⟨h1, h2⟩ := h hw st
  simp only at h1 h2 hev hn ⊢
  set E := bl L g (if st then 344 else 336) with hE
  have hn14 : not14 w = false := by subst hw; rfl
  have hc : biasChk (not14 w) d.site d'.site = true := by
    rcases hm.edge with h' | h'
    · rw [h', hn14]
      exact AllSites.ok bias_self d.site
    · exact bias_edges.ok h'
  rw [hn14] at hc
  simp only [biasChk, Bool.false_or] at hc
  have hco := List.all_eq_true.mp hc st (by cases st <;> simp)
  simp only [Bool.and_eq_true] at hco
  obtain ⟨⟨c1, c2⟩, c3⟩ := hco
  have hb : Code.bump (cls L g) n e (.acquire E) = n (.acquire E) +
      if tag d.site d'.site = .acq (if st then 344 else 336) then 1 else 0 := by
    rw [bump_tag hm]
    cases tag d.site d'.site <;>
      simp only [Tag.cnt, reduceCtorEq, Option.some.injEq, Cnt.acquire.injEq, ↓reduceIte,
        Tag.acq.injEq, bl, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff, hE]
    case acqRing δ =>
      have hne : ¬ L.sharedBase + 56 + 8 * ((n .commit + δ) % 3) =
          L.sharedBase + if st then 344 else 336 := by
        have := Nat.mod_lt (n .commit + δ) (show 0 < 3 by decide)
        cases st <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      have hne' : ¬ 56 + 8 * ((n .commit + δ) % 3) = if st then 344 else 336 := fun h =>
        hne (by omega)
      simp [hne']
  rw [hb]
  refine ⟨fun c hc' => ?_, fun δ hδ => ?_⟩
  · rw [hc'] at c1
    simp only at c1
    cases h0 : biasCnt st d.site with
    | none => simp [h0] at c1
    | some c0 =>
      rw [h0] at c1
      rw [h1 c0 h0]
      exact (beq_iff_eq.mp c1).symm
  by_cases hwr : bqWr d.site = true
  swap
  · have hwf : bqWr d.site = false := by simpa using hwr
    rw [hwf, hδ] at c2
    simp only [Bool.false_or] at c2
    obtain ⟨w0, w1⟩ := bqWr_wr hwf
    have hk : bq st d'.v = bq st d.v := by
      have k0 : d'.v.bq0 = d.v.bq0 := hm.keep .bq0 w0
      have k1 : d'.v.bq1 = d.v.bq1 := hm.keep .bq1 w1
      cases st <;> simp [bq, k0, k1]
    cases h0 : biasDbl st d.site with
    | none => simp [h0] at c2
    | some δ0 =>
      rw [h0] at c2
      have c2 := beq_iff_eq.mp c2
      rw [hk, h2 δ0 h0]
      congr 1
      generalize (if tag d.site d'.site = Tag.acq (if st then 344 else 336) then 1 else 0) = t
        at c2 ⊢
      omega
  -- a write of the parities
  rw [hwr] at c3
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at c3
  rw [c3, Nat.add_zero]
  obtain ⟨site, v, kk⟩ := d
  cases site <;> simp only [bqWr, Bool.false_eq_true] at hwr
  case arrive per vv =>
    simp only [succ, Option.some.injEq] at hn
    subst hn
    obtain ⟨rfl, hk⟩ := afterArrive_keep (p := p) (L := L) (g := g) st δ hδ
    rw [hk]
    by_cases hpv : per = .prime ∧ vv = true
    · obtain ⟨rfl, rfl⟩ := hpv
      have hbq : v.bq0 = BitVec.ofNat 64 0 := by
        have := hJ.words
        simpa [ringCls, RingWords, hw] using this
      have := h1 1 (by simp [biasCnt])
      rw [this]
      cases st <;> simp [bq, hbq]
    · simp only [hpv, ↓reduceIte]
      refine h2 0 ?_
      cases per
      · exfalso
        cases vv
        · revert hδ
          change biasDbl st (D.ite _ _ _).site = some 0 → False
          refine ite_ind (P := fun s _ => biasDbl st s = some 0 → False) ?_ ?_ <;>
            intro h <;> simp [biasDbl] at h
        · exact hpv ⟨rfl, rfl⟩
      · simp [biasDbl]
      · exfalso
        cases vv
        · simp [afterArrive, biasDbl] at hδ
        · revert hδ
          change biasDbl st (steadyEnd p L g _).site = some 0 → False
          refine iteS_ind (P := fun s _ => biasDbl st s = some 0 → False)
            (pgEnter_ind (P := fun s _ => biasDbl st s = some 0 → False) ?_ ?_)
            (ite_ind (P := fun s _ => biasDbl st s = some 0 → False) ?_ ?_) <;>
            intro h <;> simp [biasDbl] at h
  case te t i =>
    have hF : Flip t v d'.site d'.v := by
      obtain ⟨pc, kd⟩ := e
      cases kd <;> simp only [succ, reduceCtorEq, Option.some.injEq] at hn
      rename_i ld
      subst hn
      have := te_flip (p := p) (L := L) (g := g) (d := ⟨.te t i, v, kk⟩) (t := t) (i := i)
        (c := decide (laneOf L g = ld))
      simpa only [decide_eq_true_eq] using this
    have hs : biasDbl st (.te t i) = if t.val = 4 then some (if st then 0 else 1)
        else if t.val = 5 then some 1 else none := rfl
    rcases hF st δ hδ with ⟨ht, rfl, hk⟩ | ⟨ht, ⟨rfl, hk⟩ | ⟨rfl, hk⟩⟩
    · rw [hk]; exact h2 _ (by rw [hs]; simp [ht])
    · rw [hk]; exact h2 _ (by rw [hs]; simp [ht])
    · rw [hk, h2 1 (by rw [hs]; simp [ht]), xori_par]
      congr 1; omega
  case tc t c =>
    have hs : biasDbl st (.tc t c) = if t.val = 4 then some (if st then 0 else 1)
        else if t.val = 5 then some 1 else none := rfl
    have hF : Flip t v d'.site d'.v := by
      by_cases hc0 : c.val = 0
      · simp only [succ, hc0, ↓reduceIte, Option.some.injEq] at hn
        subst hn
        intro st δ h
        have h4 : biasDbl st (Site.te t 2) = if t.val = 4 then some (if st then 0 else 1)
            else if t.val = 5 then some 1 else none := rfl
        simp only at h
        rw [h4] at h
        by_cases ht : t.val = 4
        · simp only [ht, ↓reduceIte, Option.some.injEq] at h
          exact .inl ⟨ht, h.symm, rfl⟩
        · by_cases ht5 : t.val = 5
          · simp only [ht5, Nat.reduceEqDiff, ↓reduceIte, Option.some.injEq] at h
            exact .inr ⟨ht5, .inl ⟨h.symm, rfl⟩⟩
          · simp [ht, ht5] at h
      · simp only [succ, hc0, ↓reduceIte, Option.some.injEq] at hn
        subst hn
        exact groupEnd_flip fun _ => rfl
    rcases hF st δ hδ with ⟨ht, rfl, hk⟩ | ⟨ht, ⟨rfl, hk⟩ | ⟨rfl, hk⟩⟩
    · rw [hk]; exact h2 _ (by rw [hs]; simp [ht])
    · rw [hk]; exact h2 _ (by rw [hs]; simp [ht])
    · rw [hk, h2 1 (by rw [hs]; simp [ht]), xori_par]
      congr 1; omega

/-- **The Bias empty barriers' polls and parities** at every state of a loader lane. -/
theorem bias_acq {m : Mem0} {X : Execution} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) : BiasAcq L g (wOf b) (d, LdWarp.lcn n) :=
  LdWarp.count_at (I := fun w dn _ => BiasAcq L g w dn) (c := fun _ => false)
    (fun _ h => by cases h)
    (fun b _ st => ⟨fun c h => by simpa [biasCnt] using h, fun δ h => by simp [biasDbl] at h⟩)
    (fun _ _ _ _ _ _ hJ hev _ hn hm h => bias_step hJ hev hn hm h) hp hX hg hw k b d n hσ hub

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
