-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.QAcq
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
public import Lemmas.Flow.NotTensor
import Kernels.TmlFa4Fwd.Proof.LdWarp.Hist
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Loader.RefBase
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The first TMA groups of warp 14: their events

Standalone facts about the first four TMA groups (Q and Bias of the first block). `ppos` orders
their sites along the first block. A lane of warp 14 past the arrival (or a copy) of a group made
it, unless it lost an election (`group_hist`); and it made at most as many copies completing on a
Q stage as the sites it is past (`q_copies`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The position of a site along the first block: the sites of the first four TMA groups in order,
0 before them and 1000 after them (`z`: the lane has committed no packet). -/
def ppos (z : Bool) : Site → Nat
  | .pgLd per _ | .pgSt per _ | .rwSt per _ => if per = .prime then 0 else 1000
  | .slot per v | .ptP per v _ | .ptR per v _ | .ptS per v _ | .lw per v _ | .xl per v _
  | .xh per v _ | .cp per v _ _ | .commit per v | .arrive per v =>
    if per = .prime then if v then 1000 else 0 else 1000
  | .tw t => if t.val < 4 then 10 * t.val + 1 else 1000
  | .te t i => if t.val < 4 then 10 * t.val + 2 + 2 * i.val else 1000
  | .ta t => if t.val < 4 then 10 * t.val + 3 else 1000
  | .tc t c => if t.val < 4 then 10 * t.val + 5 + 2 * c.val else 1000
  | _ => if z then 0 else 1000

/-- The site after election `i` of group `t` on the lane it elected. -/
def wonSite (t : Fin 7) (i : Fin 3) : Site :=
  if i.val = 0 then .ta t else if i.val = 1 then .tc t 0 else .tc t 1

/-- The position of `wonSite t i`. -/
def wonPos (t : Fin 7) (i : Fin 3) : Nat := 10 * t.val + 3 + 2 * i.val

/-- The edge check on warp 14: an edge past `wonSite t i` leaves that site or the election before
it without winning it. -/
def grpChk (b : Bool) (s s' : Site) : Bool :=
  b || (List.finRange 7).all fun t => (List.finRange 3).all fun i => [false, true].all fun z =>
    !(decide (t.val < 4) && zOk s z &&
        decide (wonPos t i < ppos (z && tag s s' != .commit) s')) ||
      decide (wonPos t i < ppos z s) || s == wonSite t i ||
      (s == .te t i && tag s s' == .none)

theorem grp_edges : Edges grpChk := by unfold Edges AllSites; decide +kernel

/-- The copies completing on the stage of group `t` before a position. -/
def cpos (t : Fin 7) (x : Nat) : Nat :=
  if x ≤ 10 * t.val + 5 then 0 else if x ≤ 10 * t.val + 7 then 1 else 2

/-- The edge check for the copies of the Q groups. -/
def qCpChk (b : Bool) (s s' : Site) : Bool :=
  b || [(0 : Fin 7), 2].all fun t => [false, true].all fun z =>
    !zOk s z ||
      decide (cpos t (ppos z s) +
        (if s = .tc t 0 ∨ s = .tc t 1 then 1 else 0) ≤ cpos t (ppos (z && tag s s' != .commit) s'))

theorem q_cp_edges : Edges qCpChk := by unfold Edges AllSites; decide +kernel

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The commits' case after a step. -/
theorem z_next {dn : D × (Cnt → Nat)} {e : Event} {d' : D} (hm : Move L g 14 dn e d') :
    decide (Code.bump (cls L g) dn.2 e .commit = 0) =
      (decide (dn.2 .commit = 0) && tag dn.1.site d'.site != .commit) := by
  rw [bump_tag hm]
  cases tag dn.1.site d'.site <;> simp [Tag.cnt]

/-- A lane of warp 14 past `wonSite t i` left it by its event, or lost an election. -/
def GroupHist (p : Params) (L : Launch) (X : Execution) (g k : Nat) (dn : D × (Cnt → Nat)) :
    Prop :=
  ∀ (t : Fin 7) (i : Fin 3), t.val < 4 →
    wonPos t i < ppos (decide (dn.2 .commit = 0)) dn.1.site →
    (∃ j < k, ∃ e d, X.get (g, j) = some e ∧ d.site = wonSite t i ∧ Ev p L g 14 d e ∧
        ∃ b n, Frame.stateAt (thread p L) X g j = some (some (LdWarp.linj p L g b d n))) ∨
      ∃ j < k, ∃ pc inst ld, X.get (g, j) = some ⟨pc, .elect (2 ^ 32 - 1) inst ld⟩ ∧
        ld ≠ laneOf L g

/-- **A lane of warp 14 past the arrival or a copy of one of the first four TMA groups made it,
or lost an election.** -/
theorem group_hist (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 14)
    (hub : ¬ HasUb X) {k : Nat} {b : Bool} {d : D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (h0 : n .ub = 0) : GroupHist p L X g k (d, LdWarp.lcn n) := by
  refine LdWarp.hist_at (w := 14) (I := GroupHist p L X g) ?_ ?_ ?_ hp hX hg (.inl rfl) hw k b d n
    hσ h0
  · intro b k n _ _ t i ht h
    simp [ppos, wonPos] at h
  · intro k dn e d' he hst hJ hev hm h t i ht hpos
    obtain ⟨d, n⟩ := dn
    simp only at hst hJ hev hm h hpos ⊢
    rw [z_next hm] at hpos
    by_cases hpast : wonPos t i < ppos (decide (n .commit = 0)) d.site
    · rcases h t i ht hpast with ⟨j, hj, r⟩ | ⟨j, hj, r⟩
      · exact .inl ⟨j, by omega, r⟩
      · exact .inr ⟨j, by omega, r⟩
    rcases hm.edge with hs | hs
    · rw [hs] at hpos
      rw [tag_self, show (Tag.none != Tag.commit) = true from rfl, Bool.and_true] at hpos
      exact absurd hpos hpast
    have hz := z_ok hJ
    have hc := grp_edges.ok hs
    simp only [grpChk, show not14 14 = false from rfl, Bool.false_or, List.all_eq_true,
      List.mem_finRange, forall_const] at hc
    have hc := hc t i (decide (n .commit = 0)) (by cases decide (n .commit = 0) <;> simp)
    simp only [hz, ht, hpos, hpast, decide_true, decide_false, Bool.and_true,
      Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
    rcases hc with hc | ⟨hc, htag⟩
    · exact .inl ⟨k, by omega, e, d, he, hc, hev, hst⟩
    · obtain ⟨pc, kind⟩ := e
      simp only [Ev, hc] at hev
      rcases hev with ⟨inst, ld, hpc, hk⟩ | ⟨f, hk⟩
      · obtain rfl : kind = _ := hk
        refine .inr ⟨k, by omega, pc, inst, ld, he, fun hld => ?_⟩
        have h1 := hm.cnt (.won pc)
        simp only [htag, Tag.cnt, cls, hld, decide_true, Bool.and_self, reduceCtorEq,
          decide_false] at h1
      · obtain rfl : kind = _ := hk
        exact (hub ⟨(g, k), pc, f, he⟩).elim
  · intro k dn _ h t i ht hpos
    rcases h t i ht hpos with ⟨j, hj, r⟩ | ⟨j, hj, r⟩
    · exact .inl ⟨j, by omega, r⟩
    · exact .inr ⟨j, by omega, r⟩

/-- The edge check: a step to an elected lane's copy wins an election. -/
def wonChk (_ : Bool) (s s' : Site) : Bool :=
  match s' with
  | .tc _ _ => match tag s s' with | .won _ => true | _ => false
  | _ => true

theorem won_edges : Edges wonChk := by unfold Edges AllSites; decide +kernel

/-- **A lane of warp 14 at a copy of a TMA group won an election before.** -/
theorem tc_won (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 14) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (h0 : n .ub = 0) {t : Fin 7} {c : Fin 2} (hs : d.site = .tc t c) :
    ∃ j < k, ∃ pc m inst, X.get (g, j) = some ⟨pc, .elect m inst (laneOf L g)⟩ := by
  refine LdWarp.hist_at (w := 14) (I := fun k dn => ∀ t c, dn.1.site = .tc t c →
    ∃ j < k, ∃ pc m inst, X.get (g, j) = some ⟨pc, .elect m inst (laneOf L g)⟩) ?_ ?_ ?_
    hp hX hg (.inl rfl) hw k b d n hσ h0 t c hs
  · intro b k n _ _ t c h
    cases h
  · intro k dn e d' he _ hJ hev hm h t c hs
    obtain ⟨d, n⟩ := dn
    simp only at hev hm h hs
    rcases hm.edge with hs' | hs'
    · rw [hs] at hs'
      obtain ⟨j, hj, r⟩ := h t c hs'.symm
      exact ⟨j, by omega, r⟩
    · have hc := won_edges.ok hs'
      simp only at hc
      rw [hs] at hc
      simp only [wonChk] at hc
      split at hc
      · rename_i pc htag
        have h1 := hm.cnt (.won pc)
        simp only [hs, htag, Tag.cnt, decide_true] at h1
        obtain ⟨pc', kind⟩ := e
        cases kind <;> simp [cls] at h1
        obtain ⟨-, rfl⟩ := h1
        exact ⟨k, by omega, _, _, _, he⟩
      · cases hc
  · intro k dn _ h t c hs
    obtain ⟨j, hj, r⟩ := h t c hs
    exact ⟨j, by omega, r⟩

/-- A TMA group's copies complete on its barrier. -/
theorem tc_bar (hp : Pre p L m) (t : Fin 7) (c : Fin 2) {v : V} {kk : Fin 2} :
    smLoc L g (rv p L g 14 ⟨.tc t c, v, kk⟩ (tcBar t).1) (tcBar t).2 = bl L g (taOff t) := by
  fin_cases t
  · exact smLoc_sb hp 0 (by norm_num)
  · exact smLoc_addi hp 320 (by norm_num)
  · exact smLoc_sb hp 8 (by norm_num)
  · exact smLoc_sb hp 328 (by norm_num)
  · exact smLoc_addi hp 320 (by norm_num)
  · exact smLoc_sb hp 328 (by norm_num)
  · exact smLoc_addi hp 320 (by norm_num)

/-- A group completing on a Q stage is that stage's. -/
theorem q_group {t t' : Fin 7} (ht : t = 0 ∨ t = 2) (h : taOff t = taOff t') : t' = t := by
  revert t t'; decide

/-- **A lane of warp 14 makes at most two copies that complete on a Q stage.** -/
theorem q_copies (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 14) {t : Fin 7} (ht : t = 0 ∨ t = 2)
    {k : Nat} {b : Bool} {d : D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (h0 : n .ub = 0) :
    ((X.tr g).take k).countP (issuesTo (bl L g (taOff t))) ≤
      cpos t (ppos (decide (n (.load .commit) = 0)) d.site) := by
  refine LdWarp.hist_at (w := 14) (I := fun k dn => ((X.tr g).take k).countP
    (issuesTo (bl L g (taOff t))) ≤ cpos t (ppos (decide (dn.2 .commit = 0)) dn.1.site)) ?_ ?_ ?_
    hp hX hg (.inl rfl) hw k b d n hσ h0
  · intro b k n hσ hz
    have h1 : ((X.tr g).take k).countP (Proof.cls L g (.load .copy)) = 0 := by
      rw [count hσ]; exact congrFun hz .copy
    have h2 : ((X.tr g).take k).countP (issuesTo (bl L g (taOff t))) = 0 := by
      rw [List.countP_eq_zero] at h1 ⊢
      intro e he
      have := h1 e he
      obtain ⟨pc, kind⟩ := e
      cases kind <;> simp_all [issuesTo, Proof.cls, cls]
    rw [h2]; exact Nat.zero_le _
  · intro k dn e d' he hst hJ hev hm h
    clear hst
    obtain ⟨d, n⟩ := dn
    simp only at hJ hev hm h ⊢
    have hstep : ((X.tr g).take (k + 1)).countP (issuesTo (bl L g (taOff t))) =
        ((X.tr g).take k).countP (issuesTo (bl L g (taOff t))) +
          if issuesTo (bl L g (taOff t)) e then 1 else 0 := by
      have he' : (X.tr g)[k]? = some e := he
      rw [List.take_add_one, he', List.countP_append]
      simp [List.countP_cons]
    rw [hstep, z_next hm]
    have hz := z_ok hJ
    simp only at hz
    -- a copy to the stage is at one of the group's two copy sites, and moves
    have hat : issuesTo (bl L g (taOff t)) e = true →
        (d.site = .tc t 0 ∨ d.site = .tc t 1) ∧ d'.site ≠ d.site := by
      intro hi
      obtain ⟨pc, kind⟩ := e
      cases kind <;> simp only [issuesTo, Bool.false_eq_true] at hi
      rename_i a sp
      have hmb : sp.mbar = bl L g (taOff t) := by simpa using hi
      have hcp := hm.cnt .copy
      simp only [cls] at hcp
      have htag : tag d.site d'.site = .copy := by
        have := of_decide_eq_true hcp.symm
        cases h : tag d.site d'.site <;> rw [h] at this <;> simp [Tag.cnt] at this
      refine ⟨?_, fun h => by rw [h, tag_self] at htag; cases htag⟩
      obtain ⟨s, v, kk⟩ := d
      simp only at htag hev ⊢
      cases s <;> simp only [tag] at htag <;> (try (split at htag <;> simp at htag; done))
      case cp per v' i c =>
        simp only [Ev] at hev
        rcases hev with ⟨_, hk⟩ | ⟨_, hk⟩ <;> cases hk
      case tc t' c =>
        simp only [Ev] at hev
        rcases hev with ⟨a', s', hk, hb⟩ | ⟨_, hk⟩
        · obtain ⟨rfl, rfl⟩ := Kind.tensorIssue.inj hk
          rw [hmb, tc_bar hp] at hb
          have ho : taOff t = taOff t' := by
            simp only [bl, Loc.mk.injEq, true_and] at hb; omega
          obtain rfl := q_group ht ho
          fin_cases c <;> simp
        · cases hk
      all_goals (split at htag <;> (try split at htag) <;> simp at htag)
    by_cases hself : d'.site = d.site
    · have hi : issuesTo (bl L g (taOff t)) e = false := by
        cases hx : issuesTo (bl L g (taOff t)) e
        · rfl
        · exact absurd hself (hat hx).2
      rw [hself, tag_self, show (Tag.none != Tag.commit) = true from rfl, Bool.and_true, hi]
      simpa using h
    have hc := q_cp_edges.ok (hm.edge.resolve_left hself)
    simp only [qCpChk, show not14 14 = false from rfl, Bool.false_or, List.all_eq_true] at hc
    have hc := hc t (by rcases ht with rfl | rfl <;> simp) (decide (n .commit = 0))
      (by cases decide (n .commit = 0) <;> simp)
    rw [hz, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc
    refine le_trans ?_ hc
    refine Nat.add_le_add h ?_
    by_cases hi : issuesTo (bl L g (taOff t)) e = true
    · rw [ite_eq_left hi, ite_eq_left (hat hi).1]
    · rw [ite_eq_right hi]; exact Nat.zero_le _
  · intro k dn hk h
    rw [List.take_of_length_le (by omega)] at h ⊢
    exact h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
