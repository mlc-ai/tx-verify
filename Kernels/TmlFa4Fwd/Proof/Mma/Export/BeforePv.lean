-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Before
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Prev
public import Kernels.TmlFa4Fwd.Proof.Lib.Export
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Mma.Counts
import Kernels.TmlFa4Fwd.Proof.Mma.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Mma.Poll
import Lemmas.Flow.NthEv
import Lemmas.Protocol.UnitHandoff
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The PV block before an MMA or a commit

An MMA or a commit after `v + 1` polls of the stage's P-full barrier follows step 0 of the stage's
PV block of tile `v`, or is that MMA (`pv_before`): from the successful poll the lane runs its
broadcasts and the block's election, which it wins, to the block. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : Prologue.warpIndex L g = 12)
include hp hX hFw hw

/-- The kind of an event between a P-full poll and the block's first MMA. -/
def Between (e : Event) : Prop :=
  (∃ pc a b c d f g, e = ⟨pc, .shfl a b c d f g⟩) ∨ ∃ pc a b c, e = ⟨pc, .elect a b c⟩

/-- The site from which the PV block `b` is entered. -/
def walkNext : Site → Site
  | .sh k => shNext k
  | .ep b => .pv b 0
  | s => s

omit hFw hw in
/-- One step of the way from a P-full poll to the PV block. -/
theorem walk_step {K i : Nat} {d dK : D} {n nK : Cls → Nat}
    (hσK : Frame.stateAt (thread p L) X g K = some (some (minj p L g dK nK)))
    (hlK : K < (X.tr g).length)
    (hub : nK .ub = 0) (hlost : nK (.mma .lost) = 0) (hi : i ≤ K) (hws : winSite dK.site = true)
    (hσ : Frame.stateAt (thread p L) X g i = some (some (minj p L g d n)))
    (hs : (∃ k, d.site = .sh k) ∨ ∃ b, d.site = .ep b) :
    i + 1 ≤ K ∧ (∃ e, X.get (g, i) = some e ∧ Between e) ∧
      ∃ d' n', Frame.stateAt (thread p L) X g (i + 1) = some (some (minj p L g d' n')) ∧
        d'.site = walkNext d.site := by
  have hne : i ≠ K := by
    rintro rfl
    rw [hσ] at hσK
    simp only [minj, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq,
      true_and] at hσK
    obtain ⟨rfl, -⟩ := hσK
    rcases hs with ⟨k, hs⟩ | ⟨b, hs⟩ <;> rw [hs] at hws <;> cases hws
  have hiK : i < K := by omega
  have hli : i < (X.tr g).length := by omega
  obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e := ⟨_, List.getElem?_eq_getElem hli⟩
  obtain ⟨d', hd, hσ'⟩ := mma_fwd hσ he hiK hσK
  have hev := (mfired hp hX he hσ).1
  obtain ⟨pc, kd⟩ := e
  obtain ⟨site, v⟩ := d
  rcases hs with ⟨k, hs⟩ | ⟨b, hs⟩ <;> simp only at hs <;> subst hs
  · simp only [Ev] at hev
    obtain ⟨recv, ok, rfl⟩ := hev
    refine ⟨hiK, ⟨_, he, .inl ⟨_, _, _, _, _, _, _, rfl⟩⟩, d', _, hσ', ?_⟩
    simp only [succ, word32] at hd
    repeat' split at hd
    all_goals first | (cases hd; done) | (cases hd; rfl)
  · simp only [Ev] at hev
    rcases hev with ⟨inst, ld, -, rfl⟩ | ⟨f, rfl⟩
    · refine ⟨hiK, ⟨_, he, .inr ⟨_, _, _, _, rfl⟩⟩, d', _, hσ', ?_⟩
      have hwon := elect_won hX hσK hlost hiK he
      simp only [succ, hwon, ↓reduceIte, Option.some.injEq] at hd
      subst hd
      rfl
    · exfalso
      have hcu := count hσK .ub
      rw [hub, List.countP_eq_zero] at hcu
      have hmem : (⟨pc, .ub f⟩ : Event) ∈ (X.tr g).take K := by
        have : ((X.tr g).take K)[i]? = some ⟨pc, .ub f⟩ := by
          rw [List.getElem?_take, ite_eq_left hiK]; exact he
        exact List.mem_of_getElem? this
      exact hcu _ hmem (by simp [Proof.cls])

omit hp hX hFw hw in
/-- Such an event is no poll. -/
theorem between_polls {i st : Nat} {e : Event} (he : X.get (g, i) = some e) (hb : Between e) :
    Tm.pPolls L X g st (i + 1) = Tm.pPolls L X g st i := by
  unfold Tm.pPolls okPolls
  have he' : (X.tr g)[i]? = some e := he
  rw [List.take_add_one, he', Option.toList_some, List.countP_append]
  rcases hb with ⟨_, _, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
    simp [okPoll, sourceWaitSuccess]

omit hFw hw in
/-- The way from a site to the PV block. -/
theorem walk {K : Nat} {dK : D} {nK : Cls → Nat}
    (hσK : Frame.stateAt (thread p L) X g K = some (some (minj p L g dK nK)))
    (hlK : K < (X.tr g).length)
    (hub : nK .ub = 0) (hlost : nK (.mma .lost) = 0) (hws : winSite dK.site = true) (st : Nat)
    (b : Fin 4) : ∀ (f i : Nat) (d : D) (n : Cls → Nat), i ≤ K →
      Frame.stateAt (thread p L) X g i = some (some (minj p L g d n)) →
      (∀ t < f, (∃ k, walkNext^[t] d.site = .sh k) ∨ ∃ b, walkNext^[t] d.site = .ep b) →
      walkNext^[f] d.site = .pv b 0 →
      ∃ i' d' n', i' ≤ K ∧ Frame.stateAt (thread p L) X g i' = some (some (minj p L g d' n')) ∧
        d'.site = .pv b 0 ∧ Tm.pPolls L X g st i' = Tm.pPolls L X g st i := by
  intro f
  induction f with
  | zero => exact fun i d n hi hσ _ hs => ⟨i, d, n, hi, hσ, hs, rfl⟩
  | succ f ih =>
    intro i d n hi hσ hst hs
    obtain ⟨hi', ⟨e, he, hb⟩, d', n', hσ', hs'⟩ :=
      walk_step hp hX hσK hlK hub hlost hi hws hσ (hst 0 (Nat.succ_pos f))
    obtain ⟨i1, d1, n1, h1, h2, h3, h4⟩ := ih (i + 1) d' n' hi' hσ'
      (fun t ht => by rw [hs']; exact hst (t + 1) (by omega)) (by rw [hs']; exact hs)
    exact ⟨i1, d1, n1, h1, h2, h3, h4.trans (between_polls he hb)⟩

/-- **The PV block of a tile before an MMA or a commit** that follows the tile's P-full poll. -/
theorem pv_before {K pc st v : Nat} {k : TcKind} (hst : st < 2)
    (he : X.get (g, K) = some ⟨pc, .tc k⟩)
    (hk : (∃ d s acc mask, k = .mma d s acc mask) ∨ ∃ s, k = .commit s)
    (hv : v + 1 ≤ Tm.pPolls L X g st K) : ∃ i, i ≤ K ∧ Tm.Pv L X g i st v 0 := by
  obtain ⟨dK, nK, hσK, -, hws, hlost, hub, -⟩ := win_state hp hX hFw hw he hk
  have hlK := (List.getElem?_eq_some_iff.mp (show (X.tr g)[K]? = _ from he)).1
  obtain ⟨j, pcj, par, acq, sc, hjK, hget, hcnt⟩ := MbarRing.UnitHandoff.exists_poll (X := X)
    (m := Tm.pFull L (g / L.block) st) (h := g) (f := K) (c := v) hv
  -- the poll's site
  obtain ⟨d, n, hσ, hs⟩ : ∃ d n, Frame.stateAt (thread p L) X g j =
      some (some (minj p L g d n)) ∧ ((st = 0 ∧ (d.site = .wt 4 ∨ d.site = .wt 8)) ∨
        (st = 1 ∧ (d.site = .wt 6 ∨ d.site = .wt 9))) := by
    rcases mma_counts hp hX hFw hw hget (fun f h => by cases h) with ⟨s', n, hS, hev, hx⟩ | hev |
      ⟨d, n, r, w, hσ, hQ, hcm, hF, hev⟩
    · exfalso
      obtain ⟨site, x1, x2, x3⟩ := s'
      cases site
      case enter r => simp [exit] at hx
      case sh j => fin_cases j <;> simp [Startup.Ev] at hev
      all_goals simp [Startup.Ev] at hev
    · rcases hev with ⟨_, _, _, hk'⟩ | ⟨_, _, _, hk'⟩ | ⟨_, _, hk'⟩ | ⟨_, hk'⟩ <;> cases hk'
    · refine ⟨d, n, hσ, ?_⟩
      cases mma_use hev (l := Tm.pFull L (g / L.block) st) rfl with
      | commit c s _ hk' => cases hk'
      | poll ok hp' hl hk' =>
        have h1 := hl.trans (Progress.par_eq hp hQ hp').1
        simp only [Tm.pFull, Tm.bar, bl, Loc.mk.injEq, true_and] at h1
        clear hl hk' hQ hF hcm hev hσ
        obtain ⟨site, v'⟩ := d
        simp only at hp' h1 ⊢
        cases site <;> simp only [Progress.isPoll, reduceCtorEq, Bool.false_eq_true] at hp'
        case wt kk =>
          fin_cases kk <;> simp [Progress.pollO] at h1 ⊢ <;> omega
        case mw b ld =>
          simp only [Progress.pollO] at h1
          split at h1 <;> omega
  obtain ⟨d', hd, hσ'⟩ := mma_fwd hσ hget hjK hσK
  have hp1 : Tm.pPolls L X g st (j + 1) = v + 1 := by
    unfold Tm.pPolls
    have hg' : (X.tr g)[j]? = _ := hget
    rw [List.take_add_one, hg', Option.toList_some, okPolls_snoc, hcnt]
    simp [okPoll, sourceWaitSuccess]
  have hw' := walk hp hX hσK hlK hub hlost hws st
  obtain ⟨site, v'⟩ := d
  have key : ∃ b : Fin 4, b.val % 2 = st ∧ ∃ i' d' n', i' ≤ K ∧
      Frame.stateAt (thread p L) X g i' = some (some (minj p L g d' n')) ∧
      d'.site = .pv b 0 ∧ Tm.pPolls L X g st i' = v + 1 := by
    have hsh : ∀ k : Fin 14, (∃ k', Site.sh k = .sh k') ∨ ∃ b, Site.sh k = .ep b :=
      fun k => .inl ⟨k, rfl⟩
    have hep : ∀ b : Fin 4, (∃ k', Site.ep b = .sh k') ∨ ∃ b', Site.ep b = .ep b' :=
      fun b => .inr ⟨b, rfl⟩
    rcases hs with ⟨rfl, hs | hs⟩ | ⟨rfl, hs | hs⟩ <;> simp only at hs <;> subst hs <;>
      simp only [succ, ↓reduceIte, Option.some.injEq] at hd <;> subst hd
    · obtain ⟨i', d', n', a, b, c, e⟩ := hw' 0 4 (j + 1) _ _ hjK hσ' (by
        intro t ht
        interval_cases t
        · exact hsh 3
        · exact hsh 4
        · exact hsh 5
        · exact hep 0) rfl
      exact ⟨0, rfl, i', d', n', a, b, c, e.trans hp1⟩
    · obtain ⟨i', d', n', a, b, c, e⟩ := hw' 2 4 (j + 1) _ _ hjK hσ' (by
        intro t ht
        interval_cases t
        · exact hsh 9
        · exact hsh 10
        · exact hsh 11
        · exact hep 2) rfl
      exact ⟨2, rfl, i', d', n', a, b, c, e.trans hp1⟩
    · obtain ⟨i', d', n', a, b, c, e⟩ := hw' 1 3 (j + 1) _ _ hjK hσ' (by
        intro t ht
        interval_cases t
        · exact hsh 7
        · exact hsh 8
        · exact hep 1) rfl
      exact ⟨1, rfl, i', d', n', a, b, c, e.trans hp1⟩
    · obtain ⟨i', d', n', a, b, c, e⟩ := hw' 3 3 (j + 1) _ _ hjK hσ' (by
        intro t ht
        interval_cases t
        · exact hsh 12
        · exact hsh 13
        · exact hep 3) rfl
      exact ⟨3, rfl, i', d', n', a, b, c, e.trans hp1⟩
  obtain ⟨b, rfl, i', d1, n1, hi', hσ1, hs1, hcnt1⟩ := key
  have hli : i' < (X.tr g).length := by omega
  obtain ⟨ei, hgi⟩ : ∃ e, X.get (g, i') = some e := ⟨_, List.getElem?_eq_getElem hli⟩
  have hev := (mfired hp hX hgi hσ1).1
  obtain ⟨pci, kd⟩ := ei
  simp only [Ev, hs1] at hev
  rcases hev with ⟨a, s, acc, ms, rfl⟩ | ⟨f, rfl⟩
  · obtain ⟨d', m', hσ2, hJ, -⟩ := win_state hp hX hFw hw hgi (.inl ⟨_, _, _, _, rfl⟩)
    have hEq := hσ1.symm.trans hσ2
    simp only [minj, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq,
      true_and] at hEq
    obtain ⟨rfl, rfl⟩ := hEq
    obtain ⟨u, hu⟩ := (mma_at_site hp hX hw hgi hσ1 hJ).2 b 0 hs1
    have := hu.p
    obtain rfl : u = v := by omega
    exact ⟨i', hi', hu⟩
  · exfalso
    rcases Nat.lt_or_eq_of_le hi' with hlt | rfl
    · have hcu := count hσK .ub
      rw [hub, List.countP_eq_zero] at hcu
      have hmem : (⟨pci, .ub f⟩ : Event) ∈ (X.tr g).take K := by
        have : ((X.tr g).take K)[i']? = some ⟨pci, .ub f⟩ := by
          rw [List.getElem?_take, ite_eq_left hlt]; exact hgi
        exact List.mem_of_getElem? this
      exact hcu _ hmem (by simp [Proof.cls])
    · rw [he] at hgi
      cases hgi

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
