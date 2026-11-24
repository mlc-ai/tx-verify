-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Before
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.PrevRel
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Mma.Counts
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Mma.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Mma.Poll
import Lemmas.Flow.NthEv
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMAs before a K/V release

The commit that releases ring use `t` follows the eight MMAs of stage 1 that read the use's slot:
the QK MMAs of tile `t / 2`, or its PV MMAs (`kv_block`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : Prologue.warpIndex L g = 12)

/-- S-full commits of stage 1 before a position. -/
abbrev sc (L : Launch) (X : Execution) (g i : Nat) : Nat := Tm.sCommits L X g 1 i

theorem sc_step {i : Nat} {e : Event} (he : X.get (g, i) = some e)
    (hf : commitsTo (Tm.sFull L (g / L.block) 1) e = false) : sc L X g (i + 1) = sc L X g i := by
  have he' : (X.tr g)[i]? = some e := he
  unfold sc Tm.sCommits
  rw [List.take_add_one, he', Option.toList_some, List.countP_append]
  simp [hf]

theorem no_ub {K i : Nat} {σ : (glued p L g).D} {n' : Cls → Nat} {pc : Nat} {f : Fault}
    (hσK : Frame.stateAt (thread p L) X g K = some (some (σ, n'))) (hub : n' .ub = 0) (hi : i < K)
    (he : X.get (g, i) = some ⟨pc, .ub f⟩) : False := by
  have hc := count hσK .ub
  rw [hub, List.countP_eq_zero] at hc
  have hmem : (⟨pc, .ub f⟩ : Event) ∈ (X.tr g).take K := by
    have : ((X.tr g).take K)[i]? = some ⟨pc, .ub f⟩ := by
      rw [List.getElem?_take, ite_eq_left hi]; exact he
    exact List.mem_of_getElem? this
  exact hc _ hmem (by simp [Proof.cls])

include hp hX hFw hw in
/-- The PV MMA of a PV site before a state. -/
theorem pv_of_site {K i : Nat} {e : Event} {σ : (glued p L g).D} {n' : Cls → Nat}
    (hσK : Frame.stateAt (thread p L) X g K = some (some (σ, n'))) (hub : n' .ub = 0) (hi : i < K)
    {d : D} {n : Cls → Nat} {b : Fin 4} {j : Fin 8}
    (hσ : Frame.stateAt (thread p L) X g i = some (some (minj p L g d n)))
    (he : X.get (g, i) = some e) (hs : d.site = .pv b j) :
    (∃ pc d s acc ms, e = ⟨pc, .tc (.mma d s acc ms)⟩) ∧ ∃ u, Tm.Pv L X g i (b.val % 2) u j := by
  have hev := (mfired hp hX he hσ).1
  simp only [Ev, hs] at hev
  obtain ⟨pc, kd⟩ := e
  rcases hev with ⟨a, s, acc, ms, rfl⟩ | ⟨f, rfl⟩
  · obtain ⟨d', m', hσ', hJ, -⟩ := win_state hp hX hFw hw he (.inl ⟨_, _, _, _, rfl⟩)
    have hEq := hσ.symm.trans hσ'
    simp only [minj, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq,
      true_and] at hEq
    obtain ⟨rfl, rfl⟩ := hEq
    exact ⟨⟨_, _, _, _, _, rfl⟩, (mma_at_site hp hX hw he hσ hJ).2 b j hs⟩
  · exact (no_ub hσK hub hi he).elim

theorem not_init {k : Nat} {d : D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n))) : k ≠ 0 := by
  rintro rfl
  rw [Frame.stateAt_zero] at hσ
  simp [thread, glued, Code.counted, Code.glue, Code.enter, exit, Startup.code, minj] at hσ

theorem pos_of {k : Nat} {d : D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n))) : ∃ i, k = i + 1 :=
  Nat.exists_eq_succ_of_ne_zero (not_init hσ)

include hX hp in
/-- The state before a state of `relSite`, with its event. -/
theorem rel_state {k : Nat} {d : D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (k + 1) = some (some (minj p L g d n)))
    (hl : k < (X.tr g).length) (hs : relSite d.site = true) :
    ∃ e d0 n0, X.get (g, k) = some e ∧
      Frame.stateAt (thread p L) X g k = some (some (minj p L g d0 n0)) ∧
      RelOf L g d0 e d.site ∧ Ev p L g d0 e := by
  have he : (X.tr g)[k]? = some ((X.tr g)[k]) := List.getElem?_eq_getElem hl
  obtain ⟨d0, n0, h0, h1⟩ := mma_pred he hσ (by rintro rfl; simp [relSite, code] at hs)
  exact ⟨_, d0, n0, he, h0, rel_pred h1 hs, (mfired hp hX he h0).1⟩

include hp hX hFw hw

/-- **The steps of a QK block before a step.** -/
theorem qk_chain {K : Nat} {σ : (glued p L g).D} {n' : Cls → Nat}
    (hσK : Frame.stateAt (thread p L) X g K = some (some (σ, n'))) (hub : n' .ub = 0)
    (hKl : K ≤ (X.tr g).length) {b : Fin 4} :
    ∀ (jv : Nat) (j : Fin 8), j.val = jv → ∀ i, i < K → ∀ d n,
      Frame.stateAt (thread p L) X g i = some (some (minj p L g d n)) → d.site = .qk b j →
      ∀ j' : Fin 8, j'.val ≤ jv → ∃ i' ≤ i, sc L X g i' = sc L X g i ∧
        ∃ u, Tm.Qk L X g i' (b.val % 2) u j' := by
  intro jv
  induction jv with
  | zero =>
    intro j hj i hi d n hσ hs j' hj'
    obtain rfl : j' = j := Fin.ext (by omega)
    obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e :=
      ⟨_, List.getElem?_eq_getElem (show i < (X.tr g).length by omega)⟩
    exact ⟨i, le_rfl, rfl, (qk_of_site hp hX hFw hw hσK hub hi hσ he hs).2⟩
  | succ jv ih =>
    intro j hj i hi d n hσ hs j' hj'
    by_cases hjj : j'.val = jv + 1
    · obtain rfl : j' = j := Fin.ext (by omega)
      obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e :=
        ⟨_, List.getElem?_eq_getElem (show i < (X.tr g).length by omega)⟩
      exact ⟨i, le_rfl, rfl, (qk_of_site hp hX hFw hw hσK hub hi hσ he hs).2⟩
    · obtain ⟨i0, rfl⟩ := pos_of hσ
      obtain ⟨e0, d0, n0, he0, hσ0, hprev, -⟩ := prev_state hp hX hσ (by omega) (by
        rw [hs]
        have : j ≠ 0 := fun h => by rw [h] at hj; exact absurd hj (by simp)
        simpa [prevSite] using this)
      rw [hs] at hprev
      obtain ⟨j2, hj2, hs0⟩ := hprev
      obtain ⟨⟨pc0, k0, rfl⟩, u0, h0⟩ :=
        qk_of_site hp hX hFw hw hσK hub (by omega) hσ0 he0 hs0
      obtain ⟨i', hi', hsc, hu⟩ := ih j2 (by omega) i0 (by omega) d0 n0 hσ0 hs0 j' (by omega)
      refine ⟨i', by omega, hsc.trans (sc_step he0 ?_).symm, hu⟩
      obtain ⟨_, _, _, e0'⟩ := h0.issue
      rw [he0] at e0'
      cases e0'
      rfl

/-- **The poll of a PV block**, from step 5 of the block on the elected lane. -/
theorem mw_chain {K : Nat} {σ : (glued p L g).D} {n' : Cls → Nat}
    (hσK : Frame.stateAt (thread p L) X g K = some (some (σ, n'))) (hub : n' .ub = 0)
    (hlost : n' (.mma .lost) = 0) (hKl : K ≤ (X.tr g).length) {b : Fin 4} {ld : Bool} :
    ∀ i, i < K → ∀ d n, Frame.stateAt (thread p L) X g i = some (some (minj p L g d n)) →
      d.site = .mw b ld → ld = true ∧ ∃ i0 d0 n0, i0 < i ∧
        Frame.stateAt (thread p L) X g i0 = some (some (minj p L g d0 n0)) ∧
        d0.site = .pv b 5 ∧ sc L X g i0 = sc L X g i := by
  intro i
  induction i with
  | zero => intro hi d n hσ; exact (not_init hσ rfl).elim
  | succ i ih =>
    intro hi d n hσ hs
    obtain ⟨e0, d0, n0, he0, hσ0, hprev, hev0⟩ := rel_state hp hX hσ (by omega)
      (by rw [hs]; rfl)
    rw [hs] at hprev
    rcases hprev with h | ⟨h, h5⟩ | ⟨-, mk, inst, l, hk, hne⟩
    · obtain ⟨hld, i1, d1, n1, hi1, hσ1, hs1, hsc⟩ := ih (by omega) d0 n0 hσ0 h
      refine ⟨hld, i1, d1, n1, by omega, hσ1, hs1, hsc.trans (sc_step he0 ?_).symm⟩
      obtain ⟨pc0, kd0⟩ := e0
      simp only [Ev, h] at hev0
      rcases hev0 with ⟨ok, hk⟩ | ⟨f, hk⟩ <;> (rw [hk]; rfl)
    · refine ⟨h, i, d0, n0, by omega, hσ0, h5, (sc_step he0 ?_).symm⟩
      obtain ⟨⟨_, _, _, _, _, rfl⟩, -⟩ := pv_of_site hp hX hFw hw hσK hub (by omega) hσ0 he0 h5
      rfl
    · obtain ⟨pc0, kd0⟩ := e0
      simp only at hk
      subst hk
      exact absurd (elect_won hX hσK hlost (by omega) he0) hne

/-- **The steps of a PV block before a step.** -/
theorem pv_chain {K : Nat} {σ : (glued p L g).D} {n' : Cls → Nat}
    (hσK : Frame.stateAt (thread p L) X g K = some (some (σ, n'))) (hub : n' .ub = 0)
    (hlost : n' (.mma .lost) = 0) (hKl : K ≤ (X.tr g).length) {b : Fin 4} :
    ∀ (jv : Nat) (j : Fin 8), j.val = jv → ∀ i, i < K → ∀ d n,
      Frame.stateAt (thread p L) X g i = some (some (minj p L g d n)) → d.site = .pv b j →
      ∀ j' : Fin 8, j'.val ≤ jv → ∃ i' ≤ i, sc L X g i' = sc L X g i ∧
        ∃ u, Tm.Pv L X g i' (b.val % 2) u j' := by
  intro jv
  induction jv with
  | zero =>
    intro j hj i hi d n hσ hs j' hj'
    obtain rfl : j' = j := Fin.ext (by omega)
    obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e :=
      ⟨_, List.getElem?_eq_getElem (show i < (X.tr g).length by omega)⟩
    exact ⟨i, le_rfl, rfl, (pv_of_site hp hX hFw hw hσK hub hi hσ he hs).2⟩
  | succ jv ih =>
    intro j hj i hi d n hσ hs j' hj'
    by_cases hjj : j'.val = jv + 1
    · obtain rfl : j' = j := Fin.ext (by omega)
      obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e :=
        ⟨_, List.getElem?_eq_getElem (show i < (X.tr g).length by omega)⟩
      exact ⟨i, le_rfl, rfl, (pv_of_site hp hX hFw hw hσK hub hi hσ he hs).2⟩
    · obtain ⟨i0, rfl⟩ := pos_of hσ
      obtain ⟨e0, d0, n0, he0, hσ0, hprev, hev0⟩ := rel_state hp hX hσ (by omega) (by
        rw [hs]
        have : j ≠ 0 := fun h => by rw [h] at hj; exact absurd hj (by simp)
        simpa [relSite] using this)
      rw [hs] at hprev
      rcases hprev with ⟨rfl, hmw⟩ | ⟨-, j2, hj2, hs0⟩
      · obtain ⟨-, i1, d1, n1, hi1, hσ1, hs1, hsc1⟩ :=
          mw_chain hp hX hFw hw hσK hub hlost hKl i0 (by omega) d0 n0 hσ0 hmw
        have h5 : ((5 : Fin 8) : Nat) = jv := by
          have h6 : ((6 : Fin 8) : Nat) = 6 := rfl
          have : ((5 : Fin 8) : Nat) = 5 := rfl
          omega
        obtain ⟨i', hi', hsc, hu⟩ := ih 5 h5 i1 (by omega) d1 n1 hσ1 hs1 j' (by omega)
        refine ⟨i', by omega, hsc.trans (hsc1.trans (sc_step he0 ?_).symm), hu⟩
        obtain ⟨pc0, kd0⟩ := e0
        simp only [Ev, hmw] at hev0
        rcases hev0 with ⟨ok, hk⟩ | ⟨f, hk⟩ <;> (rw [hk]; rfl)
      · obtain ⟨i', hi', hsc, hu⟩ := ih j2 (by omega) i0 (by omega) d0 n0 hσ0 hs0 j' (by omega)
        refine ⟨i', by omega, hsc.trans (sc_step he0 ?_).symm, hu⟩
        obtain ⟨⟨_, _, _, _, _, rfl⟩, -⟩ := pv_of_site hp hX hFw hw hσK hub (by omega) hσ0 he0 hs0
        rfl

/-- **The MMAs before a K/V release.** -/
theorem kv_block {k pc : Nat} {s : TcCommit.Spec}
    (he : X.get (g, k) = some ⟨pc, .tc (.commit s)⟩) {o : Fin 3}
    (hb : s.mbar = Tm.bar L (g / L.block) (56 + 8 * o.val)) :
    Tm.kvRels L X g k % 3 = o.val ∧
      ((X.tr g).take k).countP (commitsTo (Tm.bar L (g / L.block) (56 + 8 * o.val))) =
        Tm.kvRels L X g k / 3 ∧
      ∀ j : Fin 8, ∃ k' < k, ∃ u, Tm.Qk L X g k' 1 u j ∧ Tm.kvRels L X g k = 2 * u ∨
        Tm.Pv L X g k' 1 u j ∧ Tm.kvRels L X g k = 2 * u + 1 := by
  obtain ⟨d, n, hσ, ⟨r, w, hQ, -⟩, hws, hlost, hub, hev⟩ :=
    win_state hp hX hFw hw he (.inr ⟨_, rfl⟩)
  obtain ⟨c, hs, hcb⟩ := mma_commit_site hev rfl
  have ho := o.isLt
  have hmb : 56 + 8 * o.val = cmO r c := by
    have h1 := hcb.trans (cm_loc hp c (r := r) (fun hc' => hQ.regs (by
      rw [hs]; fin_cases c <;> simp_all [Site.ord])))
    rw [hb] at h1
    simp only [Tm.bar, bl, Loc.mk.injEq, true_and] at h1
    omega
  have hc4 : c = 2 ∨ c = 4 ∨ c = 6 ∨ c = 9 := by
    clear hs hcb
    fin_cases c <;> simp [cmO] at hmb ⊢ <;> omega
  have hwon := win_states hX k d n hσ hws
  obtain ⟨-, hcnt⟩ := counts_at hσ hQ hwon
  have hrel : Tm.kvRels L X g k = ringRel d.site.ord r := by
    unfold Tm.kvRels
    rw [hcnt, hcnt, hcnt, commitAt_kv]
  have hsc : sc L X g k = commitAt d.site.ord r 88 := hcnt 88
  have hcs : ((X.tr g).take k).countP (commitsTo (Tm.bar L (g / L.block) (56 + 8 * o.val))) =
      (ringRel d.site.ord r + 2 - o.val) / 3 := by
    rw [hcnt]
    obtain ⟨o, ho⟩ := o
    interval_cases o <;> simp [commitAt, ringCount]
  have hpre := hQ.pre
  have hKl : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  -- the election before the commit, and the site before it
  obtain ⟨i, rfl⟩ := pos_of hσ
  obtain ⟨e1, d1, n1, he1, hσ1, hpr1, hev1⟩ := prev_state hp hX hσ (by omega)
    (by rw [hs]; rfl)
  rw [hs] at hpr1
  have hs1 : d1.site = .ce c := hpr1
  have hsc1 : sc L X g (i + 1) = sc L X g i := by
    refine sc_step he1 ?_
    obtain ⟨pc1, kd1⟩ := e1
    simp only [Ev, hs1] at hev1
    rcases hev1 with ⟨inst, ld, -, rfl⟩ | ⟨f', rfl⟩
    · rfl
    · rfl
  obtain ⟨i, rfl⟩ := pos_of hσ1
  obtain ⟨e2, d2, n2, he2, hσ2, hpr2, hev2⟩ := rel_state hp hX hσ1 (by omega) (by
    rw [hs1]; rcases hc4 with rfl | rfl | rfl | rfl <;> rfl)
  rw [hs1] at hpr2
  have hlostF : ∀ {i' : Nat} {e' : Event}, i' < i + 1 + 1 → X.get (g, i') = some e' →
      ¬ LostEl L g e' := by
    rintro i' ⟨pc', kd'⟩ hi' he' ⟨mk, inst, ld, hk, hne⟩
    simp only at hk
    subst hk
    exact absurd (elect_won hX hσ hlost hi' he') hne
  -- a K release
  have hK : ∀ cs : Fin 12, (cs = 1 ∨ cs = 5) → d2.site = .cm cs →
      sc L X g (i + 1) = sc L X g i + 1 → ∀ j : Fin 8, ∃ k' < i + 1 + 1, ∃ u,
        Tm.Qk L X g k' 1 u j ∧ u + 1 = sc L X g (i + 1) := by
    intro cs hcsv hs2 hsc2 j
    obtain ⟨i, rfl⟩ := pos_of hσ2
    obtain ⟨e3, d3, n3, he3, hσ3, hpr3, hev3⟩ := prev_state hp hX hσ2 (by omega)
      (by rw [hs2]; rfl)
    rw [hs2] at hpr3
    have hs3 : d3.site = .ce cs := hpr3
    have hsc3 : sc L X g (i + 1) = sc L X g i := by
      refine sc_step he3 ?_
      obtain ⟨pc1, kd1⟩ := e3
      simp only [Ev, hs3] at hev3
      rcases hev3 with ⟨inst, ld, -, rfl⟩ | ⟨f', rfl⟩ <;> rfl
    obtain ⟨i, rfl⟩ := pos_of hσ3
    obtain ⟨e4, d4, n4, he4, hσ4, hpr4, -⟩ := prev_state hp hX hσ3 (by omega)
      (by rw [hs3]; rcases hcsv with rfl | rfl <;> rfl)
    rw [hs3] at hpr4
    obtain ⟨b', hb', hs4⟩ | ⟨h8, -⟩ | hl := hpr4
    rotate_left
    · rcases hcsv with rfl | rfl <;> exact absurd h8 (by decide)
    · exact (hlostF (by omega) he4 hl).elim
    have hb1 : b'.val % 2 = 1 := by
      rcases hcsv with rfl | rfl <;> revert hb' <;> clear hs4 <;> revert b' <;> decide
    obtain ⟨⟨pc5, k5, rfl⟩, u5, h5⟩ := qk_of_site hp hX hFw hw hσ hub (by omega) hσ4 he4 hs4
    have hsc4 : sc L X g (i + 1) = sc L X g i := by
      refine sc_step he4 ?_
      obtain ⟨_, _, _, e0'⟩ := h5.issue
      rw [he4] at e0'
      cases e0'
      rfl
    obtain ⟨i', hi', hsc5, u, hu⟩ := qk_chain hp hX hFw hw hσ hub hKl 7 7 rfl i (by omega) d4 n4
      hσ4 hs4 j (by omega)
    rw [hb1] at hu
    refine ⟨i', by omega, u, hu, ?_⟩
    have := hu.com
    change sc L X g i' = u at this
    omega
  -- a V release
  have hV : ∀ b : Fin 4, b.val % 2 = 1 → (d2.site = .pv b 7 ∨ d2.site = .mw b false) →
      ∀ j : Fin 8, ∃ k' < i + 1 + 1, ∃ u,
        Tm.Pv L X g k' 1 u j ∧ u + 1 = sc L X g (i + 1) := by
    rintro b hb1 (hs2 | hs2) j
    · obtain ⟨⟨_, _, _, _, _, rfl⟩, -⟩ := pv_of_site hp hX hFw hw hσ hub (by omega) hσ2 he2 hs2
      have hsc2 : sc L X g (i + 1) = sc L X g i := sc_step he2 rfl
      obtain ⟨i', hi', hsc5, u, hu⟩ := pv_chain hp hX hFw hw hσ hub hlost hKl 7 7 rfl i (by omega)
        d2 n2 hσ2 hs2 j (by omega)
      rw [hb1] at hu
      refine ⟨i', by omega, u, hu, ?_⟩
      have := hu.com
      change sc L X g i' = u + 1 at this
      omega
    · obtain ⟨h, -⟩ := mw_chain hp hX hFw hw hσ hub hlost hKl i (by omega) d2 n2 hσ2 hs2
      cases h
  have hcm2 : ∀ cs : Fin 12, (cs = 1 ∨ cs = 5) → d2.site = .cm cs →
      sc L X g (i + 1) = sc L X g i + 1 := by
    intro cs hcsv hs2
    obtain ⟨pc2, kd2⟩ := e2
    simp only [Ev, hs2] at hev2
    rcases hev2 with ⟨s', h, hb', -⟩ | ⟨f, h⟩
    swap
    · subst h; exact (no_ub hσ hub (by omega) he2).elim
    subst h
    have hloc := hb'.trans (cm_loc (r := 0) hp cs (v := d2.v) (by
      rcases hcsv with rfl | rfl <;> simp))
    have hs88 : s'.mbar = Tm.sFull L (g / L.block) 1 := by
      rw [hloc]
      rcases hcsv with rfl | rfl <;> rfl
    have he' : (X.tr g)[i]? = some _ := he2
    unfold sc Tm.sCommits
    rw [List.take_add_one, he', Option.toList_some, List.countP_append]
    simp [commitsTo, hs88]
  rw [hrel, hcs]
  rw [hs] at hpre hsc ⊢
  rcases hc4 with rfl | rfl | rfl | rfl
  · rcases hpr2 with hl | ⟨-, h⟩ | ⟨h, -⟩ | ⟨b, hb', -⟩
    · exact (hlostF (by omega) he2 hl).elim
    · have hr := hpre (by decide)
      subst hr
      have e1 : 56 + 8 * o.val = 56 := hmb
      have e2 : ringRel 16 0 = 0 := by decide
      have e3 : commitAt 16 0 88 = 1 := by decide
      have e4 : ringRel (Site.cm 2).ord 0 = 0 := e2
      change _ = commitAt 16 0 88 at hsc
      change ringRel 16 0 % 3 = _ ∧ (ringRel 16 0 + 2 - _) / 3 = ringRel 16 0 / 3 ∧ _
      rw [e2]
      refine ⟨by omega, by omega, fun j => ?_⟩
      obtain ⟨k', hk', u, hu, hsu⟩ := hK 1 (.inl rfl) h (hcm2 1 (.inl rfl) h) j
      exact ⟨k', hk', u, .inl ⟨hu, by omega⟩⟩
    · exact absurd h (by decide)
    · exact absurd hb' (by revert b; decide)
  · rcases hpr2 with hl | ⟨h, -⟩ | ⟨h, -⟩ | ⟨b, hb', hs2⟩
    · exact (hlostF (by omega) he2 hl).elim
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · have e1 : 56 + 8 * o.val = 56 + 8 * ((2 * r + 1) % 3) := hmb
      have e2 : ringRel 43 r = 2 * r + 1 := by simp [ringRel, pq]; omega
      have e3 : commitAt 43 r 88 = r + 1 := by simp [commitAt, pq]; omega
      have e4 : ringRel (Site.cm 4).ord r = 2 * r + 1 := e2
      change _ = commitAt 43 r 88 at hsc
      change ringRel 43 r % 3 = _ ∧ (ringRel 43 r + 2 - _) / 3 = ringRel 43 r / 3 ∧ _
      rw [e2]
      refine ⟨by omega, by omega, fun j => ?_⟩
      have hb1 : b.val % 2 = 1 := by clear hs2; revert b; decide
      obtain ⟨k', hk', u, hu, hsu⟩ := hV b hb1 hs2 j
      exact ⟨k', hk', u, .inr ⟨hu, by omega⟩⟩
  · rcases hpr2 with hl | ⟨h, -⟩ | ⟨-, h⟩ | ⟨b, hb', -⟩
    · exact (hlostF (by omega) he2 hl).elim
    · exact absurd h (by decide)
    · have e1 : 56 + 8 * o.val = 56 + 8 * ((2 * r + 2) % 3) := hmb
      have e2 : ringRel 49 r = 2 * r + 2 := by simp [ringRel, pq]; omega
      have e3 : commitAt 49 r 88 = r + 2 := by simp [commitAt, pq]; omega
      have e4 : ringRel (Site.cm 6).ord r = 2 * r + 2 := e2
      change _ = commitAt 49 r 88 at hsc
      change ringRel 49 r % 3 = _ ∧ (ringRel 49 r + 2 - _) / 3 = ringRel 49 r / 3 ∧ _
      rw [e2]
      refine ⟨by omega, by omega, fun j => ?_⟩
      obtain ⟨k', hk', u, hu, hsu⟩ := hK 5 (.inr rfl) h (hcm2 5 (.inr rfl) h) j
      exact ⟨k', hk', u, .inl ⟨hu, by omega⟩⟩
    · exact absurd hb' (by revert b; decide)
  · rcases hpr2 with hl | ⟨h, -⟩ | ⟨h, -⟩ | ⟨b, hb', hs2⟩
    · exact (hlostF (by omega) he2 hl).elim
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · have e1 : 56 + 8 * o.val = 56 + 8 * ((2 * r + 1) % 3) := hmb
      have e2 : ringRel 81 r = 2 * r + 1 := by simp [ringRel, pq]; omega
      have e3 : commitAt 81 r 88 = r + 1 := by simp [commitAt, pq]; omega
      have e4 : ringRel (Site.cm 9).ord r = 2 * r + 1 := e2
      change _ = commitAt 81 r 88 at hsc
      change ringRel 81 r % 3 = _ ∧ (ringRel 81 r + 2 - _) / 3 = ringRel 81 r / 3 ∧ _
      rw [e2]
      refine ⟨by omega, by omega, fun j => ?_⟩
      have hb1 : b.val % 2 = 1 := by clear hs2; revert b; decide
      obtain ⟨k', hk', u, hu, hsu⟩ := hV b hb1 hs2 j
      exact ⟨k', hk', u, .inr ⟨hu, by omega⟩⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
