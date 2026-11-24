-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Tmem
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

/-! # The QK MMAs before an MMA or a commit

A QK MMA of step `j ≠ 0` directly follows the tile's step `j - 1` (`qk_prev`); an S-full commit with
`u` earlier ones follows step 7 of tile `u` and an election (`qk_before_commit`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A machine that has stopped stays so. -/
theorem dead_mono {i : Nat} (h : Frame.stateAt (thread p L) X g i = some none) :
    ∀ K, i ≤ K → Frame.stateAt (thread p L) X g K = some none := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => exact h
  | succ K hK ih =>
    rcases hk : (X.tr g)[K]? with _ | e
    · have hle : (X.tr g).length ≤ K := by
        by_contra hc; rw [List.getElem?_eq_getElem (by omega)] at hk; cases hk
      rw [Frame.stateAt_of_le (by omega), ← Frame.stateAt_of_le hle]
      exact ih
    · rw [Frame.stateAt_succ hk, ih]
      rfl

/-- **A state of the role before a later state is followed by a state of the role.** -/
theorem mma_fwd {i K : Nat} {d : D} {n : Cls → Nat} {e : Event} {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g i = some (some (minj p L g d n)))
    (he : X.get (g, i) = some e) (hK : i < K)
    (hσK : Frame.stateAt (thread p L) X g K = some (some σ)) :
    ∃ d', succ p L g d e = some (some d') ∧ Frame.stateAt (thread p L) X g (i + 1) =
      some (some (minj p L g d' (Code.bump (Proof.cls L g) n e))) := by
  have hs := Frame.stateAt_succ (C := thread p L) (show (X.tr g)[i]? = some e from he)
  rw [hσ] at hs
  have hn : Frame.stateAt (thread p L) X g (i + 1) = (thread p L g).next (minj p L g d n) e := hs
  rw [next_minj] at hn
  change _ = (succ p L g d e).map _ at hn
  rcases hd : succ p L g d e with _ | _ | d' <;> rw [hd] at hn
  · rw [Frame.stateAt_none_mono (by simpa using hn) (show i + 1 ≤ K by omega)] at hσK
    cases hσK
  · exfalso
    rw [dead_mono (by simpa using hn) K (by omega)] at hσK
    cases hσK
  · exact ⟨d', rfl, by simpa using hn⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : Prologue.warpIndex L g = 12)
include hp hX hFw hw

/-- The state of an MMA or a commit: the lane has lost no election. -/
theorem win_state {K pc : Nat} {k : TcKind} (he : X.get (g, K) = some ⟨pc, .tc k⟩)
    (hk : (∃ d s acc mask, k = .mma d s acc mask) ∨ ∃ s, k = .commit s) :
    ∃ d n, Frame.stateAt (thread p L) X g K = some (some (minj p L g d n)) ∧
      RefCounts p L g (d, rc n) ∧ winSite d.site = true ∧ n (.mma .lost) = 0 ∧ n .ub = 0 ∧
      Ev p L g d ⟨pc, .tc k⟩ := by
  rcases mma_counts hp hX hFw hw he (fun f h => by cases h) with ⟨s', n, hS, hev, hx⟩ | hev |
    ⟨d, n, r, w, hσ, hQ, hcm, hF, hev⟩
  · exfalso
    obtain ⟨site, x1, x2, x3⟩ := s'
    cases site
    case enter r => simp [exit] at hx
    case sh j => fin_cases j <;> simp [Startup.Ev] at hev
    all_goals simp [Startup.Ev] at hev
  · rcases hev with ⟨_, _, _, hk'⟩ | ⟨_, _, _, hk'⟩ | ⟨_, _, hk'⟩ | ⟨_, hk'⟩
    all_goals first
      | (cases hk'; done)
      | (cases hk'
         rcases hk with ⟨_, _, _, _, h⟩ | ⟨_, h⟩ <;> cases h)
  · have hws : winSite d.site = true := by
      rcases hk with ⟨a, s, acc, mask, rfl⟩ | ⟨s, rfl⟩
      · rcases mma_site hev with ⟨b, j, h⟩ | ⟨b, j, h⟩ <;> rw [h] <;> rfl
      · obtain ⟨c, h⟩ := commit_site hev
        rw [h]; rfl
    refine ⟨d, n, hσ, ⟨r, w, hQ, hcm⟩, hws, ?_, ub_zero hX he hσ, hev⟩
    have hwon := win_states hX K d n hσ hws
    have h1 := hQ.won
    have h2 := hQ.lost
    cases w
    · simp only [Bool.false_eq_true, ite_false] at h1
      change n (.mma .won) = 0 at h1
      omega
    · exact h2

omit hp hFw hw in
/-- An election of a lane before such a state is won. -/
theorem elect_won {K i pc mk inst ld : Nat} {σ : (glued p L g).D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g K = some (some (σ, n))) (h0 : n (.mma .lost) = 0)
    (hi : i < K) (he : X.get (g, i) = some ⟨pc, .elect mk inst ld⟩) : laneOf L g = ld := by
  have hc := count hσ (.mma .lost)
  rw [h0, List.countP_eq_zero] at hc
  have hmem : (⟨pc, .elect mk inst ld⟩ : Event) ∈ (X.tr g).take K := by
    have : ((X.tr g).take K)[i]? = some ⟨pc, .elect mk inst ld⟩ := by
      rw [List.getElem?_take, ite_eq_left hi]; exact he
    exact List.mem_of_getElem? this
  have hm := elect_full hX (show X.Elect (g, i) pc mk inst ld from he)
  by_contra hne
  exact hc _ hmem (by simp [Proof.cls, Mma.cls, hm]; exact fun h => hne h.symm)

omit hFw hw in
/-- The state before a state of the pipeline, with its event. -/
theorem prev_state {k : Nat} {d : D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (k + 1) = some (some (minj p L g d n)))
    (hl : k < (X.tr g).length) (hs : prevSite d.site = true) :
    ∃ e d0 n0, X.get (g, k) = some e ∧
      Frame.stateAt (thread p L) X g k = some (some (minj p L g d0 n0)) ∧
      PrevOf L g d0 e d.site ∧ Ev p L g d0 e := by
  have he : (X.tr g)[k]? = some ((X.tr g)[k]) := List.getElem?_eq_getElem hl
  obtain ⟨d0, n0, h0, h1⟩ := mma_pred he hσ (by rintro rfl; simp [prevSite, code] at hs)
  exact ⟨_, d0, n0, he, h0, pred_site h1 hs, (mfired hp hX he h0).1⟩

omit hp hX hFw hw in
/-- A QK MMA is of one stage and one tile. -/
theorem qk_eq {k st u st' u' : Nat} {j j' : Fin 8} (h : Tm.Qk L X g k st u j)
    (h' : Tm.Qk L X g k st' u' j') : st = st' ∧ u = u' ∧ (j = 0 ↔ j' = 0) := by
  obtain ⟨_, _, _, e⟩ := h.issue
  obtain ⟨_, _, _, e'⟩ := h'.issue
  rw [e] at e'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at e'
  obtain ⟨-, h1, -, h2, -⟩ := e'
  obtain rfl : st = st' := by omega
  refine ⟨rfl, h.com.symm.trans h'.com, ?_⟩
  have h0 : ∀ i : Fin 8, i = 0 ↔ (i.val != 0) = false := by decide
  rw [h0 j, h0 j', h2]

omit hp hX hFw hw in
/-- A QK MMA is of one step. -/
theorem qk_step {k st u st' u' : Nat} {j j' : Fin 8} (h : Tm.Qk L X g k st u j)
    (h' : Tm.Qk L X g k st' u' j') : j = j' := by
  obtain ⟨rfl, rfl, -⟩ := qk_eq h h'
  obtain ⟨pc, _, _, e⟩ := h.issue
  have h1 := (h.descs ⟨pc, e⟩).1
  rw [(h'.descs ⟨pc, e⟩).1] at h1
  simp only [Tm.qkA, Tm.kDesc, TcShared.Descriptor.mk.injEq] at h1
  have hj := j.isLt
  have hj' := j'.isLt
  exact Fin.ext (by omega)

/-- The QK MMA of a QK site before a state. -/
theorem qk_of_site {K i : Nat} {e : Event} {σ : (glued p L g).D} {n' : Cls → Nat}
    (hσK : Frame.stateAt (thread p L) X g K = some (some (σ, n'))) (hub : n' .ub = 0) (hi : i < K)
    {d : D} {n : Cls → Nat} {b : Fin 4} {j : Fin 8}
    (hσ : Frame.stateAt (thread p L) X g i = some (some (minj p L g d n)))
    (he : X.get (g, i) = some e) (hs : d.site = .qk b j) :
    (∃ pc k, e = ⟨pc, .tc k⟩) ∧ ∃ u, Tm.Qk L X g i (b.val % 2) u j := by
  have hev := (mfired hp hX he hσ).1
  simp only [Ev, hs] at hev
  obtain ⟨pc, kd⟩ := e
  rcases hev with ⟨a, s, acc, ms, rfl⟩ | ⟨f, rfl⟩
  · obtain ⟨d', m', hσ', hJ, -⟩ := win_state hp hX hFw hw he (.inl ⟨_, _, _, _, rfl⟩)
    have hEq := hσ.symm.trans hσ'
    simp only [minj, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq,
      true_and] at hEq
    obtain ⟨rfl, rfl⟩ := hEq
    exact ⟨⟨_, _, rfl⟩, (mma_at_site hp hX hw he hσ hJ).1 b j hs⟩
  · exfalso
    have hc := count hσK .ub
    rw [hub, List.countP_eq_zero] at hc
    have hmem : (⟨pc, .ub f⟩ : Event) ∈ (X.tr g).take K := by
      have : ((X.tr g).take K)[i]? = some ⟨pc, .ub f⟩ := by
        rw [List.getElem?_take, ite_eq_left hi]; exact he
      exact List.mem_of_getElem? this
    exact hc _ hmem (by simp [Proof.cls])

/-- **A QK MMA's predecessor in its block.** -/
theorem qk_prev {k st u : Nat} {j : Fin 8} (hq : Tm.Qk L X g k st u j) (hj : j ≠ 0) :
    ∃ i, k = i + 1 ∧ ∃ j', j'.val + 1 = j.val ∧ Tm.Qk L X g i st u j' := by
  obtain ⟨pc, da, db, he⟩ := hq.issue
  obtain ⟨d, n, hσ, hJ, hws, hlost, hub, hev⟩ := win_state hp hX hFw hw he
    (.inl ⟨_, _, _, _, rfl⟩)
  obtain ⟨hqk, hpv⟩ := mma_at_site hp hX hw he hσ hJ
  obtain ⟨b, j1, hs⟩ : ∃ b j1, d.site = .qk b j1 := by
    rcases mma_site hev with h | ⟨b, j', h⟩
    · exact h
    · obtain ⟨u', h'⟩ := hpv b j' h
      obtain ⟨_, _, he'⟩ := h'.issue
      rw [he] at he'
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq,
        TcMma.OperandSpec.mk.injEq] at he'
      obtain ⟨-, -, ⟨-, -, -, -, -, ha, -⟩, -⟩ := he'
      exact absurd ha (by simp)
  obtain ⟨u1, h1⟩ := hqk b j1 hs
  obtain ⟨rfl, rfl, hj1⟩ := qk_eq hq h1
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Frame.stateAt_zero] at hσ
    simp [thread, glued, Code.counted, Code.glue, Code.enter, exit, Startup.code, minj] at hσ
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hl := (List.getElem?_eq_some_iff.mp (show (X.tr g)[i + 1]? = _ from he)).1
  obtain ⟨e0, d0, n0, he0, hσ0, hprev, -⟩ := prev_state hp hX hσ (by omega) (by
    rw [hs]; simpa [prevSite] using fun h => hj (hj1.mpr h))
  rw [hs] at hprev
  obtain ⟨j2, hj2, hs0⟩ := hprev
  obtain ⟨⟨pc0, k0, rfl⟩, u0, h0⟩ := qk_of_site hp hX hFw hw hσ hub (Nat.lt_succ_self i) hσ0 he0 hs0
  refine ⟨i, rfl, j2, by rw [qk_step hq h1, hj2], ?_⟩
  have hcom : Tm.sCommits L X g (b.val % 2) (i + 1) = Tm.sCommits L X g (b.val % 2) i := by
    obtain ⟨_, _, _, e0'⟩ := h0.issue
    rw [he0] at e0'
    cases e0'
    unfold Tm.sCommits
    have he' : (X.tr g)[i]? = _ := he0
    rw [List.take_add_one, he', Option.toList_some, List.countP_append]
    simp [commitsTo]
  have e1 := hq.com
  have e2 := h0.com
  rw [hcom, e2] at e1
  exact e1 ▸ h0

/-- **An S-full commit follows step 7 of its tile's QK block and an election.** -/
theorem qk_before_commit {k st : Nat} {s : TcCommit.Spec} (hst : st < 2)
    (hc : X.Commit (g, k) s) (hb : s.mbar = Tm.sFull L (g / L.block) st) :
    ∃ i, k = i + 2 ∧ Tm.Qk L X g i st (Tm.sCommits L X g st k) 7 ∧
      (∃ pc mk inst ld, X.get (g, i + 1) = some ⟨pc, .elect mk inst ld⟩) ∧
      Tm.pPolls L X g st k = Tm.sCommits L X g st k := by
  obtain ⟨pc, he⟩ := hc
  obtain ⟨d, n, hσ, ⟨r, w, hQ, -⟩, hws, hlost, hub, hev⟩ :=
    win_state hp hX hFw hw he (.inr ⟨_, rfl⟩)
  obtain ⟨c, hs, hcb⟩ := mma_commit_site hev rfl
  have hmb : 80 + 8 * st = cmO r c := by
    have h1 := hcb.trans (cm_loc hp c (r := r) (fun hc' => hQ.regs (by
      rw [hs]; fin_cases c <;> simp_all [Site.ord])))
    rw [hb] at h1
    simp only [Tm.sFull, Tm.bar, bl, Loc.mk.injEq, true_and] at h1
    omega
  obtain ⟨b, hce, hbst⟩ : ∃ b, qkDone b = .ce c ∧ b.val % 2 = st := by
    have : (c = 0 ∧ st = 0) ∨ (c = 1 ∧ st = 1) ∨ (c = 3 ∧ st = 0) ∨ (c = 5 ∧ st = 1) := by
      clear hs hcb
      interval_cases st <;> fin_cases c <;> simp [cmO] at hmb ⊢ <;> omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, rfl, rfl⟩
    · exact ⟨1, rfl, rfl⟩
    · exact ⟨2, rfl, rfl⟩
    · exact ⟨3, rfl, rfl⟩
  have hnz : ∀ {k : Nat} {d : D} {n : Cls → Nat}, prevSite d.site = true →
      Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)) → k ≠ 0 := by
    rintro k d n hs hσ rfl
    rw [Frame.stateAt_zero] at hσ
    simp [thread, glued, Code.counted, Code.glue, Code.enter, exit, Startup.code, minj] at hσ
  have hp0 : prevSite d.site = true := by rw [hs]; rfl
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (hnz hp0 hσ)
  have hl := (List.getElem?_eq_some_iff.mp (show (X.tr g)[i + 1]? = _ from he)).1
  obtain ⟨e1, d1, n1, he1, hσ1, hpr1, hev1⟩ := prev_state hp hX hσ (by omega) hp0
  rw [hs] at hpr1
  have hs1 : d1.site = .ce c := hpr1
  have hp1 : prevSite d1.site = true := by
    rw [hs1, ← hce]
    have : ∀ b, prevSite (qkDone b) = true := by decide
    exact this b
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (hnz hp1 hσ1)
  obtain ⟨e2, d2, n2, he2, hσ2, hpr2, -⟩ := prev_state hp hX hσ1 (by omega) hp1
  rw [hs1] at hpr2
  obtain ⟨⟨b', hb', hs2⟩⟩ | ⟨rfl, -⟩ | ⟨mk, inst, ld, hk2, hne⟩ := hpr2
  rotate_left
  · exfalso
    have : ∀ b : Fin 4, qkDone b ≠ .ce 8 := by decide
    exact this b hce
  · obtain ⟨pc2, kd2⟩ := e2
    simp only at hk2
    subst hk2
    exact absurd (elect_won hX hσ hlost (by omega) he2) hne
  obtain rfl : b' = b := by
    have : ∀ b b' : Fin 4, qkDone b' = qkDone b → b' = b := by decide
    exact this _ _ (hb'.trans hce.symm)
  obtain ⟨⟨pc2, k2, rfl⟩, u, h0⟩ := qk_of_site hp hX hFw hw hσ hub (by omega) hσ2 he2 hs2
  rw [hbst] at h0
  have hcnt : ∀ f : Event → Bool, (∀ d s acc ms, f ⟨pc2, .tc (.mma d s acc ms)⟩ = false) →
      (∀ pc m i l, f ⟨pc, .elect m i l⟩ = false) →
      ((X.tr g).take (i + 1 + 1)).countP f = ((X.tr g).take i).countP f := by
    intro f hf1 hf2
    have e1' : (X.tr g)[i + 1]? = some e1 := he1
    have e2' : (X.tr g)[i]? = some ⟨pc2, .tc k2⟩ := he2
    have h1f : f e1 = false := by
      obtain ⟨pc1, kd1⟩ := e1
      simp only [Ev, hs1] at hev1
      rcases hev1 with ⟨inst, ld, -, rfl⟩ | ⟨f', rfl⟩
      · exact hf2 _ _ _ _
      · exfalso
        have hcu := count hσ .ub
        rw [hub, List.countP_eq_zero] at hcu
        have hmem : (⟨pc1, .ub f'⟩ : Event) ∈ (X.tr g).take (i + 1 + 1) := by
          have : ((X.tr g).take (i + 1 + 1))[i + 1]? = some ⟨pc1, .ub f'⟩ := by
            rw [List.getElem?_take, ite_eq_left (by omega)]; exact he1
          exact List.mem_of_getElem? this
        exact hcu _ hmem (by simp [Proof.cls])
    have h2f : f ⟨pc2, .tc k2⟩ = false := by
      obtain ⟨_, _, _, e0'⟩ := h0.issue
      rw [he2] at e0'
      cases e0'
      exact hf1 _ _ _ _
    rw [List.take_add_one, e1', Option.toList_some, List.countP_append, List.take_add_one, e2',
      Option.toList_some, List.countP_append]
    simp [h1f, h2f]
  have hcs := hcnt (commitsTo (Tm.sFull L (g / L.block) st)) (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl)
  have hcp := hcnt (okPoll (Tm.pFull L (g / L.block) st)) (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl)
  have hu : Tm.sCommits L X g st (i + 1 + 1) = u := hcs.trans h0.com
  refine ⟨i, rfl, by rw [hu]; exact h0, ?_, by rw [hu]; exact hcp.trans h0.p⟩
  obtain ⟨pc1, kd1⟩ := e1
  simp only [Ev, hs1] at hev1
  rcases hev1 with ⟨inst, ld, -, rfl⟩ | ⟨f', rfl⟩
  · exact ⟨_, _, _, _, he1⟩
  · exfalso
    have hcu := count hσ .ub
    rw [hub, List.countP_eq_zero] at hcu
    have hmem : (⟨pc1, .ub f'⟩ : Event) ∈ (X.tr g).take (i + 1 + 1) := by
      have : ((X.tr g).take (i + 1 + 1))[i + 1]? = some ⟨pc1, .ub f'⟩ := by
        rw [List.getElem?_take, ite_eq_left (by omega)]; exact he1
      exact List.mem_of_getElem? this
    exact hcu _ hmem (by simp [Proof.cls])

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
