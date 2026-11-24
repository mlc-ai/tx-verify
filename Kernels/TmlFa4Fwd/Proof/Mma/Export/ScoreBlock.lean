-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.RelBlock
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Mma.Counts
import Kernels.TmlFa4Fwd.Proof.Mma.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Mma.Poll
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The QK block before an S-full commit, and the first S-full commit of a stage

An S-full commit of stage `st` follows the eight QK MMAs of its tile (`s_block`). A commit to an O
barrier follows an S-full commit of each stage and as many K/V releases as ring uses
(`o_commit_counts`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : Prologue.warpIndex L g = 12)
include hp hX hFw hw

/-- **The QK MMAs before an S-full commit.** -/
theorem s_block {k pc st : Nat} {s : TcCommit.Spec} (hst : st < 2)
    (he : X.get (g, k) = some ⟨pc, .tc (.commit s)⟩)
    (hb : s.mbar = Tm.bar L (g / L.block) (80 + 8 * st)) :
    ∀ j : Fin 8, ∃ k' < k, ∃ u, Tm.Qk L X g k' st u j := by
  obtain ⟨d, n, hσ, ⟨r, w, hQ, -⟩, hws, hlost, hub, hev⟩ :=
    win_state hp hX hFw hw he (.inr ⟨_, rfl⟩)
  obtain ⟨c, hs, hcb⟩ := mma_commit_site hev rfl
  have hmb : 80 + 8 * st = cmO r c := by
    have h1 := hcb.trans (cm_loc hp c (r := r) (fun hc' => hQ.regs (by
      rw [hs]; fin_cases c <;> simp_all [Site.ord])))
    rw [hb] at h1
    simp only [Tm.bar, bl, Loc.mk.injEq, true_and] at h1
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
  have hKl : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨i, rfl⟩ := pos_of hσ
  obtain ⟨e1, d1, n1, he1, hσ1, hpr1, -⟩ := prev_state hp hX hσ (by omega) (by rw [hs]; rfl)
  rw [hs] at hpr1
  have hs1 : d1.site = .ce c := hpr1
  obtain ⟨i, rfl⟩ := pos_of hσ1
  obtain ⟨e2, d2, n2, he2, hσ2, hpr2, -⟩ := prev_state hp hX hσ1 (by omega) (by
    rw [hs1, ← hce]
    have : ∀ b, prevSite (qkDone b) = true := by decide
    exact this b)
  rw [hs1] at hpr2
  obtain ⟨b', hb', hs2⟩ | ⟨h8, -⟩ | ⟨mk, inst, ld, hk2, hne⟩ := hpr2
  rotate_left
  · subst h8
    have h8 : ∀ b, qkDone b ≠ .ce 8 := by decide
    exact absurd hce (h8 b)
  · obtain ⟨pc2, kd2⟩ := e2
    simp only at hk2
    subst hk2
    exact absurd (elect_won hX hσ hlost (by omega) he2) hne
  have hbb : b' = b := by
    have : ∀ b b' : Fin 4, qkDone b' = qkDone b → b' = b := by decide
    exact this _ _ (hb'.trans hce.symm)
  subst hbb
  intro j
  obtain ⟨i', hi', -, u, hu⟩ := qk_chain hp hX hFw hw hσ hub hKl 7 7 rfl i (by omega) d2 n2 hσ2
    hs2 j (by omega)
  exact ⟨i', by omega, u, by rw [← hbst]; exact hu⟩

/-- **The counts at a commit to a final O barrier**: an S-full commit of each stage, and every ring
use acquired is released. -/
theorem o_commit_counts {k pc st : Nat} {s : TcCommit.Spec} (hst : st < 2)
    (he : X.get (g, k) = some ⟨pc, .tc (.commit s)⟩)
    (hb : s.mbar = Tm.bar L (g / L.block) (144 + 8 * st)) :
    (∀ st' < 2, 1 ≤ ((X.tr g).take k).countP
      (commitsTo (Tm.bar L (g / L.block) (80 + 8 * st')))) ∧
    Tm.kvRels L X g k = Tm.kvPolls L X g k ∧
    ∀ o : Fin 3, ((X.tr g).take k).countP (commitsTo (Tm.bar L (g / L.block) (56 + 8 * o.val))) =
      (Tm.kvRels L X g k + 2 - o.val) / 3 := by
  obtain ⟨d, n, hσ, ⟨r, w, hQ, -⟩, hws, hlost, hub, hev⟩ :=
    win_state hp hX hFw hw he (.inr ⟨_, rfl⟩)
  obtain ⟨c, hs, hcb⟩ := mma_commit_site hev rfl
  have hmb : 144 + 8 * st = cmO r c := by
    have h1 := hcb.trans (cm_loc hp c (r := r) (fun hc' => hQ.regs (by
      rw [hs]; fin_cases c <;> simp_all [Site.ord])))
    rw [hb] at h1
    simp only [Tm.bar, bl, Loc.mk.injEq, true_and] at h1
    omega
  have hc2 : c = 10 ∨ c = 11 := by
    clear hs hcb
    interval_cases st <;> fin_cases c <;> simp [cmO] at hmb ⊢ <;> omega
  have hwon := win_states hX k d n hσ hws
  obtain ⟨hacq, hcnt⟩ := counts_at hσ hQ hwon
  have hrel : Tm.kvRels L X g k = ringRel d.site.ord r := by
    unfold Tm.kvRels
    rw [hcnt, hcnt, hcnt, commitAt_kv]
  have hpol : Tm.kvPolls L X g k = ringAcq d.site.ord r := by
    unfold Tm.kvPolls
    rw [hacq, hacq, hacq, acqAt_kv]
  have hcs : ∀ o : Fin 3, ((X.tr g).take k).countP
      (commitsTo (Tm.bar L (g / L.block) (56 + 8 * o.val))) =
        (ringRel d.site.ord r + 2 - o.val) / 3 := by
    intro o
    rw [hcnt]
    obtain ⟨o, ho⟩ := o
    interval_cases o <;> simp [commitAt, ringCount]
  rw [hrel, hpol]
  refine ⟨fun st' hst' => ?_, ?_, hcs⟩
  · rw [hcnt, hs]
    rcases hc2 with rfl | rfl <;> interval_cases st' <;> simp [commitAt, pq, Site.ord]
  · rw [hs]
    rcases hc2 with rfl | rfl <;> simp [ringRel, ringAcq, pq, Site.ord]

/-- **The ring uses released at a commit to a final O barrier** are twice the tile's blocks. -/
theorem o_commit_uses {k pc st : Nat} {s : TcCommit.Spec} (hst : st < 2)
    (he : X.get (g, k) = some ⟨pc, .tc (.commit s)⟩)
    (hb : s.mbar = Tm.bar L (g / L.block) (144 + 8 * st)) :
    ∃ R, MmaRounds p L g R ∧ Tm.kvRels L X g k = 2 * R + 2 := by
  rcases mma_counts hp hX hFw hw he (fun f h => by cases h) with ⟨s', n, hS, hev, hx⟩ | hev |
    ⟨d, n, r, w, hσ, hQ, hcm, hF, hev⟩
  · exfalso
    obtain ⟨site, x1, x2, x3⟩ := s'
    cases site
    case enter r => simp [exit] at hx
    case sh j => fin_cases j <;> simp [Startup.Ev] at hev
    all_goals simp [Startup.Ev] at hev
  · rcases hev with ⟨_, _, _, hk'⟩ | ⟨_, _, _, hk'⟩ | ⟨_, _, hk'⟩ | ⟨_, hk'⟩ <;> cases hk'
  obtain ⟨c, hs, hcb⟩ := mma_commit_site hev rfl
  have hmb : 144 + 8 * st = cmO r c := by
    have h1 := hcb.trans (cm_loc hp c (r := r) (fun hc' => hQ.regs (by
      rw [hs]; fin_cases c <;> simp_all [Site.ord])))
    rw [hb] at h1
    simp only [Tm.bar, bl, Loc.mk.injEq, true_and] at h1
    omega
  have hc2 : c = 10 ∨ c = 11 := by
    clear hs hcb
    interval_cases st <;> fin_cases c <;> simp [cmO] at hmb ⊢ <;> omega
  have hwon := win_states hX k d n hσ (by rw [hs]; rfl)
  obtain ⟨-, hcnt⟩ := counts_at hσ hQ hwon
  have hrel : Tm.kvRels L X g k = ringRel d.site.ord r := by
    unfold Tm.kvRels
    rw [hcnt, hcnt, hcnt, commitAt_kv]
  obtain ⟨R, bal, hC, hB⟩ := bs_ref (pmid_of (by rw [hs]; rfl)) hF
  have hB' : Bs p L g d.v = Bs p L g (mmaRef p L g R bal) := hB
  have ht := hQ.tail (by rw [hs]; rcases hc2 with rfl | rfl <;> decide)
  refine ⟨_, ⟨R, bal, hC.1, rfl⟩, ?_⟩
  rw [← hB', hrel, hs]
  have hr : ringRel (Site.cm c).ord r = 2 * r + 2 := by
    rcases hc2 with rfl | rfl <;> simp [ringRel, pq, Site.ord] <;> omega
  rw [hr]
  omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
