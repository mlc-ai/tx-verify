-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Lib.TmemRegion
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Before
import Kernels.TmlFa4Fwd.Proof.Mma.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Mma.Ref
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The Q stages' commits

The commit to the second Q stage's empty barrier follows the one to the first's, at pc 2537, with no
commit between, and the poll of the first stage's full barrier (`q_commits`); the lane that made it
has polled each full barrier at its exit. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A Q commit is its lane's only one on its barrier**, after a K/V release. -/
theorem q_commit_one (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 12) {k pc : Nat} {s : TcCommit.Spec}
    (st : Fin 2) (he : X.get (g, k) = some ⟨pc, .tc (.commit s)⟩)
    (hb : s.mbar = obj L g (8 * st.val + 16)) :
    ((X.tr g).take k).countP (commitsTo (obj L g (8 * st.val + 16))) = 0 ∧
      1 ≤ ((X.tr g).take k).countP (commitsTo (obj L g 56)) := by
  obtain ⟨d, n, hσ, ⟨r, w, hQ, hcm⟩, hws, hlost, hub, hev⟩ :=
    win_state hp hX hFw hw he (.inr ⟨_, rfl⟩)
  obtain ⟨c, hs, hcb⟩ := mma_commit_site hev rfl
  have hmb : 8 * st.val + 16 = cmO r c := by
    have h1 := hcb.trans (cm_loc hp c (r := r) (fun hc' => hQ.regs (by
      rw [hs]; fin_cases c <;> simp_all [Site.ord])))
    rw [hb] at h1
    exact obj_inj h1
  have hc : c.val = 7 + st.val := by
    clear hs hcb
    fin_cases st <;> fin_cases c <;> simp [cmO] at hmb ⊢ <;> omega
  have hw1 : w = true := hcm (by rw [hs]; clear hmb hs hcb hc; revert c; decide)
  subst hw1
  have hcom : ∀ o, ((X.tr g).take k).countP (commitsTo (obj L g o)) =
      commitAt d.site.ord r o := by
    intro o
    have h := hQ.com o
    simp only [↓reduceIte] at h
    rw [← h]
    show _ = n (.mma (.commit (bl L g o)))
    rw [← count hσ]
    rfl
  rw [hcom, hcom, hs]
  fin_cases st <;> simp only at hc
  · obtain rfl : c = 7 := Fin.ext hc
    simp [Site.ord, commitAt, pq, ringRel, ringCount]
    omega
  · obtain rfl : c = 8 := Fin.ext hc
    simp [Site.ord, commitAt, pq, ringRel, ringCount]
    omega

/-- **The second Q commit**: the lane's commit two events before it is the first stage's, the event
between is an election, and the lane has polled the first stage's full barrier. -/
theorem q_commits (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 12) {k pc : Nat} {s : TcCommit.Spec}
    (he : X.get (g, k) = some ⟨pc, .tc (.commit s)⟩) (hb : s.mbar = obj L g 24) :
    1 ≤ okPolls (obj L g 0) ((X.tr g).take k) ∧
      ∃ i s', k = i + 2 ∧ X.get (g, i) = some ⟨2537, .tc (.commit s')⟩ ∧ s'.mbar = obj L g 16 ∧
        ∀ j, i < j → j < k → ¬ ∃ s, X.Commit (g, j) s := by
  obtain ⟨d, n, hσ, ⟨r, w, hQ, -⟩, hws, hlost, hub, hev⟩ :=
    win_state hp hX hFw hw he (.inr ⟨_, rfl⟩)
  have hnub : ∀ {i pc f}, i < k → X.get (g, i) ≠ some ⟨pc, .ub f⟩ := by
    intro i pc f hi hg
    have hc := count hσ .ub
    rw [hub, List.countP_eq_zero] at hc
    have hmem : (⟨pc, .ub f⟩ : Event) ∈ (X.tr g).take k := by
      have : ((X.tr g).take k)[i]? = some ⟨pc, .ub f⟩ := by
        rw [List.getElem?_take, ite_eq_left hi]; exact hg
      exact List.mem_of_getElem? this
    exact hc _ hmem (by simp [Proof.cls])
  obtain ⟨c, hs, hcb⟩ := mma_commit_site hev rfl
  have hmb : 24 = cmO r c := by
    have h1 := hcb.trans (cm_loc hp c (r := r) (fun hc' => hQ.regs (by
      rw [hs]; fin_cases c <;> simp_all [Site.ord])))
    rw [hb] at h1
    exact obj_inj h1
  obtain rfl : c = 8 := by
    clear hs hcb
    fin_cases c <;> simp [cmO] at hmb ⊢ <;> omega
  have hpoll : 1 ≤ okPolls (obj L g 0) ((X.tr g).take k) := by
    have ha := hQ.acq 0
    rw [show okPolls (obj L g 0) ((X.tr g).take k) = n (.mma (.acquire (bl L g 0))) by
      rw [← count hσ]; rfl]
    change n _ = _ at ha
    rw [ha, hs]
    simp [Site.ord, acqAt, pq]
  refine ⟨hpoll, ?_⟩
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
  have hs1 : d1.site = .ce 8 := hpr1
  have hp1 : prevSite d1.site = true := by rw [hs1]; rfl
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (hnz hp1 hσ1)
  obtain ⟨e2, d2, n2, he2, hσ2, hpr2, hev2⟩ := prev_state hp hX hσ1 (by omega) hp1
  rw [hs1] at hpr2
  have hs2 : d2.site = .cm 7 := by
    rcases hpr2 with ⟨b, hb', -⟩ | ⟨-, h⟩ | ⟨mk, inst, ld, hk2, hne⟩
    · have : ∀ b : Fin 4, qkDone b ≠ .ce 8 := by decide
      exact absurd hb' (this b)
    · exact h
    · obtain ⟨pc2, kd2⟩ := e2
      simp only at hk2
      subst hk2
      exact absurd (elect_won hX hσ hlost (by omega) he2) hne
  have hev2' := hev2
  simp only [Ev, hs2] at hev2'
  obtain ⟨pc2, kd2⟩ := e2
  rcases hev2' with ⟨s', rfl, hb', -⟩ | ⟨f, rfl⟩
  swap
  · exact absurd he2 (hnub (by omega))
  have hpc2 : pc2 = 2537 := by
    obtain ⟨t, ins, o, -, -, -, hf⟩ :=
      Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he2 hσ2 (by intro f h; cases h)
    have h1 : pc2 = (code p L g (ent p L)).pc d2 := Flow.fires_pc hf
    rw [h1]
    show d2.site.pc = 2537
    rw [hs2]
    rfl
  subst hpc2
  refine ⟨i, s', rfl, he2, ?_, ?_⟩
  · rw [hb']
    exact (cm_loc hp (v := d2.v) 7 (r := 0) (fun h => by simp at h)).trans rfl
  · rintro j h1 h2 ⟨s'', pc'', hc''⟩
    obtain rfl : j = i + 1 := by omega
    rw [show X.get (g, i + 1) = some e1 from he1] at hc''
    cases hc''
    simp only [Ev, hs1] at hev1
    rcases hev1 with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> cases hk

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
