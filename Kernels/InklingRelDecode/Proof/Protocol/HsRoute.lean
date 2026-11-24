-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.HsParity
public import Kernels.InklingRelDecode.Proof.Interface.RrArrive

@[expose] public section

/-!
# The fields of `Mbar.Route` that the threads' counts give

* `arrive_polls`: thread 0's arrival on `p_ready b` at the site `arrive` of iteration `i` has
  `i / 2` earlier arrivals on the barrier (`Rr.arr_cnt`) and `i / 2 + 1` earlier successful polls
  of `s_ready b` (`Rd.sm_cnt`);
* `qk_polls`, `pv_polls`: the committing lane's commit to `s_ready b` (to `o_done`) is at the site
  `qkCommit` (`pvCommit2`) of an iteration whose `p_ready` polls `mma_cnt` counts;
* `ctx_of`: `Mbar.Ctx` of a launched CTA from the two fields that are not proved here
  (`soft_bar`, `lane_commit`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Hs
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal kvReady kvEmpty commitSpec)
open PTX.Kernels.InklingRelDecode.Proof.SO (below2)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem p0_div (hpre : Pre Q L mem0) (c : Nat) :
    p0Of L c / L.block = c ∧ p0Of L c % L.block = 0 := by
  have hb : L.block = 256 := hpre.block
  unfold p0Of
  rw [hb]
  omega

/-- **`Route.arrive_polls`.** -/
theorem arrive_polls (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {c i pc b : Nat} {sc : MbarScope} (hb : b < 2)
    (he : X.get (p0Of L c, i) = some ⟨pc, .arrive (pReady L c b) 0 1 true sc⟩) :
    arrivals (pReady L c b) ((X.tr (p0Of L c)).take i) + 1 ≤
      okPolls (sReady L c b) ((X.tr (p0Of L c)).take i) := by
  obtain ⟨hpc, hp0⟩ := p0_div hpre c
  have hg : p0Of L c < L.threads := event_thread_lt hX he
  have hk : i < (X.tr (p0Of L c)).length := len_of_get he
  rcases arrive_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨_, _, _, _, _, rfl⟩ with
    ⟨d, -, j, hj, -, hev⟩ | ⟨d, hσ, hs, -, hev⟩ | ⟨d, P, -, hs, hsh⟩
  · simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
    obtain ⟨-, h, -⟩ := hev
    hs_loc h
  · simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
    obtain ⟨-, h, -⟩ := hev
    have h' := h
    simp only [EvW.pReady, EvD.pReadyOf, EvD.Bar.loc, EvD.Bar.off, EvW.barLoc, EvW.pReadyOff,
      Loc.mk.injEq, true_and] at h'
    have hbi : d.i % 2 = b := by omega
    have ha := (Rr.arr_cnt hpre hX hf hg hp0 i hk.le _ hσ).2 d rfl b hb
    have hs' := ((Rd.sm_cnt hpre hX hf hg i hk.le _ hσ).2 d rfl).s b hb
    rw [hpc] at ha hs'
    rw [ha, hs']
    simp only [SO.smPolled, hs, below2]
    omega
  · unfold EvW.LdShape at hsh
    rw [hs] at hsh
    simp only [Event.mk.injEq, Kind.arrive.injEq] at hsh
    obtain ⟨-, h, -⟩ := hsh
    hs_loc h

/-- **`Route.qk_polls`.** -/
theorem qk_polls (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hB : Mma.MmaBcast L X) {c i pc b : Nat}
    {sp : TcCommit.Spec}
    (hb : b < 2) (he : X.get (cmOf L X c, i) = some ⟨pc, .tc (.commit sp)⟩)
    (hm : sp.mbar = sReady L c b) :
    ((X.tr (cmOf L X c)).take i).countP (commitsTo (sReady L c b)) ≤
      okPolls (pReady L c b) ((X.tr (cmOf L X c)).take i) := by
  have hg : cmOf L X c < L.threads := event_thread_lt hX he
  have hk : i < (X.tr (cmOf L X c)).length := len_of_get he
  obtain ⟨d, P, hσ, h⟩ := commit_state hpre hX hf he
  rcases h with ⟨hs, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
    simp only [commitSpec] at hm
  rotate_left 1
  all_goals try hs_loc hm
  have hm' := hm
  simp only [EvW.sReady, barLoc_eq, EvW.sReadyOff] at hm'
  obtain ⟨hc, hbi⟩ := hm'
  have hlead := electLead_take (lead_of_qkCommit hpre hX hf hk hσ hs) i
  obtain ⟨hP, hC⟩ := mma_cnt hpre hX hf hR hg hk hσ
  rw [hc] at hP hC
  rw [(hC hlead ((bcast_of_mma hf.roleWarp hB hg hk.le hσ).take i)).1 b hb, hP b hb]
  simp only [SO.Mm.qkDone, SO.Mm.pPolled, hs, below2]
  omega

/-- **`Route.pv_polls`.** -/
theorem pv_polls (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hB : Mma.MmaBcast L X) {c i pc : Nat}
    {sp : TcCommit.Spec}
    (he : X.get (cmOf L X c, i) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = oDone L c) :
    ∀ s, s ≤ ((X.tr (cmOf L X c)).take i).countP (commitsTo (oDone L c)) →
      s / 2 + 1 ≤ okPolls (pReady L c (s % 2)) ((X.tr (cmOf L X c)).take i) := by
  have hg : cmOf L X c < L.threads := event_thread_lt hX he
  have hk : i < (X.tr (cmOf L X c)).length := len_of_get he
  obtain ⟨d, P, hσ, h⟩ := commit_state hpre hX hf he
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨hs, rfl⟩ | ⟨-, rfl⟩ <;>
    simp only [commitSpec] at hm
  rotate_left 2
  all_goals try hs_loc hm
  have hm' := hm
  simp only [EvW.oDone, barLoc_eq, EvW.oDoneOff] at hm'
  obtain ⟨hc, -⟩ := hm'
  have hlead := electLead_take (exists_pv7_commit2 hpre hX hf hk hσ hs).1 i
  obtain ⟨hP, hC⟩ := mma_cnt hpre hX hf hR hg hk hσ
  rw [hc] at hP hC
  intro s hs'
  rw [(hC hlead ((bcast_of_mma hf.roleWarp hB hg hk.le hσ).take i)).2] at hs'
  have hs2 : s % 2 < 2 := Nat.mod_lt _ (by omega)
  rw [hP _ hs2]
  have h1 := ((mma_inv_at hX hf hk hσ).pv (by rw [hs]; trivial)).1
  simp only [SO.Mm.oDoneC, SO.Mm.pPolled, hs, below2] at hs' ⊢
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.Hs
