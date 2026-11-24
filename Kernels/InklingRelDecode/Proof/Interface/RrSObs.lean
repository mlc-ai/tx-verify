-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.RrArrive
public import Kernels.InklingRelDecode.Proof.Protocol.IpLifeCommit
public import Kernels.InklingRelDecode.Proof.Result.RdSLoad

@[expose] public section

/-!
# Every `s_ready` commit of an exited CTA is observed (`Life.SObserved`)

The QK commit of block `i` is the lane's `(i / 2)`-th commit to `s_ready (i % 2)`
(`Rd.qk_commit_block`) and the loop bound of the MMA warp is the split's `num_iters`, so
`i < num_iters`. Thread 0 of the CTA, which exited, passes `bar21` of iteration `i`
(`Rr.sm_reaches_bar21`) having made `i / 2 + 1` successful polls of `s_ready (i % 2)`
(`Rd.sm_cnt`), so it has the poll with `i / 2` earlier ones (`MbarRing.Poll.nth_spec`); that poll
observes the commit with `i / 2` earlier commits (`SO.s_observes`), which is this commit.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Rr
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady)

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`Life.SObserved`.** -/
theorem sObserved_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hB : Mma.MmaBcast L X) (hbw : BaseWordRead L X)
    (hnw : NumWordRead Q L X)
    (hR : RoleReads L X) (G : SrPkg L kernel asms mem0 X) : Life.SObserved L X := by
  intro g k pc sp r m b he htg hb hm hx
  subst hm
  have hg : g < L.threads := event_thread_lt hX he
  have hcl : g / L.block < L.grid := cta_lt hX ⟨_, he⟩
  have H := G.ctx (g / L.block) hcl
  have hcommit : SO.CommitBar L (g / L.block) (sReady L (g / L.block) b) :=
    SO.CommitBar.sReady hb
  obtain ⟨hgcm, hspm⟩ := H.facts.commit_only he htg hcommit
  have hspb : sp.mbar = sReady L (g / L.block) b := hspm
  -- the lane's state at the commit
  have hk : k < (X.tr g).length := len_of_get he
  obtain ⟨d, P, hσ, hsh⟩ :=
    mma_event_state hpre hX hf.sound hf.tracked hg he (Or.inr ⟨sp, rfl⟩)
  have hsite : d.site = .qkCommit := Rd.site_of_scommit hb hsh hspb
  have hlead := lead_of_qkCommit hpre hX hf hk hσ hsite
  obtain ⟨d', P', hσ', -, hi2, hdi⟩ := Rd.qk_commit_block hpre hX hf hR hlead hB hg hb he hspb
  have hdd : d' = d := by
    have := Option.some.inj (Option.some.inj (hσ'.symm.trans hσ))
    simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
    exact this.1
  subst hdd
  have hI := mma_inv_at hX hf hk hσ
  have hlt : d'.i < d'.n := (hI.qk (by rw [hsite]; trivial)).1
  have hn : d'.n = Q.numIters (reqOf L g) (splitOf L g) :=
    mma_iters_loop hpre hX hf hbw hnw (m := (g, k)) ⟨P, hσ⟩ (Or.inl (by rw [hsite]; trivial))
  -- thread 0 of the CTA passed `bar21` of the iteration
  obtain ⟨g0, hg0, hg0c, hlead0, hcz, hcx⟩ := thread0 hpre hg
  have hdef0 : g0 % L.block < 128 := by omega
  have hex0 := hx g0 hg0 hg0c
  obtain ⟨k', ds, hσ0, hs0, hi0, hk0⟩ := sm_reaches_bar21 hpre hX hf hg0 hex0 hdef0
    (i0 := d'.i) (by rw [hcz, hcx]; exact hn ▸ hlt)
  have hb2 : (d'.i % 2) < 2 := Nat.mod_lt _ (by omega)
  have hcnt := ((Rd.sm_cnt hpre hX hf hg0 k' hk0.le _ hσ0).2 ds rfl).s b hb
  have hsp : SO.smPolled ds = ds.i + 1 := by simp [SO.smPolled, hs0]
  rw [hsp, hi0, hg0c] at hcnt
  have hbi : b = d'.i % 2 := hi2.symm
  have hr' : ((X.tr g).take k).countP (commitsTo (sReady L (g / L.block) b)) = d'.i / 2 := by
    unfold SO.blockB at hdi
    omega
  have hpoll : d'.i / 2 < okPolls (sReady L (g / L.block) b) (X.tr g0) := by
    have h1 : okPolls (sReady L (g / L.block) b) ((X.tr g0).take k') ≤
        okPolls (sReady L (g / L.block) b) (X.tr g0) :=
      (List.take_sublist _ _).countP_le
    have h2 : SO.below2 b (d'.i + 1) = d'.i / 2 + 1 := by
      unfold SO.below2
      omega
    omega
  obtain ⟨pcw, p, acq, sc, hw, hq⟩ := MbarRing.Poll.nth_spec (m := sReady L (g / L.block) b)
    (g := g0) hpoll
  have hsoft : G.Soft (g / L.block) g0 := ⟨hg0, hg0c, hdef0⟩
  obtain ⟨i', pc', sp', rank, hget', hmb', htg', hcnt', hrank, hobs⟩ :=
    SO.s_observes H.cons H.facts hb (Mbar.sReach H hb hsoft) hw hq
  -- the commit the poll observes is this commit
  have hii : i' = k := by
    have hgg : G.cm (g / L.block) = g := hgcm.symm
    rw [hgg] at hget' hcnt' hrank hobs
    exact nthEv_unique (p := commitsTo (sReady L (g / L.block) b)) hget'
      (by simp [commitsTo, hmb']) he (by simp [commitsTo, hspb]) (by rw [hcnt', hr'])
  have hgg : G.cm (g / L.block) = g := hgcm.symm
  rw [hgg] at hget' hrank hobs
  subst hii
  have hsp' : sp' = sp := by
    have := hget'.symm.trans he
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at this
    exact this.2
  subst hsp'
  have hrr : rank = r := by
    obtain ⟨l, rfl⟩ := Life.commit_spec_of hpre hX hf he
    obtain ⟨h1, -⟩ := Life.target_commitSpec htg'
    obtain ⟨h2, -⟩ := Life.target_commitSpec htg
    exact Fin.ext (h1.trans h2.symm)
  subst hrr
  exact ⟨g0, _, acq, sc, hg0, hg0c, hrank, hobs⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Rr
