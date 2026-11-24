-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WmLag

@[expose] public section

/-!
# The MMA warp's `kv_ready` poll: the blocker clause for the blocks after the preloaded ones

`Wk.MmaKvPollsRest` is the blocker clause of a lane of the MMA warp at its poll of
`kv_ready (i % 3)`. For a block `i ≥ num_pre` it is proved (`mmaKvPollsRest_of`): by
`Wm.mma_kv_blocked` lane 0 of the loader has not arrived for block `i` (it lags the lane,
`ap_lag`), or the loader's copying lane has not issued all copies of block `i` (it lags the lane
when it led and elected, `cp_lag`; else a lane of the loader warp with no election lags it,
`exists_noElect`, `noElect_lag`), or a tensor copy's notification is undelivered (an open
`.tensor` obligation). For a block `i < num_pre` the producers are the prologue's thread 0 and
the elected lanes of warps 0 and 1; that case is the premise `MmaKvPreRest`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wm
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)
open PTX.Kernels.InklingRelDecode.Proof.Lp (ldThread)
open PTX.Kernels.InklingRelDecode.Proof.Wk (np)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0}

/-- **The blocker clause of the MMA warp's `kv_ready` poll for a preloaded block** (`i <
num_pre`, whose producers are the prologue's). -/
def MmaKvPreRest (T : Nat → TSt → Nat) (Q : Params) (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ X g (d : Mma.D) (P : Loader.Pro) m par before, Maximal L kernel asms mem0 X →
    Frame.Pending L X g → Step.Released L X g →
    St Q L X g (X.tr g).length = some (some (.w (.mma d P))) → d.site = .kvWait →
    d.i < np Q L g → PollAt L g (.w (.mma d P)) m par →
    MBarrier.stateBefore (X.objects m) (X.objects m).length = some before →
    before.phase % 2 = par % 2 → Sched.Blk (timed T Q L) X g

/-- **`Wk.MmaKvPollsRest`** from the premise for the preloaded blocks. -/
theorem mmaKvPollsRest_of (hpre : Pre Q L mem0)
    (hF : ∀ X, Consistent L kernel asms mem0 X → ThreadFacts Q L mem0 X)
    (hR : ∀ X, Consistent L kernel asms mem0 X → RoleReads L X)
    (hB : ∀ X, Consistent L kernel asms mem0 X → BaseWordRead L X)
    (hN : ∀ X, Consistent L kernel asms mem0 X → NumWordRead Q L X)
    (hNP : ∀ X, Consistent L kernel asms mem0 X → NumPreRead Q L X)
    (hub : ∀ X, Consistent L kernel asms mem0 X → ¬ HasUb X)
    (hP : ∀ X, Consistent L kernel asms mem0 X →
      ∃ P : Sr.SrPkg L kernel asms mem0 X, ∀ c, P.cm c = Hs.cmOf L X c)
    (hpr : MmaKvPreRest Wt.time Q L mem0) : Wk.MmaKvPollsRest Wt.time Q L mem0 := by
  intro X g d P m par before hmax hp hrel hσ hw hat hst hpar
  by_cases hi : d.i < np Q L g
  · exact hpr X g d P m par before hmax hp hrel hσ hw hi hat hst hpar
  push Not at hi
  have hX := hmax.1
  have hf := hF X hX
  have hg := hp.1
  have hb : L.block = 256 := hpre.block
  have hgrid : g / L.block < L.grid := by
    unfold Launch.threads at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  rcases hat with ⟨-, rfl, rfl⟩ | ⟨hs', -⟩
  swap
  · rw [hw] at hs'; cases hs'
  set c := g / L.block with hcdef
  have hs3 : d.i % 3 < 3 := Nat.mod_lt _ (by omega)
  obtain ⟨G, hcm⟩ := hP X hX
  obtain ⟨pArr, pCp, hPS⟩ := Lp.preRing_of hpre hX hf c hgrid (d.i % 3) hs3
  have H := Lp.slot_hyp hpre hX hf (hR X hX) (hNP X hX) G hgrid hs3 hPS
  set S := Lp.slotOf Q L X c (d.i % 3) (G.cm c) pArr pCp with hS
  -- the committing lane is in the poller's warp
  have hcmM : Hs.MmaOf L c (Hs.cmOf L X c) := Hs.cm_mma hpre hgrid
  have h7 := roleWarp_inv hf.roleWarp _ _ le_rfl hσ
  simp only [RoleWarp, roleWarp] at h7
  have hcw : SameWarp L S.cm g := by
    show SameWarp L (G.cm c) g
    rw [hcm]
    obtain ⟨h1, h2, h3⟩ := hcmM
    exact ⟨⟨h1, hg, h2⟩, by rw [h3]; omega⟩
  have hnpc : Lp.npOf Q L c = np Q L g := Lp.npOf_eq Q L g
  have hnp3 : np Q L g ≤ 3 := Lp.numPre_le _ _ _
  have hδ : S.δ = Ring.below (d.i % 3) (np Q L g) := by
    show (if d.i % 3 < Lp.npOf Q L c then 1 else 0) = _
    rw [hnpc, Ring.below_small hs3 hnp3]
  have hδq : S.δ = 1 → 1 ≤ d.i / 3 := by
    intro h1
    rw [hδ, Ring.below_small hs3 hnp3] at h1
    split at h1 <;> omega
  have hpar' : before.phase % 2 = d.i / 3 % 2 := by omega
  rcases Wm.mma_kv_blocked hpre hX hf (hR X hX) H hσ hw rfl rfl hcw hδq hst hpar' with
    ha | hcp | ht
  · -- lane 0 of the loader has not arrived
    rw [hδ] at ha
    obtain ⟨hal, -, -⟩ := Lp.ldThread_props hb hgrid
    exact Wy.blk_of_lags hX hσ hal
      (ap_lag hpre hX hf (hR X hX) (hNP X hX) (hub X hX) (hB X hX) (hN X hX) hg hσ hw ha)
  · -- the copying lane has not issued every copy
    rw [hδ] at hcp
    by_cases hlead : ∃ h', SameWarp L (ldThread L c) h' ∧ ElectLead L h' (X.tr h') ∧
        ∃ ld, Elected (X.tr h') ld
    · obtain ⟨h', hsw, hl, ld, he⟩ := hlead
      have hcpe : Lp.cpThread L X c = h' := Lp.cpThread_eq hX hsw hl he
      obtain ⟨hal, hac, ha192⟩ := Lp.ldThread_props hb hgrid
      have hyc : h' / L.block = c := by rw [← hsw.1.2.2, hac]
      have hyw : h' % L.block / 32 = 6 := by rw [← hsw.2, ha192]
      have hcp' : (X.tr h').countP (issuesTo (kvReady L c (d.i % 3))) +
          8 * Ring.below (d.i % 3) (np Q L g) < 8 * (d.i / 3 + 1) := by
        have : S.cp = h' := hcpe
        rw [← this]
        exact hcp
      exact Wy.blk_of_lags hX hσ hsw.1.2.1
        (cp_lag hpre hX hf (hR X hX) (hNP X hX) (hub X hX) (hB X hX) (hN X hX) hg hσ hw
          hsw.1.2.1 hyc hyw hl hcp')
    · obtain ⟨y, hyl, hyc, hyw, hel⟩ := exists_noElect hpre hX hgrid hlead
      exact Wy.blk_of_lags hX hσ hyl
        (noElect_lag hpre hX hf (hR X hX) (hNP X hX) (hub X hX) (hB X hX) (hN X hX) hg hσ hw hi
          hyl hyc hyw hel)
  · exact .inl ⟨.tensor, .inr (.inr (.inl rfl)), ht⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wm
