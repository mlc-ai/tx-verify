-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SxAll
public import Kernels.InklingRelDecode.Proof.Protocol.SxBase
public import Kernels.InklingRelDecode.Proof.Protocol.SxUCopy
public import Kernels.InklingRelDecode.Proof.Result.MmaPremises

@[expose] public section

/-!
# The use of a copy and of an MMA read of block `i`, and the order of two copies by their uses

* `copy_use_block`: a copy of block `i` (`Result.Mma.CopyBlock`) completes on `kv_ready (i % 3)`
  and is of the slot's use `i / 3` (the loader's: `Ring.loader_copy_exec`, as in
  `Lp.copy_use_lt`; the prologue's: use 0, block `i < 3`);
* `read_use_block`: an MMA of block `i` (`Result.Mma.MmaBlock`) has `i / 3` earlier commits to
  `kv_empty (i % 3)` (`Ring.Cover.lane_counts`, `Ring.Mm.done`);
* `copies_lt`: a copy of a lower use than another copy of one byte of a slot is before it
  (`Ring.Kv.copies_chain` with `Ring.Cover.kv_cover`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sx
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- `kv_ready` names its CTA and its slot. -/
theorem kvReady_inj {c c' t t' : Nat} (h : kvReady L c t = kvReady L c' t') :
    c = c' ∧ t = t' := by
  simp only [kvReady, EvW.barLoc, EvW.kvReadyOff, Loc.mk.injEq] at h
  omega

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- **The slot and the use of a copy of block `i`.** -/
theorem copy_use_block (hR : RoleReads L X) (hp : NumPreRead Q L X) {c t : Nat} (ht : t < 3)
    {pArr : EvId} {pCp : Fin 8 → EvId} (hP : Lp.PreSlot Q L X c t pArr pCp) (cm : Nat)
    {k pc a i : Nat} {sp : TensorCopy.Spec} (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩)
    (hm : sp.mbar = kvReady L c t) (hb : Result.Mma.CopyBlock Q L X (g, k) i) :
    t = i % 3 ∧ Ring.Kv.copyUse X (Lp.slotOf Q L X c t cm pArr pCp) (g, k) = i / 3 := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := len_of_get he
  obtain ⟨-, hgc, hcase⟩ := Lp.copy_kvReady hpre hX hf he hm
  rcases hb with ⟨d, P, hσ, hdi⟩ | ⟨d, j, hσ, hj, hs, hji⟩
  · rcases hcase with ⟨d', hσ'⟩ | ⟨d', P', hσ', hcp⟩
    · rw [hσ] at hσ'; cases hσ'
    rw [hσ] at hσ'
    simp only [Option.some.injEq, TSt.w.injEq, WComp.WSt.loader.injEq] at hσ'
    obtain ⟨rfl, rfl⟩ := hσ'
    have hnot : ¬ ∃ i : Fin 8, (g, k) = pCp i := by
      rintro ⟨i, hi⟩
      have h1 := (hP.cp_thr i).2
      rw [← hi] at h1
      have := Lp.loader_warp hf.roleWarp hk.le hσ
      simp only at h1
      omega
    have hnpre : ¬ Lp.PreSite d.site := by
      intro h; rcases h with h | h | h <;> rw [h] at hcp <;> cases hcp
    obtain ⟨hw, k0, d0, hk0, h0, hd, hs0, hi0, hin, -, hPl, hC⟩ :=
      Lp.loader_anchor hpre hX hf hR hp hk hσ hnpre
    have hlead := electLead_of_elected hX (Lp.copy_lead hX k hk hσ hcp)
    have hm' : sp.mbar = kvReady L (g / L.block) t := by rw [hgc]; exact hm
    obtain ⟨-, hs3, -, -, -, hblk, -⟩ := Ring.loader_copy_exec hpre hw hg hX hk0 h0 hd
      (hf.ldRng hg hσ) hin hs0
      (by rw [hi0]; exact Lp.numPre_le _ _ _) ht (hlead.take k) (hC _) (hPl _) he hm'
    have hnpe : Lp.npOf Q L c = ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x) := by
      rw [← hgc]; rfl
    have hu : Ring.Kv.copyUse X (Lp.slotOf Q L X c t cm pArr pCp) (g, k) =
        ((X.tr g).take k).countP (issuesTo (kvReady L c t)) / 8 +
          (if t < Lp.npOf Q L c then 1 else 0) := by
      have hcond : ¬ ((Lp.slotOf Q L X c t cm pArr pCp).δ = 1 ∧
          ∃ i, (g, k) = (Lp.slotOf Q L X c t cm pArr pCp).pCp i) := fun h => hnot h.2
      unfold Ring.Kv.copyUse
      simp only [hcond, ↓reduceIte]
      rfl
    rw [hu, hnpe]
    rw [hgc, hi0] at hblk
    unfold Ring.loaderBlock Ring.loaderUse Ring.blockOf at hblk
    subst hdi
    split at hblk <;> split <;> omega
  · rcases hcase with ⟨d', hσ'⟩ | ⟨d', P', hσ', hcp⟩
    · rw [hσ] at hσ'
      simp only [Option.some.injEq, TSt.d.injEq, DComp.St.pro.injEq] at hσ'
      subst hσ'
      obtain ⟨⟨i', hi'⟩, hnp⟩ := hP.cp he hm hσ
      have hu : Ring.Kv.copyUse X (Lp.slotOf Q L X c t cm pArr pCp) (g, k) = 0 := by
        have hcond : (Lp.slotOf Q L X c t cm pArr pCp).δ = 1 ∧
            ∃ i, (g, k) = (Lp.slotOf Q L X c t cm pArr pCp).pCp i :=
          ⟨by simp [Lp.slotOf, hnp], i', hi'⟩
        unfold Ring.Kv.copyUse
        simp only [hcond, and_self, ↓reduceIte]
      rcases copy_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨a, sp, rfl⟩ with
        ⟨d2, hσ2, j2, hj2, hs2, a', s', hev, -, -, h3, -⟩ | ⟨d2, P2, hσ2, -⟩
      · rw [hσ] at hσ2
        simp only [Option.some.injEq, TSt.d.injEq, DComp.St.pro.injEq] at hσ2
        subst hσ2
        have hjj : j2 = j := Lp.ptcSite_inj j2 hj2 j hj (hs2.symm.trans hs)
        subst hjj
        simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
        obtain ⟨-, -, rfl⟩ := hev
        rw [hm] at h3
        obtain ⟨-, hjs⟩ := Lp.kvReady_loc_eq h3.symm
        refine ⟨by omega, by rw [hu]; omega⟩
      · rw [hσ] at hσ2; cases hσ2
    · rw [hσ] at hσ'; cases hσ'

/-- **The commits of an MMA of block `i` to its slot's `kv_empty`**: `i / 3`. -/
theorem read_use_block (hR : RoleReads L X) (hMB : Mma.MmaBcast L X) {k i : Nat} {d : Mma.D}
    {P : Loader.Pro} (hk : k < (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.mma d P))))
    (hb : Result.Mma.MmaBlock d i) :
    ((X.tr g).take k).countP (commitsTo (kvEmpty L (g / L.block) (i % 3))) = i / 3 := by
  have hlead : ElectLead L g (X.tr g) := by
    rcases hb with ⟨j, hs, -⟩ | ⟨j, hs, -⟩
    · exact lead_of_qk hX j.val rfl hk hσ hs
    · exact lead_of_pv hX j.val rfl hk hσ hs
  obtain ⟨-, hc⟩ := Ring.Cover.lane_counts hpre hX hf hR hlead
    (bcast_of_mma hf.roleWarp hMB (Frame.lt_of_get hX (List.getElem?_eq_getElem hk)) hk.le hσ)
    hk hσ (s := i % 3)
    (Nat.mod_lt _ (by omega))
  rw [hc]
  unfold Ring.below
  rcases hb with ⟨j, hs, hi⟩ | ⟨j, hs, hi⟩ <;> simp only [Ring.Mm.done, hs] <;> omega

/-- **Two copies of one byte of a slot, of a lower and a higher use, are ordered.** -/
theorem copies_lt (hR : RoleReads L X) (hp : NumPreRead Q L X) (G : Sr.SrPkg L kernel asms mem0 X)
    (hMB : Mma.MmaBcast L X) {c t : Nat} (hc : c < L.grid) (ht : t < 3) {pArr : EvId}
    {pCp : Fin 8 → EvId} (hP : Lp.PreSlot Q L X c t pArr pCp) {i1 i2 : EvId} {x y z x' y' z' : Nat}
    {l : Loc} (hw1 : AsyncCovers X i1 (.write (.load x y z)) l)
    (hw2 : AsyncCovers X i2 (.write (.load x' y' z')) l)
    (hm1 : ∀ pc a sp, X.get i1 = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = kvReady L c t)
    (hm2 : ∀ pc a sp, X.get i2 = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = kvReady L c t)
    (hlt : Ring.Kv.copyUse X (Lp.slotOf Q L X c t (G.cm c) pArr pCp) i1 <
      Ring.Kv.copyUse X (Lp.slotOf Q L X c t (G.cm c) pArr pCp) i2) :
    modelCausality L X l (.async i1 (.write (.load x y z)))
      (.async i2 (.write (.load x' y' z'))) := by
  obtain ⟨pc1, a1, sp1, he1, hl1⟩ := copy_write_at hw1
  obtain ⟨pc2, a2, sp2, he2, hl2⟩ := copy_write_at hw2
  have hm1' := hm1 _ _ _ he1
  have hm2' := hm2 _ _ _ he2
  obtain ⟨g1, k1⟩ := i1
  obtain ⟨g2, k2⟩ := i2
  obtain ⟨t1, ht1, v1, s1, h1, hv1, hs1, hh1, hmt1, hb1⟩ := copy_box hpre hX hf he1
  obtain ⟨t2, ht2, v2, s2, h2, hv2, hs2, hh2, hmt2, hb2⟩ := copy_box hpre hX hf he2
  obtain ⟨hsp, c1, lo1, hi1⟩ := hb1 x y z l hl1
  obtain ⟨-, c2, -, -⟩ := hb2 x' y' z' l hl2
  obtain ⟨hcc, htt⟩ := kvReady_inj (hm1'.symm.trans hmt1)
  subst htt
  have hg1 : g1 < L.threads := Frame.lt_of_get hX he1
  have hg2 : g2 < L.threads := Frame.lt_of_get hX he2
  have H := Lp.slot_hyp hpre hX hf hR hp G hc ht hP
  have hreg := box_region hv1 hs1 hh1 lo1 hi1
  refine ⟨.inl ⟨hg1, hg2, c1.symm.trans c2⟩, ?_⟩
  refine Ring.Kv.copies_chain hX H he1 hm1' he2 hm2' hlt hw1 hw2 ?_
  intro jc pc sp hjc hmb' hcnt
  have hm' : sp.mbar = kvEmpty L c t := hmb'
  obtain ⟨kR, idx, -, hT, hcR, hpol, hcv, hpres⟩ :=
    Ring.Cover.kv_cover hpre hX hf hR hMB ht hjc hm' ⟨hsp, c1.trans hcc.symm, hreg⟩
  refine ⟨kR, true, idx, hT, ?_, ?_, hcv, hpres⟩
  · unfold Ring.Kv.readUse
    exact hcR.trans hcnt
  · have : ((X.tr (G.cm c)).take jc).countP (commitsTo (kvEmpty L c t)) + 1 ≤
        okPolls (kvReady L c t) ((X.tr (G.cm c)).take kR) := hpol
    rw [← hcnt]
    exact this

end
end PTX.Kernels.InklingRelDecode.Proof.Sx
