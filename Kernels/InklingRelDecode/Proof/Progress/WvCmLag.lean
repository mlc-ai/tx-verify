-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WvCm
public import Kernels.InklingRelDecode.Proof.Interface.WvAll

@[expose] public section

/-!
# `CmLag` proved

`cmLag_of` assembles `Wy.CmLag` for `Wt.time` from `WvCm.lean`: the committing lane is the
elected lane of the MMA warp (`lead_case`) or, when no lane of the warp has elected yet, lane 0
of the warp, which has made no election (`noElect_of`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Progress PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady oDone oFinal)
open PTX.Kernels.InklingRelDecode.Proof.SO (below2)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **With no elected lane, lane 0 of the MMA warp has made no election.** An election of it has
a partner of the leader's lane in its instance, which returned the leader, that is its own
lane. -/
theorem noElect_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) {c : Nat}
    (hc : c < L.grid) (hL : ¬ ∃ y, Hs.LeadOf L X c y) :
    ∀ j e mask inst ld, X.get (c * L.block + 224, j) = some e →
      e.kind ≠ .elect mask inst ld := by
  intro j e mask inst ld he hk
  have hb : L.block = 256 := hpre.block
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  have hy : (c * L.block + 224, j).1 < L.threads := Frame.lt_of_get hX he
  have hel : X.Elect (c * L.block + 224, j) pc mask inst ld := he
  obtain ⟨-, hmem, hld⟩ := hX.elect.1 _ _ _ _ _ hel
  have hld32 : ld < 32 := hld.1
  set h := c * L.block + 224 + ld with hh
  have hhl : h < L.threads := by
    unfold Launch.threads
    rw [hh, hb]
    have : (c + 1) * 256 ≤ L.grid * 256 := Nat.mul_le_mul_right _ hc
    rw [Nat.add_mul] at this
    omega
  have hsw : SameWarp L (c * L.block + 224) h := by
    refine ⟨⟨hy, hhl, ?_⟩, ?_⟩ <;> rw [hb, hh, hb] <;> omega
  have hmask : mask = 4294967295 :=
    electMask_full hX _ _ (List.mem_of_getElem? (show (X.tr _)[j]? = _ from he)) mask inst ld rfl
  have hlane : laneOf L h = ld := by
    unfold laneOf
    rw [hh, hb]
    omega
  have hm' : electMember mask (laneOf L h) := by rw [hlane]; exact hld
  obtain ⟨x, pc0, pc', mask0, mask', inst0, l0, l', hel0, hx⟩ := ElectOrd.partner hX hsw hel hm'
  have h0 : X.get (c * L.block + 224, j) = some ⟨pc0, .elect mask0 inst0 l0⟩ := hel0
  rw [he] at h0
  simp only [Option.some.injEq, Event.mk.injEq, Kind.elect.injEq] at h0
  obtain ⟨-, rfl, rfl, rfl⟩ := h0
  obtain ⟨-, hmm, hll, -⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ hel hx hsw
  apply hL
  refine ⟨h, ⟨hhl, ?_, ?_⟩, x, pc', inst, ?_⟩
  · rw [hh, hb]; omega
  · rw [hh, hb]; omega
  · have hx' : X.get (h, x) = some ⟨pc', .elect mask' inst l'⟩ := hx
    rw [hx', ← hmm, hmask, ← hll, hlane]

/-- An event of a thread without exit and without undefined behaviour does not end it. -/
theorem noEnds {y : Nat} (hub : ¬ HasUb X) (hnx : ∀ j pc, X.get (y, j) ≠ some ⟨pc, .exit⟩) :
    ∀ e ∈ X.tr y, ¬ Ends e := by
  intro e he hend
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  have hg : X.get (y, j) = some (X.tr y)[j] := List.getElem?_eq_getElem hj
  rcases hend with ⟨f, hf⟩ | hx
  · exact hub ⟨(y, j), (X.tr y)[j].pc, f, by rw [hg, ← hf]⟩
  · exact hnx j (X.tr y)[j].pc (by rw [hg, ← hx])

/-- **`Wy.CmLag`** for `Wt.time`. -/
theorem cmLag_of (hpre : Pre Q L mem0)
    (hF : ∀ X, Consistent L kernel asms mem0 X → ThreadFacts Q L mem0 X)
    (hR : ∀ X, Consistent L kernel asms mem0 X → RoleReads L X)
    (hB : ∀ X, Consistent L kernel asms mem0 X → BaseWordRead L X)
    (hN : ∀ X, Consistent L kernel asms mem0 X → NumWordRead Q L X)
    (hMB : ∀ X, Consistent L kernel asms mem0 X → Mma.MmaBcast L X) :
    Wy.CmLag Wt.time Q L mem0 := by
  intro X g s m par hX hub hg hσ hat hle
  have hf := hF X hX
  have hR' := hR X hX
  have hb : L.block = 256 := hpre.block
  have hgrid : g / L.block < L.grid := by
    unfold Launch.threads at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  have hph : (dPh s).2 = 2 := by
    cases s with
    | sm d => rcases hat with ⟨hs, -, -⟩ | ⟨hs, -, -⟩ <;> simp [dPh, hs]
    | epi d => obtain ⟨hs, -, -⟩ := hat; simp [dPh, hs]
    | _ => exact hat.elim
  obtain ⟨hnxg, hgb, hinvg⟩ := poller_end hpre hX hf hR' hub hg hσ hph
  obtain ⟨-, -, hz⟩ := ProA.cta_lt hpre hg
  have hN24 := Lp.numIters_le24 hpre hz (ProA.cta L g .x)
  -- the lane and what it gives about its MMA states
  have hcmM : Hs.MmaOf L (g / L.block) (Hs.cmOf L X (g / L.block)) := Hs.cm_mma hpre hgrid
  have hcta : ∀ a, ProA.cta L (Hs.cmOf L X (g / L.block)) a = ProA.cta L g a :=
    fun a => ProA.cta_eq_of_block hcmM.2.1 a
  have hnum : ∀ ky d P, St Q L X (Hs.cmOf L X (g / L.block)) ky =
      some (some (.w (.mma d P))) → d.site ≠ .setMaxReg → d.site ≠ .ldNum →
      d.n = Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
    intro ky d P hσy h1 h2
    have := ((words_inv hpre hX hf (hB X hX) (hN X hX) _ _ hσy).2.2 h1 h2).1
    rw [hcta, hcta] at this
    exact this
  have hnxy : ∀ j pc, X.get (Hs.cmOf L X (g / L.block), j) ≠ some ⟨pc, .exit⟩ :=
    noExit_peer hpre hX hf hR' hcmM.2.1.symm (by have := hcmM.2.2; omega) hnxg hgb
  -- the two kinds of committing lane
  have hkind : (ElectLead L (Hs.cmOf L X (g / L.block)) (X.tr (Hs.cmOf L X (g / L.block))) ∧
      ∀ ky d P, ky ≤ (X.tr (Hs.cmOf L X (g / L.block))).length →
        St Q L X (Hs.cmOf L X (g / L.block)) ky = some (some (.w (.mma d P))) →
        d.site ≠ .setMaxReg →
        (∀ b < 2, ((X.tr (Hs.cmOf L X (g / L.block))).take ky).countP
            (commitsTo (sReady L (g / L.block) b)) = below2 b (SO.Mm.qkDone d)) ∧
        ((X.tr (Hs.cmOf L X (g / L.block))).take ky).countP
            (commitsTo (oDone L (g / L.block))) = SO.Mm.oDoneC d ∧
        ((X.tr (Hs.cmOf L X (g / L.block))).take ky).countP
            (commitsTo (oFinal L (g / L.block))) = SO.Mm.finDone d) ∨
      (∀ ky d P, ky ≤ (X.tr (Hs.cmOf L X (g / L.block))).length →
        St Q L X (Hs.cmOf L X (g / L.block)) ky = some (some (.w (.mma d P))) → PreE d) := by
    by_cases hL : ∃ y, Hs.LeadOf L X (g / L.block) y
    · obtain ⟨y, hy⟩ := hL
      have hcm : Hs.cmOf L X (g / L.block) = y := Hs.cm_eq hX hy
      obtain ⟨⟨hyt, hyc, hy7⟩, mm, pc, inst, hel⟩ := hy
      have hlead : ElectLead L y (X.tr y) :=
        electLead_of_elected hX ⟨_, List.mem_of_getElem? (show (X.tr y)[mm]? = _ from hel),
          4294967295, inst, rfl⟩
      rw [hcm] at hnxy ⊢
      refine .inl ⟨hlead, fun ky d P hk hσy hs => ?_⟩
      have := Proof.Wv.mma_commits_le hpre hX hf hR' hk hσy hs hlead (hMB X hX y hyt hy7)
        (noEnds hub hnxy)
      rw [hyc] at this
      exact this
    · refine .inr fun ky d P hk hσy => ?_
      by_contra hne
      have hcM := Hs.cm_mma (X := X) hpre hgrid
      obtain ⟨j, e, mask, inst, ld, -, he, hk'⟩ :=
        elect_of hX hf (hMB X hX _ hcM.1 hcM.2.2) ky hk hσy hne
      have hcm : Hs.cmOf L X (g / L.block) = g / L.block * L.block + 224 := by
        unfold Hs.cmOf
        simp only [hL, dite_false]
      rw [hcm] at he
      exact noElect_of hpre hX hgrid hL j e mask inst ld he hk'
  have hsub : ∀ ky m, ((X.tr (Hs.cmOf L X (g / L.block))).take ky).countP (commitsTo m) ≤
      (X.tr (Hs.cmOf L X (g / L.block))).countP (commitsTo m) :=
    fun ky m => (List.take_sublist _ _).countP_le
  cases s with
  | sm d =>
    have hI : Sm.Inv L g d := hinvg.2
    have hcnt := (Rd.sm_cnt hpre hX hf hg _ le_rfl _ hσ).2 d rfl
    rcases hat with ⟨hs, rfl, rfl⟩ | ⟨hs, rfl, rfl⟩
    · -- `waitS`
      have hl : Sm.LateSite d.site := by rw [hs]; trivial
      have hlt := sm_iter_lt hpre hf hg hσ hI hl
      have hpol := hcnt.s (d.i % 2) (Nat.mod_lt _ (by omega))
      rw [List.take_length] at hpol
      have hsp : SO.smPolled d = d.i := by simp [SO.smPolled, hs]
      rw [hsp, SO.below2_of_buf (Nat.mod_lt _ (by omega)) rfl] at hpol
      have hT := (smT_band d hl).1
      refine lags_of hpre hX hf hR' hub (T0 := slot d.i + bandS) hT
        (by have := pre_lt_slot d.i; unfold bandS; wt_omega) hnxg hgb hcmM ?_
      intro ky d' P hk hσy hI'
      rcases hkind with ⟨hlead, hc⟩ | hpe
      · refine lt_waitS hI' hlt (by omega) (hnum ky d' P hσy) ?_ ?_
        · exact fun h1 h2 h3 => fin_iter_le hX hlead hk hσy h1 h2 h3
        · intro hs'
          have := (hc ky d' P hk hσy hs').1 (d.i % 2) (Nat.mod_lt _ (by omega))
          have := hsub ky (sReady L (g / L.block) (d.i % 2))
          omega
      · exact preE_lt_sm (hpe ky d' P hk hσy) (by omega) (by omega) (hnum ky d' P hσy)
          (fin0 hX ky hk hσy)
    · -- `waitO`
      have hl : Sm.LateSite d.site := by rw [hs]; trivial
      have hlt := sm_iter_lt hpre hf hg hσ hI hl
      have hi1 : 1 ≤ d.i := hcnt.ok hs
      have hpol := hcnt.o
      rw [List.take_length] at hpol
      have hsp : SO.smOPolled d = d.i - 1 := by simp [SO.smOPolled, hs]
      rw [hsp] at hpol
      have hT := (smT_band d hl).1
      refine lags_of hpre hX hf hR' hub (T0 := slot d.i + bandS) hT
        (by have := pre_lt_slot d.i; unfold bandS; wt_omega) hnxg hgb hcmM ?_
      intro ky d' P hk hσy hI'
      rcases hkind with ⟨hlead, hc⟩ | hpe
      · refine lt_waitO hI' hi1 hlt (by omega) (hnum ky d' P hσy) ?_ ?_
        · exact fun h1 h2 h3 => fin_iter_le hX hlead hk hσy h1 h2 h3
        · intro hs'
          have := (hc ky d' P hk hσy hs').2.1
          have := hsub ky (oDone L (g / L.block))
          omega
      · exact preE_lt_sm (hpe ky d' P hk hσy) (by omega) (by omega) (hnum ky d' P hσy)
          (fin0 hX ky hk hσy)
  | epi d =>
    obtain ⟨hs, rfl, rfl⟩ := hat
    have hpol := Hs.epi_cnt hpre hX hf hg _ le_rfl _ hσ
    rw [List.take_length] at hpol
    have hz0 : Hs.fCnt (.epi d) = 0 := by simp [Hs.fCnt, SO.epiPolled, hs]
    rw [hz0] at hpol
    have hT : epi0 ≤ dcompT (.epi d) := by
      simp only [dcompT, epiT]
      omega
    refine lags_of hpre hX hf hR' hub (T0 := epi0) hT (by wt_omega) hnxg hgb hcmM ?_
    intro ky d' P hk hσy hI'
    rcases hkind with ⟨-, hc⟩ | hpe
    · refine lt_epi hI' fun hs' => ?_
      have := (hc ky d' P hk hσy hs').2.2
      have := hsub ky (oFinal L (g / L.block))
      omega
    · exact preE_lt_epi (hpe ky d' P hk hσy)
  | _ => exact hat.elim

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wv
