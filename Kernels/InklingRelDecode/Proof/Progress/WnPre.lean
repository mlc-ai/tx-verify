-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WmAll
public import Kernels.InklingRelDecode.Proof.Interface.WnAll

@[expose] public section

/-!
# The MMA warp's `kv_ready` poll for a preloaded block (`Wm.MmaKvPreRest`)

A lane `g` of the MMA warp at its poll of `kv_ready i` for a block `i < num_pre` (so `i < 3`, the
poll's parity is `0`): the final phase of `kv_ready i` is `0` (`Wm.full_phase_le` with the
parity), so by `Wm.full_short` either no arrival unit is recorded, or one is and fewer than eight
copies completed.

* **No arrival**: thread 0 of the CTA has made no arrival on `kv_ready i` (each would leave a
  counted record, `Wm.arrive_rec`), so it has no state at `bar18` (`Interface.arr_of_bar18`).
* **Fewer than eight copies**, with every tensor copy notified (else an open `.tensor`
  obligation): the threads of warps 0 and 1 that lead their elections (`Lp.exists_lead`) cannot
  both have a state at `bar18`: each would have issued its four copies of block `i` before it
  (`Interface.ptc_of_bar18`, `Interface.ptc_issue`), eight distinct events, each leaving a
  completed record (`Wm.copy_rec`, `eight_le`).

A default-partition thread with no state at `bar18` lags the lane (`pre_lag`): it has not exited
(its exit is an epilogue state, which follows `bar18`, `Interface.back_bar18`), and its state, or
the state before its last event if it stopped, is a start or prologue state, timed before every
slot.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wn
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)
open PTX.Kernels.InklingRelDecode.Proof.Wk (np)
open PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.MBarrier hiding okPolls

noncomputable section
set_option maxRecDepth 100000

/-- **Eight distinct records satisfying `p`** give a count of at least eight. -/
theorem eight_le {log : List (Record Ref)} {p : Record Ref → Bool} (f : Fin 2 × Fin 4 → Ref)
    (hf : Function.Injective f) (hmem : ∀ x, ∃ r ∈ log, r.id = f x ∧ p r = true) :
    8 ≤ log.countP p := by
  classical
  have hsub : Finset.univ.image f ⊆ ((log.filter p).map Record.id).toFinset := by
    intro z hz
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨r, hr, hid, hp⟩ := hmem x
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨r, List.mem_filter.mpr ⟨hr, hp⟩, hid⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf] at h1
  have h2 := List.toFinset_card_le ((log.filter p).map Record.id)
  rw [List.length_map, ← List.countP_eq_length_filter] at h2
  have h8 : (Finset.univ : Finset (Fin 2 × Fin 4)).card = 8 := by decide
  omega

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **A default-partition thread with no state at `bar18` lags an MMA lane at `kvWait`.** -/
theorem pre_lag (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hub : ¬ HasUb X) {d : Mma.D} {P : Loader.Pro} (hw : d.site = .kvWait)
    {y : Nat} (hyl : y < L.threads) (hyd : y % L.block < 128)
    (hno : ∀ k (d0 : ProA.D), k ≤ (X.tr y).length →
      St Q L X y k = some (some (.d (.pro d0))) → d0.site = .bar18 → False) :
    Wy.Lags Wt.time Q L X y g (.w (.mma d P)) := by
  have hmT : mmaT d = slot d.i + bandM + 1 := by
    simp only [mmaT, hw, Bound.Mma.pos]
  have hpast : ∀ k s, k ≤ (X.tr y).length → St Q L X y k = some (some (.d s)) →
      dcompT s < slot d.i := by
    intro k s hk hσy
    have hs0 := slot_le_slot (show 0 ≤ d.i from Nat.zero_le _)
    cases s with
    | dstart d0 =>
      have := dstartT_le d0
      simp only [dcompT]
      wt_omega
    | pro p =>
      have := Wx.pro_idx_le p.site
      simp only [dcompT, proT]
      wt_omega
    | sm d' =>
      exfalso
      obtain ⟨k0, d0, h1, h2, h3⟩ := back_bar18 hk hσy (.inl ⟨d', rfl⟩)
      exact hno k0 d0 (by omega) h2 h3
    | epi d' =>
      exfalso
      obtain ⟨k0, d0, h1, h2, h3⟩ := back_bar18 hk hσy (.inr ⟨d', rfl⟩)
      exact hno k0 d0 (by omega) h2 h3
  have hnx : ∀ j pc, X.get (y, j) ≠ some ⟨pc, .exit⟩ := by
    intro j pc hj
    have hj' : j ≤ (X.tr y).length :=
      (List.getElem?_eq_some_iff.mp (show (X.tr y)[j]? = _ from hj)).1.le
    rcases exit_event_state hX hf.sound hf.tracked hj with ⟨de, hσ', -⟩ | ⟨x, hσ', -⟩
    · obtain ⟨k0, d0, h1, h2, h3⟩ := back_bar18 hj' hσ' (.inr ⟨de, rfl⟩)
      exact hno k0 d0 (by omega) h2 h3
    · obtain ⟨s', hs'⟩ := B0N.dstate_of hj' hσ' hyd
      cases hs'
  refine ⟨hnx, ?_⟩
  show Sched.threadTime (timed Wt.time Q L) X y < mmaT d
  rcases Wu.end_cases hX hf.sound hf.tracked hub hyl hnx with
    ⟨σ, hσy, -⟩ | ⟨σ, e1, hpos, hσy, hnone, -, he1⟩
  · obtain ⟨sy, rfl⟩ := B0N.dstate_of le_rfl hσy hyd
    rw [threadTime_eq hσy]
    have := hpast _ sy le_rfl hσy
    show dcompT sy < mmaT d
    unfold bandM at hmT
    omega
  · obtain ⟨sy, rfl⟩ := B0N.dstate_of (Nat.sub_le _ _) hσy hyd
    rw [threadTime_stop hσy hnone]
    have := hpast _ sy (Nat.sub_le _ _) hσy
    show dcompT sy + 1 < mmaT d
    unfold bandM at hmT
    omega

/-- **`Wm.MmaKvPreRest`** for `Wt.time`. -/
theorem mmaKvPre_of (hpre : Pre Q L mem0)
    (hF : ∀ X, Consistent L kernel asms mem0 X → ThreadFacts Q L mem0 X)
    (hR : ∀ X, Consistent L kernel asms mem0 X → RoleReads L X)
    (hNP : ∀ X, Consistent L kernel asms mem0 X → NumPreRead Q L X)
    (hub : ∀ X, Consistent L kernel asms mem0 X → ¬ HasUb X)
    (hP : ∀ X, Consistent L kernel asms mem0 X →
      ∃ P : Sr.SrPkg L kernel asms mem0 X, ∀ c, P.cm c = Hs.cmOf L X c) :
    Wm.MmaKvPreRest Wt.time Q L mem0 := by
  intro X g d P m par before hmax hp hrel hσ hw hi hat hst hpar
  have hX := hmax.1
  have hf := hF X hX
  have hg := hp.1
  have hb : L.block = 256 := hpre.block
  have hth : L.threads = L.grid * L.block := rfl
  have hgrid : g / L.block < L.grid := by
    unfold Launch.threads at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  rcases hat with ⟨-, rfl, rfl⟩ | ⟨hs', -⟩
  swap
  · rw [hw] at hs'; cases hs'
  set c := g / L.block with hcdef
  have hnp3 : np Q L g ≤ 3 := Lp.numPre_le _ _ _
  have hi3 : d.i < 3 := by omega
  have hs3 : d.i % 3 < 3 := Nat.mod_lt _ (by omega)
  have hmod : d.i % 3 = d.i := Nat.mod_eq_of_lt hi3
  have hdiv : d.i / 3 = 0 := Nat.div_eq_of_lt hi3
  obtain ⟨G, hcm⟩ := hP X hX
  obtain ⟨pArr, pCp, hPS⟩ := Lp.preRing_of hpre hX hf c hgrid (d.i % 3) hs3
  have H := Lp.slot_hyp hpre hX hf (hR X hX) (hNP X hX) G hgrid hs3 hPS
  set S := Lp.slotOf Q L X c (d.i % 3) (G.cm c) pArr pCp with hS
  have hcmM : Hs.MmaOf L c (Hs.cmOf L X c) := Hs.cm_mma hpre hgrid
  have h7 := roleWarp_inv hf.roleWarp _ _ le_rfl hσ
  simp only [RoleWarp, roleWarp] at h7
  have hcw : SameWarp L S.cm g := by
    show SameWarp L (G.cm c) g
    rw [hcm]
    obtain ⟨h1, h2, h3⟩ := hcmM
    exact ⟨⟨h1, hg, h2⟩, by rw [h3]; omega⟩
  have hle : before.phase ≤ d.i / 3 + 1 :=
    Wm.full_phase_le hpre hX hf (hR X hX) H hσ hw rfl hcw hst
  have hpar' : before.phase % 2 = d.i / 3 % 2 := by omega
  rw [hdiv] at hle hpar'
  have hph : before.phase = 0 := by omega
  have hfull : S.full = kvReady L c d.i := by
    show kvReady L c (d.i % 3) = _
    rw [hmod]
  -- a thread of the CTA's default partition
  have hcta : ∀ {y : Nat}, y / L.block = c → np Q L y = np Q L g := by
    intro y hy
    show ProA.numPre Q _ _ = ProA.numPre Q _ _
    rw [ProA.cta_eq_of_block hy, ProA.cta_eq_of_block hy]
  rcases Wm.full_short hX H hst with hu | ⟨-, hc⟩
  · -- no arrival: thread 0 of the CTA lags the lane
    rw [hph] at hu
    have hyl : c * L.block < L.threads := by rw [hth, hb] at *; omega
    have hy0 : c * L.block % L.block = 0 := Nat.mul_mod_left _ _
    have hyc : c * L.block / L.block = c := by rw [hb]; omega
    have hno : ∀ k (d0 : ProA.D), k ≤ (X.tr (c * L.block)).length →
        St Q L X (c * L.block) k = some (some (.d (.pro d0))) → d0.site = .bar18 → False := by
      intro k d0 hk hσ0 hs0
      have hbn : d.i < np Q L (c * L.block) := by rw [hcta hyc]; exact hi
      obtain ⟨k0, pc, -, he⟩ := arr_of_bar18 hpre hX hf hyl hy0 hbn hk hσ0 hs0
      rw [hyc, ← hfull] at he
      obtain ⟨r, hr, -, hcr⟩ := Wm.arrive_rec hX H he
      have h1 := Wm.units_eq_countP H
      have h2 : 0 < (X.objects S.full).countP countedArrive :=
        List.countP_pos_iff.mpr ⟨r, hr, hcr⟩
      omega
    exact Wy.blk_of_lags hX hσ hyl
      (pre_lag hX hf (hub X hX) hw hyl (by omega) hno)
  · -- fewer than eight copies
    rw [hph] at hc
    by_cases hall : ∀ i mapAddress s, X.TensorIssue i mapAddress s →
        ∃ observation, X.tensor i = some observation ∧ observation.effects.notified = true
    swap
    · exact .inl ⟨.tensor, .inr (.inr (.inl rfl)), hall⟩
    by_contra hnb
    -- the leading thread of warp `w` has a state at `bar18`
    have key : ∀ w : Fin 2, ∃ h, h < L.threads ∧ h / L.block = c ∧ h % L.block / 32 = w.val ∧
        ElectLead L h (X.tr h) ∧ ∃ (k : Nat) (d0 : ProA.D), k ≤ (X.tr h).length ∧
          St Q L X h k = some (some (.d (.pro d0))) ∧ d0.site = .bar18 := by
      intro w
      have hw0 : c * L.block + 32 * w.val < L.threads := by
        have := w.isLt
        rw [hth, hb] at *; omega
      obtain ⟨h, hsw, hlead⟩ := Lp.exists_lead hX hb hw0
      obtain ⟨⟨-, hh1, hcta'⟩, hwarp⟩ := hsw
      have hhc : h / L.block = c := by
        have := w.isLt
        rw [hb] at hcta' ⊢; omega
      have hhw : h % L.block / 32 = w.val := by
        have := w.isLt
        rw [hb] at hwarp ⊢; omega
      refine ⟨h, hh1, hhc, hhw, hlead, ?_⟩
      by_contra hne
      push Not at hne
      exact hnb (Wy.blk_of_lags hX hσ hh1
        (pre_lag hX hf (hub X hX) hw hh1
          (by have := w.isLt; rw [hb] at hhw ⊢; omega)
          (fun k d0 hk hσ0 hs0 => hne k d0 hk hσ0 hs0)))
    choose hh hhl hhc hhw hhlead kB dB hkB hσB hsB using key
    -- its four copies of block `d.i`
    have hK : ∀ x : Fin 2 × Fin 4, ∃ (k : Nat) (d' : ProA.D), k < (X.tr (hh x.1)).length ∧
        St Q L X (hh x.1) k = some (some (.d (.pro d'))) ∧
          d'.site = ProA.ptcSite (4 * d.i + x.2.val) := by
      intro x
      have ht : ProA.tidOf L (hh x.1) < 64 := by
        have := x.1.isLt
        have := hhw x.1
        unfold ProA.tidOf
        rw [hb] at this ⊢; omega
      have hbn : (4 * d.i + x.2.val) / 4 < np Q L (hh x.1) := by
        rw [hcta (hhc x.1)]
        have : (4 * d.i + x.2.val) / 4 = d.i := by have := x.2.isLt; omega
        rw [this]; exact hi
      obtain ⟨k', d', hk', hσ', hs'⟩ := ptc_of_bar18 hpre hX hf (hhl x.1) ht (hhlead x.1)
        (by have := x.2.isLt; omega) hbn (hkB x.1) (hσB x.1) (hsB x.1)
      exact ⟨k', d', by have := hkB x.1; omega, hσ', hs'⟩
    choose K dK hK1 hK2 hK3 using hK
    have hrec : ∀ x, ∃ r ∈ X.objects S.full,
        r.id = Ref.async (hh x.1, K x) (.notify .load) ∧ Wm.doneCp r = true := by
      intro x
      obtain ⟨pc, a, sp, he, hm⟩ := ptc_issue hpre hX hf (hhl x.1) (hK1 x) (hK2 x)
        (by have := x.2.isLt; omega) (hK3 x)
      have hm' : sp.mbar = S.full := by
        rw [hm, hfull, hhc x.1]
        congr 1
        have := x.2.isLt
        omega
      exact Wm.copy_rec hX H he hm' (hall _ _ _ ⟨pc, he⟩)
    have hinj : Function.Injective (fun x : Fin 2 × Fin 4 =>
        (Ref.async (hh x.1, K x) (.notify .load) : Ref)) := by
      intro x x' hxx
      simp only [Ref.async.injEq, Prod.mk.injEq, and_true] at hxx
      obtain ⟨h1, h2⟩ := hxx
      have hw1 : x.1 = x'.1 := by
        apply Fin.ext
        rw [← hhw x.1, ← hhw x'.1, h1]
      have hσ1 := hK2 x
      have hσ2 := hK2 x'
      rw [← hw1, ← h2] at hσ2
      rw [hσ1] at hσ2
      simp only [Option.some.injEq, TSt.d.injEq, DComp.St.pro.injEq] at hσ2
      have hsite := hK3 x'
      rw [← hσ2, hK3 x] at hsite
      have := Lp.ptcSite_inj _ (by have := x.2.isLt; omega) _
        (by have := x'.2.isLt; omega) hsite
      exact Prod.ext hw1 (Fin.ext (by omega))
    have h8 := eight_le _ hinj hrec
    have hcc : completedTxCount (X.objects S.full) = (X.objects S.full).countP Wm.doneCp := rfl
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wn
