-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WkAll
public import Kernels.InklingRelDecode.Proof.Progress.WvAll
public import Kernels.InklingRelDecode.Proof.Progress.WyAll

@[expose] public section

/-!
# The committing MMA lane lags a loader lane blocked at `kv_empty`

A loader lane at its poll of `kv_empty (i % 3)` at the end of its trace, whose CTA's committing
MMA lane `cm` has made at most `i / 3 - 1` commits to the slot (`Wk.loader_empty_blocked`), is
lagged by `cm` (`loader_lag`): `cm` has not exited and its time is below the loader's.

* The loader lane has not exited and has made two barrier-1 events (`ld_poller_end`, from
  `phase_inv`), so `cm`, a worker of its CTA, is not at a later-round or exit state and has not
  exited (`Wv.noLate`, `Wv.noExit_peer`); `lags_ld` is `Wv.lags_of` for a loader poller.
* If `cm` is the elected lane of the MMA warp, its commits to `kv_empty s` before each of its
  states are `below s (Ring.Mm.done d)` (`mma_kv_commits_le`, `Ring.mma_commits` on the run from
  the end-state anchor `Wv.mma_anchor_le`). So it has not committed block `i - 3`
  (`below_le_of`): it is before the loop, or in the loop at an iteration at most `i - 2`
  (`mmaT_lt_wait`, the time bands of `WtTime.lean`), and not at the loop's end, whose count is the
  CTA's `num_iters`, above `i` (`Interface.page_inv`, `words_inv`).
* Otherwise `cm` has made no election, so it is before its role's first election (`Wv.PreE`),
  which is before the loader's poll of a block `i ≥ 3`; a loop that does not run (`Wv.fin0`) is
  excluded by the loader's iteration `i < num_iters ≤ 2 ^ 24` (`Lp.numIters_le24`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wk
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Progress PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX.Kernels.InklingRelDecode.Proof.Progress.Wv (PreE)
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvEmpty)
open PTX.Kernels.InklingRelDecode.Proof.Ring (wAt)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The MMA lane's commits to `kv_empty` at a state up to the trace's end**, when every
election of the thread returned its lane and no event of the thread ends it. -/
theorem mma_kv_commits_le (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {k : Nat} {d : Mma.D} {P : Loader.Pro}
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.mma d P))))
    (hs : d.site ≠ .setMaxReg) (hlead : ElectLead L g (X.tr g)) (hbc : Mma.BcastRun (X.tr g))
    (hne : ∀ e ∈ X.tr g, ¬ Ends e) :
    ∀ s < 3, ((X.tr g).take k).countP (commitsTo (kvEmpty L (g / L.block) s)) =
      Ring.below s (Ring.Mm.done d) := by
  intro s hs3
  obtain ⟨hg, hw, k0, d0, hk0, -, h0, hd, hs0, hin, hC, -⟩ :=
    Proof.Wv.mma_anchor_le hpre hX hf hR hk hσ hs
  obtain ⟨hT, hend, hin'⟩ := SO.mma_exec_run hpre hw hg hX hk0 h0 hd hin
  have hE : ∀ e ∈ ((X.tr g).drop k0).take (k - k0), Ring.MmRun L g e := by
    intro e he
    have hmem : e ∈ X.tr g := List.mem_of_mem_drop (List.mem_of_mem_take he)
    exact ⟨⟨hne e hmem, hlead e hmem⟩, hbc e hmem⟩
  have h := Ring.mma_commits hpre hg hT hE hin' hend hs3
  have hz : Ring.Mm.done d0 = 0 := by simp [Ring.Mm.done, hs0]
  have hb0 : Ring.below s 0 = 0 := by unfold Ring.below; omega
  rw [hz, hb0, Nat.add_zero] at h
  rw [Ring.countP_take_split _ _ hk0, h, hC, Nat.zero_add]

/-- **A loader lane at its `kv_empty` poll at the end of its trace** has not exited, has made two
barrier-1 events, and its state satisfies the machine's invariant. -/
theorem ld_poller_end (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hub : ¬ HasUb X) (hg : g < L.threads)
    {d : Loader.D} {P : Loader.Pro}
    (hσ : St Q L X g (X.tr g).length = some (some (.w (.loader d P)))) (hw : d.site = .wait) :
    (∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) ∧ b1N X g (X.tr g).length ≤ 2 ∧
      (threadCode L g Q).inv (.w (.loader d P)) := by
  have hnx := Wv.noExit_of_end hX hf hσ
  obtain ⟨-, t, -, hb1, -, h3, -, -⟩ := phase_inv hpre hX hf.sound hR _ _ le_rfl hσ
  have ht : t = 0 := h3 (by simp [tKind, wKind])
  obtain ⟨tt, hr⟩ := Frame.run_some hX hub (pending_of_noExit hX hg hnx)
  have hσ' : Frame.stateAt (code L Q) X g (X.tr g).length = some (some (.w (.loader d P))) := hσ
  obtain ⟨-, -, -, -, hinv, -⟩ := Frame.end_at hf.sound hg hr hσ'
  refine ⟨hnx, ?_, hinv⟩
  rw [hb1, ht]
  simp [tPh, wPh, hw]

/-- **A lane of the MMA warp lags a loader poller** (`Wv.lags_of` for a loader poller). -/
theorem lags_ld (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hub : ¬ HasUb X) {y : Nat}
    {d : Loader.D} {P : Loader.Pro} {T0 : Nat} (hT0 : T0 ≤ loaderT d) (hc0 : c0 + 6 < T0)
    (hnxg : ∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) (hgb : b1N X g (X.tr g).length ≤ 2)
    (hy : Hs.MmaOf L (g / L.block) y)
    (hm : ∀ ky d P, ky ≤ (X.tr y).length → St Q L X y ky = some (some (.w (.mma d P))) →
      Mma.Inv d → mmaT d + 1 < T0) :
    Wy.Lags Wt.time Q L X y g (.w (.loader d P)) := by
  obtain ⟨hyl, hyc, hyw⟩ := hy
  have hb : L.block = 256 := hpre.block
  have hyd : ¬ y % L.block < 128 := by omega
  have hc : g / L.block = y / L.block := hyc.symm
  have hnxy := Wv.noExit_peer hpre hX hf hR hc hyd hnxg hgb
  refine ⟨hnxy, ?_⟩
  have key : ∀ ky σ, ky ≤ (X.tr y).length → St Q L X y ky = some (some σ) →
      (threadCode L y Q).inv σ → Wt.time y σ + 1 < T0 := by
    intro ky σ hk hσ hinv
    have hnl := Wv.noLate hpre hX hf.sound hR hc hk hnxg hgb hσ
    have hrw := roleWarp_inv hf.roleWarp _ _ hk hσ
    cases σ with
    | d s' => exact absurd ((cls_inv ky _ hk hσ).mp trivial) hyd
    | w s' =>
      cases s' with
      | worker w =>
        have := Wv.workerT_early w hnl
        show workerT w + 1 < T0
        omega
      | idle d =>
        simp only [RoleWarp, roleWarp] at hrw
        omega
      | loader d P =>
        simp only [RoleWarp, roleWarp] at hrw
        omega
      | mma d P => exact hm ky d P hk hσ hinv.2.1
      | exit x => exact absurd trivial hnl
  show Sched.threadTime (timed Wt.time Q L) X y < loaderT d
  rcases Wu.end_cases hX hf.sound hf.tracked hub hyl hnxy with
    ⟨σ, hσy, hinv⟩ | ⟨σ, e1, hpos, hσy, hnone, hinv, he1⟩
  · rw [threadTime_eq hσy]
    have := key _ σ le_rfl hσy hinv
    omega
  · rw [threadTime_stop hσy hnone]
    have := key _ σ (Nat.sub_le _ _) hσy hinv
    omega

/-- The block `i - 3` of slot `i % 3` is not committed: `below s B ≤ i / 3 - 1` means
`B + 3 ≤ i`. -/
theorem below_le_of {B i : Nat} (h : Ring.below (i % 3) B + 1 ≤ i / 3) :
    B + 3 ≤ i := by
  unfold Ring.below at h
  omega

theorem loaderT_wait {d : Loader.D} (hw : d.site = .wait) :
    loaderT d = slot d.i + bandL + (21 - Bound.Loader.pos .wait) := by
  unfold loaderT
  rw [hw]

/-- **An MMA loop state two iterations back is before a loader `wait`.** -/
theorem mmaT_lt_wait {d' : Mma.D} {d : Loader.D} (hm : Mma.QkSite d'.site ∨ Mma.PvSite d'.site)
    (hw : d.site = .wait) (hi : d'.i + 2 ≤ d.i) : mmaT d' + 1 < loaderT d := by
  have h1 := Wv.mmaT_loop_le d' hm
  have h2 : slot d.i ≤ loaderT d := by rw [loaderT_wait hw]; omega
  have h3 := slot_le_slot hi
  unfold slot at h1 h2 h3
  unfold bandM span at *
  omega

/-- A state before the loop is before a loader `wait`. -/
theorem pre_lt_wait {d' : Mma.D} {d : Loader.D} (hm : Mma.PreSite d'.site)
    (hw : d.site = .wait) : mmaT d' + 1 < loaderT d := by
  have h1 := Wv.mmaT_pre hm
  have h2 : slot d.i ≤ loaderT d := by rw [loaderT_wait hw]; omega
  unfold slot c1 loop0 at *
  omega

/-- **The committing MMA lane lags a loader lane at its `kv_empty` poll** while it has not
committed the block three before the loader's. -/
theorem loader_lag (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hB : BaseWordRead L X)
    (hN : NumWordRead Q L X) (hMB : Mma.MmaBcast L X) (hub : ¬ HasUb X) (hg : g < L.threads)
    {d : Loader.D}
    {P : Loader.Pro} (hσ : St Q L X g (X.tr g).length = some (some (.w (.loader d P))))
    (hw : d.site = .wait)
    (hle : (X.tr (Hs.cmOf L X (g / L.block))).countP
      (commitsTo (kvEmpty L (g / L.block) (d.i % 3))) + 1 ≤ d.i / 3) :
    Wy.Lags Wt.time Q L X (Hs.cmOf L X (g / L.block)) g (.w (.loader d P)) := by
  have hb : L.block = 256 := hpre.block
  have hgrid : g / L.block < L.grid := by
    unfold Launch.threads at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  obtain ⟨hnxg, hgb, hinvg⟩ := ld_poller_end hpre hX hf hR hub hg hσ hw
  obtain ⟨-, -, hz⟩ := ProA.cta_lt hpre hg
  have hN24 := Lp.numIters_le24 hpre hz (ProA.cta L g .x)
  set N := Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) with hNdef
  have hdn : d.n = N := (page_inv hpre hX hf hN _ _ hσ).1 (by rw [hw]; rfl)
  have hiN : d.i < N := by rw [← hdn]; exact (hf.ldRng hg hσ).loop (by rw [hw]; rfl)
  have hi3 : 1 ≤ d.i / 3 := by omega
  have hcmM : Hs.MmaOf L (g / L.block) (Hs.cmOf L X (g / L.block)) := Hs.cm_mma hpre hgrid
  have hcta : ∀ a, ProA.cta L (Hs.cmOf L X (g / L.block)) a = ProA.cta L g a :=
    fun a => ProA.cta_eq_of_block hcmM.2.1 a
  have hnum : ∀ ky d P, St Q L X (Hs.cmOf L X (g / L.block)) ky =
      some (some (.w (.mma d P))) → d.site ≠ .setMaxReg → d.site ≠ .ldNum → d.n = N := by
    intro ky d P hσy h1 h2
    have := ((words_inv hpre hX hf hB hN _ _ hσy).2.2 h1 h2).1
    rw [hcta, hcta] at this
    exact this
  have hnxy : ∀ j pc, X.get (Hs.cmOf L X (g / L.block), j) ≠ some ⟨pc, .exit⟩ :=
    Wv.noExit_peer hpre hX hf hR hcmM.2.1.symm (by have := hcmM.2.2; omega) hnxg hgb
  have hsub : ∀ ky, ((X.tr (Hs.cmOf L X (g / L.block))).take ky).countP
      (commitsTo (kvEmpty L (g / L.block) (d.i % 3))) ≤
      (X.tr (Hs.cmOf L X (g / L.block))).countP (commitsTo (kvEmpty L (g / L.block) (d.i % 3))) :=
    fun ky => (List.take_sublist _ _).countP_le
  refine lags_ld hpre hX hf hR hub (T0 := loaderT d) le_rfl ?_ hnxg hgb hcmM ?_
  · have : slot d.i ≤ loaderT d := by rw [loaderT_wait hw]; omega
    unfold slot c0 loop0 at *
    omega
  intro ky d' P' hk hσy hI'
  have hfin0 : (d'.site = .finBar ∨ d'.site = .finElect) → d'.i = 0 → False := by
    intro hs hi
    have hsr : d'.site ≠ .setMaxReg := by rcases hs with h | h <;> rw [h] <;> nofun
    have hsl : d'.site ≠ .ldNum := by rcases hs with h | h <;> rw [h] <;> nofun
    rcases Wv.fin0 hX ky hk hσy hs hi with h | h <;> rw [hnum ky d' P' hσy hsr hsl] at h <;> omega
  have hbcy : Mma.BcastRun (X.tr (Hs.cmOf L X (g / L.block))) := hMB _ hcmM.1 hcmM.2.2
  by_cases hL : ∃ y, Hs.LeadOf L X (g / L.block) y
  · -- the elected lane: its commits as a function of its state
    obtain ⟨y, hy⟩ := hL
    have hcm : Hs.cmOf L X (g / L.block) = y := Hs.cm_eq hX hy
    obtain ⟨⟨-, hyc, -⟩, mm, pc, inst, hel⟩ := hy
    have hlead : ElectLead L y (X.tr y) :=
      electLead_of_elected hX ⟨_, List.mem_of_getElem? (show (X.tr y)[mm]? = _ from hel),
        4294967295, inst, rfl⟩
    rw [hcm] at hσy hk hnxy hsub hle hnum hbcy
    rcases Wv.site_cases d'.site with hs | hs | hs | hs
    · exact pre_lt_wait hs hw
    · have hsr : d'.site ≠ .setMaxReg := by
        intro h; rw [h] at hs; exact hs
      have hc := mma_kv_commits_le hpre hX hf hR hk hσy hsr hlead hbcy
        (Wv.noEnds hub hnxy)
        (d.i % 3) (Nat.mod_lt _ (by omega))
      rw [hyc] at hc
      have hdone : Ring.Mm.done d' = d'.i - 1 := by
        obtain ⟨s, i, n, tm, pro⟩ := d'
        cases s <;> simp_all [Mma.QkSite, Ring.Mm.done]
      have := below_le_of (i := d.i) (B := d'.i - 1)
        (by have := hsub ky; rw [hc, hdone] at this; omega)
      exact mmaT_lt_wait (.inl hs) hw (by omega)
    · have hsr : d'.site ≠ .setMaxReg := by
        intro h; rw [h] at hs; exact hs
      have hc := mma_kv_commits_le hpre hX hf hR hk hσy hsr hlead hbcy
        (Wv.noEnds hub hnxy)
        (d.i % 3) (Nat.mod_lt _ (by omega))
      rw [hyc] at hc
      have hdone : d'.i - 1 ≤ Ring.Mm.done d' := by
        obtain ⟨s, i, n, tm, pro⟩ := d'
        cases s <;> simp_all [Mma.PvSite, Ring.Mm.done]
      have hmono : Ring.below (d.i % 3) (d'.i - 1) ≤ Ring.below (d.i % 3) (Ring.Mm.done d') := by
        unfold Ring.below; omega
      have := below_le_of (i := d.i) (B := d'.i - 1)
        (by have := hsub ky; rw [hc] at this; omega)
      exact mmaT_lt_wait (.inr hs) hw (by omega)
    · have hsr : d'.site ≠ .setMaxReg := by
        intro h; rw [h] at hs; unfold FinSite at hs; rcases hs with h | h | h | h | h <;> cases h
      have hsl : d'.site ≠ .ldNum := by
        intro h; rw [h] at hs; unfold FinSite at hs; rcases hs with h | h | h | h | h <;> cases h
      have hc := mma_kv_commits_le hpre hX hf hR hk hσy hsr hlead hbcy
        (Wv.noEnds hub hnxy)
        (d.i % 3) (Nat.mod_lt _ (by omega))
      rw [hyc] at hc
      have hn' := hnum ky d' P' hσy hsr hsl
      have hfi := Wv.fin_iter_le hX hlead hk hσy hs (by rw [hn']; omega) (by rw [hn']; omega)
      have hdone : Ring.Mm.done d' = N := by
        obtain ⟨s, i, n, tm, pro⟩ := d'
        unfold FinSite at hs
        simp only at hs hfi hn'
        have hi0 : i ≠ 0 := by omega
        rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp [Ring.Mm.done, hi0, hn']
      have := below_le_of (i := d.i) (B := N) (by have := hsub ky; rw [hc, hdone] at this; omega)
      omega
  · -- no elected lane: the lane is before its role's first election
    have hpe : PreE d' := by
      by_contra hne
      obtain ⟨j, e, mask, inst, ld, -, he, hk'⟩ := Wv.elect_of hX hf hbcy ky hk hσy hne
      have hcm : Hs.cmOf L X (g / L.block) = g / L.block * L.block + 224 := by
        unfold Hs.cmOf
        simp only [hL, dite_false]
      rw [hcm] at he
      exact Wv.noElect_of hpre hX hgrid hL j e mask inst ld he hk'
    rcases hpe with hs | ⟨hi0, hs⟩
    · exact pre_lt_wait hs hw
    · rcases hs with h | h | h | h | h | h | h
      all_goals first
        | exact (hfin0 (.inl h) hi0).elim
        | exact (hfin0 (.inr h) hi0).elim
        | exact mmaT_lt_wait (.inl (by rw [h]; trivial)) hw (by omega)

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wk
