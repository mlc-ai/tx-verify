-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WmAll
public import Kernels.InklingRelDecode.Proof.Progress.WkAll

@[expose] public section

/-!
# A short producer of `kv_ready` lags the polling MMA lane

A lane `g` of the MMA warp at its poll of `kv_ready (i % 3)` at the end of its trace is at the
MMA band of slot `i`. A lane `y` of the loader warp of its CTA lags it (`ld_lag_of`) when each of
its loader states of the loop after the anchor is of an iteration at most `i`: such a state is in
the loader band of a slot at most `i` (`Wt.loaderT_band`); the states before the loop are at fixed
times before every slot; the loop's end (`bar1`, then `setMaxInc`) has iteration `num_iters > i`
and is excluded by the premise; `y` has not exited and is not at a later-round state
(`Wv.noExit_peer`, `Wv.noLate`, from `g`'s two barrier-1 events, `mm_poller_end`).

The premise holds for each short producer of `Wm.mma_kv_blocked`:

* lane 0 of the loader, when it has made at most `i / 3 - δ` arrivals on `kv_ready (i % 3)`: its
  arrivals before a loop state are `below s (arrIters d) - δ` (`Wm.ld_arr_le`) (`ap_lag`);
* the copying lane, when it led every election of its trace and has issued fewer than
  `8 (i / 3 + 1 - δ)` copies: its copies before a loop state are `cpMu s d - 8 δ`
  (`Wm.ld_cp_le`) (`cp_lag`);
* a lane of the loader warp with no election in its trace: it has made at least
  `4 (d.i - num_pre)` elections before a loop state (`Wm.el_le`), so it is in iteration
  `num_pre ≤ i` (`noElect_lag`). When no lane of the loader warp led and elected, such a lane
  exists (`exists_noElect`): lane 0 if it made no election, else the lane its elections returned,
  whose own elections would return it (one leader per warp and mask).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wm
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Progress PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)
open PTX.Kernels.InklingRelDecode.Proof.Lp (PreSite ldThread)
open PTX.Kernels.InklingRelDecode.Proof.Wk (np)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

section
variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hub : ¬ HasUb X)
include hpre hX hf hR hub

/-- **An MMA lane at its `kv_ready` poll at the end of its trace** has not exited, has made two
barrier-1 events, and its state satisfies the machine's invariant. -/
theorem mm_poller_end (hg : g < L.threads) {d : Mma.D} {P : Loader.Pro}
    (hσ : St Q L X g (X.tr g).length = some (some (.w (.mma d P)))) (hw : d.site = .kvWait) :
    (∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) ∧ b1N X g (X.tr g).length ≤ 2 ∧
      (threadCode L g Q).inv (.w (.mma d P)) := by
  have hnx := Wv.noExit_of_end hX hf hσ
  obtain ⟨-, t, -, hb1, -, h3, -, -⟩ := phase_inv hpre hX hf.sound hR _ _ le_rfl hσ
  have ht : t = 0 := h3 (by simp [tKind, wKind])
  obtain ⟨tt, hr⟩ := Frame.run_some hX hub (pending_of_noExit hX hg hnx)
  have hσ' : Frame.stateAt (code L Q) X g (X.tr g).length = some (some (.w (.mma d P))) := hσ
  obtain ⟨-, -, -, -, hinv, -⟩ := Frame.end_at hf.sound hg hr hσ'
  refine ⟨hnx, ?_, hinv⟩
  rw [hb1, ht]
  simp [tPh, wPh, hw]

/-- **A lane of the CTA's loader warp lags an MMA poller** when each of its loader states is
before the poller's time `T0`. -/
theorem lags_mm {y : Nat} {d : Mma.D} {P : Loader.Pro} {T0 : Nat} (hT0 : T0 ≤ mmaT d)
    (hc0 : c0 + 6 < T0) (hnxg : ∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩)
    (hgb : b1N X g (X.tr g).length ≤ 2) (hyl : y < L.threads) (hyc : y / L.block = g / L.block)
    (hyw : y % L.block / 32 = 6)
    (hm : ∀ ky d P, ky ≤ (X.tr y).length → St Q L X y ky = some (some (.w (.loader d P))) →
      Loader.Inv L y d → loaderT d + 1 < T0) :
    Wy.Lags Wt.time Q L X y g (.w (.mma d P)) := by
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
      | mma d P =>
        simp only [RoleWarp, roleWarp] at hrw
        omega
      | loader d P => exact hm ky d P hk hσ hinv.2.1
      | exit x => exact absurd trivial hnl
  show Sched.threadTime (timed Wt.time Q L) X y < mmaT d
  rcases Wu.end_cases hX hf.sound hf.tracked hub hyl hnxy with
    ⟨σ, hσy, hinv⟩ | ⟨σ, e1, hpos, hσy, hnone, hinv, he1⟩
  · rw [threadTime_eq hσy]
    have := key _ σ le_rfl hσy hinv
    omega
  · rw [threadTime_stop hσy hnone]
    have := key _ σ (Nat.sub_le _ _) hσy hinv
    omega

/-- **A lane of the loader warp lags an MMA poller at `kv_ready`** when each of its loader
states of the loop other than its last site is of an iteration at most the poller's. -/
theorem ld_lag_of (hB : BaseWordRead L X) (hN : NumWordRead Q L X) (hg : g < L.threads)
    {d : Mma.D} {P : Loader.Pro}
    (hσ : St Q L X g (X.tr g).length = some (some (.w (.mma d P)))) (hw : d.site = .kvWait)
    {y : Nat} (hyl : y < L.threads) (hyc : y / L.block = g / L.block)
    (hyw : y % L.block / 32 = 6)
    (hle : ∀ ky d' P', ky ≤ (X.tr y).length →
      St Q L X y ky = some (some (.w (.loader d' P'))) →
      Loader.Inv L y d' → ¬ PreSite d'.site → d'.site ≠ .bar0 → d'.site ≠ .setMaxInc →
      d'.i ≤ d.i) :
    Wy.Lags Wt.time Q L X y g (.w (.mma d P)) := by
  obtain ⟨hnxg, hgb, hinvg⟩ := mm_poller_end hpre hX hf hR hub hg hσ hw
  have hI : Mma.Inv d := hinvg.2.1
  have hqk := (hI.qk (by rw [hw]; trivial)).1
  have hsr : d.site ≠ .setMaxReg := by rw [hw]; nofun
  have hsl : d.site ≠ .ldNum := by rw [hw]; nofun
  have hdn := ((words_inv hpre hX hf hB hN _ _ hσ).2.2 hsr hsl).1
  have hcta : ∀ a, ProA.cta L y a = ProA.cta L g a := fun a => ProA.cta_eq_of_block hyc a
  have hband := mmaT_band d (by rw [hw]; exact .inl trivial)
  have hmT : mmaT d = slot d.i + bandM + 1 := by
    simp only [mmaT, hw, Bound.Mma.pos]
  refine lags_mm hpre hX hf hR hub (T0 := mmaT d) le_rfl ?_ hnxg hgb hyl hyc hyw ?_
  · have : loop0 ≤ slot d.i := by unfold slot; omega
    unfold loop0 c0 at *
    omega
  intro ky d' P' hk hσy hI'
  -- the loop's end has iteration `num_iters`
  have hend : d'.site = .bar1 → False := by
    intro hs
    obtain ⟨k0, e, d0, hadj, -, -, hσ0, hn⟩ := Wk.ld_pred_le hX hk hσy (by rw [hs]; nofun)
    have hni := Lp.next_into_bar1 (hf.ldRng hyl hσ0) hn hs
    have hdn' := (page_inv hpre hX hf hN _ _ hσy).1 (by rw [hs]; rfl)
    rw [hcta, hcta] at hdn'
    have := hle ky d' P' hk hσy hI' (by rw [hs]; rintro (h | h | h) <;> cases h)
      (by rw [hs]; nofun) (by rw [hs]; nofun)
    omega
  by_cases hpl : PreSite d'.site
  · rcases hpl with h | h | h <;>
      · simp only [loaderT, h]
        have : loop0 ≤ slot d.i := by unfold slot; omega
        unfold loop0 c0 at *
        omega
  by_cases hb0 : d'.site = .bar0
  · simp only [loaderT, hb0]
    have : loop0 ≤ slot d.i := by unfold slot; omega
    unfold loop0 c1 at *
    omega
  by_cases hsm : d'.site = .setMaxInc
  · exfalso
    obtain ⟨k0, e, d0, hadj, -, -, hσ0, hn⟩ := Wk.ld_pred_le hX hk hσy (by rw [hsm]; nofun)
    obtain ⟨hs0, hi0, hn0⟩ := Lp.next_into_setMaxInc hn hsm
    obtain ⟨k1, e1, d1, hadj1, -, -, hσ1, hn1⟩ := Wk.ld_pred_le hX (k := k0) (by omega) hσ0
      (by rw [hs0]; nofun)
    have hni := Lp.next_into_bar1 (hf.ldRng hyl hσ1) hn1 hs0
    have hdn' := (page_inv hpre hX hf hN _ _ hσ0).1 (by rw [hs0]; rfl)
    rw [hcta, hcta] at hdn'
    have hk0 : k0 < (X.tr y).length := by omega
    have hI0 : Loader.Inv L y d0 := (Lp.loader_inv_at hX hf hk0 hσ0).1
    have := hle k0 d0 P' (by omega) hσ0 hI0 (by rw [hs0]; rintro (h | h | h) <;> cases h)
      (by rw [hs0]; nofun) (by rw [hs0]; nofun)
    omega
  have hlp : d'.site.inLoop = true := by
    obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d'
    simp only [PreSite, not_or] at hpl
    obtain ⟨h1, h2, h3⟩ := hpl
    cases s <;> simp_all [Loader.Site.inLoop]
  have hi := hle ky d' P' hk hσy hI' hpl hb0 hsm
  have h1 := loaderT_band d' hlp
  have h2 := slot_le_slot hi
  omega

end

/-! ### The three short producers -/

section
variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X) (hub : ¬ HasUb X)
include hpre hX hf hR hp hub

omit hp in
/-- The loader-warp lane `y` of the poller's CTA has not exited and no event of it ends it. -/
theorem ld_noEnds (hg : g < L.threads) {d : Mma.D} {P : Loader.Pro}
    (hσ : St Q L X g (X.tr g).length = some (some (.w (.mma d P)))) (hw : d.site = .kvWait)
    {y : Nat} (hyc : y / L.block = g / L.block) (hyw : y % L.block / 32 = 6) :
    ∀ e ∈ X.tr y, ¬ Ends e := by
  obtain ⟨hnxg, hgb, -⟩ := mm_poller_end hpre hX hf hR hub hg hσ hw
  have hb : L.block = 256 := hpre.block
  exact Wv.noEnds hub (Wv.noExit_peer hpre hX hf hR hyc.symm (by omega) hnxg hgb)

variable (hB : BaseWordRead L X) (hN : NumWordRead Q L X) (hg : g < L.threads) {d : Mma.D}
    {P : Loader.Pro} (hσ : St Q L X g (X.tr g).length = some (some (.w (.mma d P))))
include hB hN hg hσ

/-- **Lane 0 of the loader lags the poller** while it has not arrived for the poller's block. -/
theorem ap_lag (hw : d.site = .kvWait)
    (har : arrivals (kvReady L (g / L.block) (d.i % 3)) (X.tr (ldThread L (g / L.block))) +
      Ring.below (d.i % 3) (np Q L g) ≤ d.i / 3) :
    Wy.Lags Wt.time Q L X (ldThread L (g / L.block)) g (.w (.mma d P)) := by
  have hb : L.block = 256 := hpre.block
  have hgrid : g / L.block < L.grid := by
    unfold Launch.threads at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  obtain ⟨hyl, hyc, hy192⟩ := Lp.ldThread_props hb hgrid
  have hyw : ldThread L (g / L.block) % L.block / 32 = 6 := by rw [hy192]
  have hne := ld_noEnds hpre hX hf hR hub hg hσ hw hyc hyw
  have hl : laneOf L (ldThread L (g / L.block)) = 0 := by
    unfold laneOf
    rw [hy192]
  have hnp : np Q L (ldThread L (g / L.block)) = np Q L g := by
    simp only [np, ProA.cta_eq_of_block hyc]
  have hs3 : d.i % 3 < 3 := Nat.mod_lt _ (by omega)
  refine ld_lag_of hpre hX hf hR hub hB hN hg hσ hw hyl hyc hyw ?_
  intro ky d' P' hk hσy hI' hpl hb0 hsm
  have h := Wm.ld_arr_le hpre hX hf hR hp hk hσy hI' hpl hb0 hne hl _ hs3
  rw [hyc, hnp] at h
  have hsub : arrivals (kvReady L (g / L.block) (d.i % 3))
      ((X.tr (ldThread L (g / L.block))).take ky) ≤
      arrivals (kvReady L (g / L.block) (d.i % 3)) (X.tr (ldThread L (g / L.block))) :=
    (List.take_sublist _ _).countP_le
  have hai : d'.i ≤ Ring.Ld.arrIters d' := by
    unfold Ring.Ld.arrIters; omega
  by_contra hgt
  have hmono : Ring.below (d.i % 3) (d.i + 1) ≤ Ring.below (d.i % 3) (Ring.Ld.arrIters d') := by
    unfold Ring.below; omega
  rw [Ring.below_succ hs3, ite_eq_left rfl, Ring.below_of_slot hs3 rfl] at hmono
  omega

/-- **The copying lane lags the poller** while it led every election of its trace and has not
issued all copies of the poller's block. -/
theorem cp_lag (hw : d.site = .kvWait) {y : Nat} (hyl : y < L.threads)
    (hyc : y / L.block = g / L.block) (hyw : y % L.block / 32 = 6) (hlead : ElectLead L y (X.tr y))
    (hcp : (X.tr y).countP (issuesTo (kvReady L (g / L.block) (d.i % 3))) +
      8 * Ring.below (d.i % 3) (np Q L g) < 8 * (d.i / 3 + 1)) :
    Wy.Lags Wt.time Q L X y g (.w (.mma d P)) := by
  have hne := ld_noEnds hpre hX hf hR hub hg hσ hw hyc hyw
  have hnp : np Q L y = np Q L g := by simp only [np, ProA.cta_eq_of_block hyc]
  have hs3 : d.i % 3 < 3 := Nat.mod_lt _ (by omega)
  refine ld_lag_of hpre hX hf hR hub hB hN hg hσ hw hyl hyc hyw ?_
  intro ky d' P' hk hσy hI' hpl hb0 hsm
  have h := Wm.ld_cp_le hpre hX hf hR hp hk hσy hpl hb0 hne hlead _ hs3
  rw [hyc, hnp] at h
  have hsub : ((X.tr y).take ky).countP (issuesTo (kvReady L (g / L.block) (d.i % 3))) ≤
      (X.tr y).countP (issuesTo (kvReady L (g / L.block) (d.i % 3))) :=
    (List.take_sublist _ _).countP_le
  by_contra hgt
  have hmono : Ring.below (d.i % 3) (d.i + 1) ≤ Ring.below (d.i % 3) d'.i := by
    unfold Ring.below; omega
  rw [Ring.below_succ hs3, ite_eq_left rfl, Ring.below_of_slot hs3 rfl] at hmono
  unfold Ring.Ld.cpMu at h
  omega

/-- **A lane of the loader warp with no election lags the poller** of a block after the
preloaded ones. -/
theorem noElect_lag (hw : d.site = .kvWait) (hnpi : np Q L g ≤ d.i) {y : Nat} (hyl : y < L.threads)
    (hyc : y / L.block = g / L.block) (hyw : y % L.block / 32 = 6)
    (hel : Wm.elects X y (X.tr y).length = 0) :
    Wy.Lags Wt.time Q L X y g (.w (.mma d P)) := by
  have hnp : np Q L y = np Q L g := by simp only [np, ProA.cta_eq_of_block hyc]
  refine ld_lag_of hpre hX hf hR hub hB hN hg hσ hw hyl hyc hyw ?_
  intro ky d' P' hk hσy hI' hpl hb0 hsm
  have h := Wm.el_le hpre hX hf hp ky hk hσy hpl
  have hsub : Wm.elects X y ky ≤ Wm.elects X y (X.tr y).length := by
    unfold Wm.elects
    exact (List.take_sublist_take_left hk).countP_le
  rw [hnp] at h
  omega

end

/-- **When no lane of the loader warp led and elected, a lane of it has no election.** -/
theorem exists_noElect (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) {c : Nat}
    (hc : c < L.grid)
    (hno : ¬ ∃ h', SameWarp L (ldThread L c) h' ∧ ElectLead L h' (X.tr h') ∧
      ∃ ld, Elected (X.tr h') ld) :
    ∃ y, y < L.threads ∧ y / L.block = c ∧ y % L.block / 32 = 6 ∧
      Wm.elects X y (X.tr y).length = 0 := by
  have hb : L.block = 256 := hpre.block
  obtain ⟨hal, hac, ha192⟩ := Lp.ldThread_props hb hc
  have hzero : ∀ y, y < L.threads → y / L.block = c → y % L.block / 32 = 6 →
      (¬ ∃ e ∈ X.tr y, ∃ mask inst ld, e.kind = .elect mask inst ld) →
      Wm.elects X y (X.tr y).length = 0 := by
    intro y _ _ _ hn
    unfold Wm.elects
    rw [List.take_length, List.countP_eq_zero]
    intro e he hel
    apply hn
    refine ⟨e, he, ?_⟩
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp_all [isElectEv]
  by_cases h0 : ∃ e ∈ X.tr (ldThread L c), ∃ mask inst ld, e.kind = .elect mask inst ld
  · obtain ⟨e, he, mask, inst, ld, hk⟩ := h0
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    have hx : (X.tr (ldThread L c))[j] =
        ⟨(X.tr (ldThread L c))[j].pc, .elect mask inst ld⟩ := by rw [← hk]
    have hE : X.Elect (ldThread L c, j) (X.tr (ldThread L c))[j].pc mask inst ld :=
      show (X.tr (ldThread L c))[j]? = _ by rw [List.getElem?_eq_getElem hj, ← hx]
    have hld : ld < 32 := (hX.elect.1 _ _ _ _ _ hE).2.2.1
    set y := c * L.block + 192 + ld with hy
    have hth : L.threads = L.grid * L.block := rfl
    have hyl : y < L.threads := by
      rw [hth, hb]
      have : c + 1 ≤ L.grid := hc
      have h2 : (c + 1) * 256 ≤ L.grid * 256 := Nat.mul_le_mul_right _ this
      rw [hy, hb]
      omega
    have hyc : y / L.block = c := by rw [hy, hb]; omega
    have hyw : y % L.block / 32 = 6 := by rw [hy, hb]; omega
    refine ⟨y, hyl, hyc, hyw, hzero y hyl hyc hyw ?_⟩
    rintro ⟨e', he', mask', inst', ld', hk'⟩
    obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem he'
    have hx' : (X.tr y)[j'] = ⟨(X.tr y)[j'].pc, .elect mask' inst' ld'⟩ := by rw [← hk']
    have hE' : X.Elect (y, j') (X.tr y)[j'].pc mask' inst' ld' :=
      show (X.tr y)[j']? = _ by rw [List.getElem?_eq_getElem hj', ← hx']
    have hm : mask = mask' := by
      rw [elect_full hX hE, elect_full hX hE']
    subst hm
    have hsw : SameWarp L (ldThread L c) y :=
      ⟨⟨hal, hyl, by rw [hac, hyc]⟩, by rw [hyw, ha192]⟩
    have hll := hX.elect.2.2 _ _ _ _ _ _ _ _ _ hE hE' hsw
    have hlane : laneOf L y = ld := by
      unfold laneOf
      rw [hy, hb]
      omega
    apply hno
    refine ⟨y, hsw,
      electLead_of_elected hX ⟨_, he', mask, inst', by rw [hk', ← hll, hlane]⟩,
      ld, _, he', mask, inst', by rw [hk', ← hll]⟩
  · exact ⟨ldThread L c, hal, hac, by rw [ha192], hzero _ hal hac (by rw [ha192]) h0⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wm
