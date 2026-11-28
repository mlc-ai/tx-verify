-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.OutFence
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Lemmas.Kernel.FrameEnd
import Lemmas.Kernel.ElectSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.StepPlumb
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Cnt9
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarLag
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Pred
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.OutSeq
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.PredArr
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticAsyncRef

@[expose] public section

/-! # Warpgroup 0's output trace facts

The three facts barrier 9's publication of the output tiles uses (`OutRows`,
`Protocol/Bar/Bar9.lean`), with `R` the CTA's block count:

* `wg0_outIssue`: a tensor store (pcs 1358, 1516, 1673, 1831: a static scan) is chunk `c`'s of a
  lane of warps 0 and 1, reading the slots of its tile, after its barrier-9 event of ordinal
  `2 R + 2 + c`: the store's state is `otma c`, which follows the election `oel c`, which follows
  barrier 9 at `obar c` only for a warp word at most `1` (`Wg0.opos_pred`); the barrier's ordinal
  among the role's is `3 R + 2 + c` (`Wg0.bar_ord`), the `2 R + 2 + c`-th on barrier 9
  (`w0_idCnt`);
* `wg0_outStage`: before its barrier-9 event of ordinal `2 R + 2 + c` a lane of warpgroup 0 made
  its proxy fence and before it its 32 staging stores of chunk `c`: that event is at `obar c`,
  and the 33 states before it are the chunk's consecutive sites (a backward walk, `walk`);
* `wg0_outExit`: an exiting lane of warpgroup 0 made at least `2 R + 6` barrier-9 events (it
  passed all `3 R + 7` role barriers, `w0_lagB`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-! ### Barrier 9's ordinals -/

/-- The role's ordinal of barrier 9's `2 R + 2 + c`-th event is `3 R + 2 + c`. -/
private theorem cnt9_inj {R p B c : Nat} (hc : c < 4) (hB : Wg0.idAt R p B = 9)
    (h : w0IdCnt R p 9 B = 2 * R + 2 + c) : B = 3 * R + 2 + c := by
  have h0 := w0Cnt9_epi R p (2 + c) (by omega)
  rw [← Nat.add_assoc, show min (2 + c) 6 = 2 + c by omega] at h0
  have hid : Wg0.idAt R p (3 * R + 2 + c) = 9 := by
    simp only [Wg0.idAt]; split_ifs <;> omega
  rcases Nat.lt_trichotomy B (3 * R + 2 + c) with hl | he | hl
  · have h1 := w0IdCnt_mono (R := R) (p := p) (id := 9) (Nat.succ_le_of_lt hl)
    rw [w0IdCnt_succ, ite_eq_left hB] at h1
    omega
  · exact he
  · have h1 := w0IdCnt_mono (R := R) (p := p) (id := 9) (Nat.succ_le_of_lt hl)
    rw [w0IdCnt_succ, ite_eq_left hid] at h1
    omega

/-- A state of warpgroup 0 at position `i + 1` of an output sequence follows one at position
`i`; the election's state follows the barrier's only for a warp word at most `1`. -/
private theorem back1 (hFw : Follow P L X) (hnu : NoUbInner L X) {y : Nat}
    (hw : warp L y < 4) (hy : y < L.threads) {t : Nat} (ht : t < (X.tr y).length)
    {d : Wg0.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    {c : Fin 4} {i : Nat} (ho : Wg0.opos d = some (c, i + 1)) :
    ∃ t', t = t' + 1 ∧ ∃ (d' : Wg0.Control.D) (n' : Cls → Nat),
      Frame.stateAt (thread P L) X y t' = some (some (.inr ⟨.inl .wg0, d'⟩, n')) ∧
      Wg0.opos d' = some (c, i) ∧ (d.site = .oel c → scmpi .gt .s (warpW L y) 1 = false) ∧
      ∃ e, X.get (y, t') = some e ∧ Wg0.Control.succ P L y (warpW L y) d' e = some (some d) := by
  rcases wg0_pred_pre hFw (LaneUbFree.of_inner hnu hw ht) hw hy ht.le hσ with
      ⟨t', rfl, d', n', e, he, hs', hS⟩ | hsm
  · obtain ⟨h1, h2⟩ := Wg0.opos_pred hS ho
    exact ⟨t', rfl, d', n', hs', h1, h2, e, he, hS⟩
  · simp [Wg0.opos, hsm] at ho

/-- **The backward walk**: the `s` states before a state at position `i` of an output sequence
are at positions `i - s`. -/
private theorem walk (hFw : Follow P L X) (hnu : NoUbInner L X) {y : Nat}
    (hw : warp L y < 4) (hy : y < L.threads) {j : Nat} (hj : j < (X.tr y).length)
    {d : Wg0.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X y j = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    {c : Fin 4} {i : Nat} (ho : Wg0.opos d = some (c, i)) :
    ∀ s ≤ i, s ≤ j ∧ ∃ (d' : Wg0.Control.D) (n' : Cls → Nat),
      Frame.stateAt (thread P L) X y (j - s) = some (some (.inr ⟨.inl .wg0, d'⟩, n')) ∧
      Wg0.opos d' = some (c, i - s) := by
  intro s
  induction s with
  | zero => intro; exact ⟨Nat.zero_le _, d, n, hσ, ho⟩
  | succ s ih =>
    intro hs
    obtain ⟨-, d1, n1, h1, o1⟩ := ih (by omega)
    rw [show i - s = (i - (s + 1)) + 1 by omega] at o1
    obtain ⟨t', ht', d2, n2, h2, o2, -⟩ := back1 hFw hnu hw hy (by omega) h1 o1
    exact ⟨by omega, d2, n2, by rw [show j - (s + 1) = t' by omega]; exact h2, o2⟩

private theorem get_lt {y t : Nat} (h : t < (X.tr y).length) : ∃ e, X.get (y, t) = some e :=
  ⟨_, List.getElem?_eq_getElem h⟩

/-- The event of a state of the output sequence has the state's kind. -/
private theorem ev_of (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {t : Nat} {d : Wg0.Control.D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    {p : Fin 4 × Nat} (ho : Wg0.opos d = some p) {e : Event} (he : X.get (y, t) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) :
    Wg0.EvK P L y (warpW L y) d e ∧ (∀ f, e.kind ≠ .ub f) ∧ e.pc = d.site.pc := by
  obtain ⟨σ, hσ', hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  rw [hσ] at hσ'
  cases hσ'
  have hpc' : e.pc = d.site.pc := hpc
  have hr := Wg0.opos_pc ho
  obtain ⟨d', n', h, -, hE, -⟩ := wg0_state hJ hi hev hpc (by omega)
  simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨hE.2, hub, hpc'⟩

/-- The warp word is at most `1` exactly in warps 0 and 1. -/
private theorem warpW_le1 (hp : Pre P L m) {g : Nat}
    (h : scmpi .gt .s (warpW L g) 1 = false) : warp L g < 2 := by
  have hw : warp L g = warpOf L g := by
    simp only [warp, warpOf, tidOf_x_eq hp, tidOf_eq hp]
  have hl := warpOf_lt hp (g := g)
  rw [hw]
  simp only [warpW] at h
  generalize warpOf L g = k at hl h ⊢
  interval_cases k <;> simp_all (config := { decide := true })

/-- The barrier-9 count before the barrier of chunk `c` of a lane of warps 0–3. -/
private theorem obar_cnt (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : NoUbInner L X) {y t : Nat} (hw : warp L y < 4) (hy : y < L.threads)
    {d : Wg0.Control.D} {n : Cls → Nat} {c : Fin 4}
    (ht : t < (X.tr y).length)
    (hσ : Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    (hs : d.site = .obar c) :
    ((X.tr y).take t).countP (Execution.isBarId 9) = 2 * blocksOf P L (y / L.block) + 2 + c := by
  rcases w0_bst_pre hFw (LaneUbFree.of_inner hnu hw ht) hw hy hσ with
    ⟨_, _, h, -⟩ | ⟨d', n', h, hC, hL, -, hB⟩
  · cases h
  simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  obtain ⟨rfl, -⟩ := h
  have hsb : d.site.isBar = true := by rw [hs]; rfl
  have hO : Wg0.barOrd d = 3 * blocksOf P L (y / L.block) + 2 + c := by
    rcases Wg0.bar_ord hsb hC hL with ⟨hr, -⟩ | ⟨-, ho⟩
    · rw [hs] at hr; cases hr
    · rw [ho, hs]; simp only [Wg0.Site.bidx]; omega
  rw [w0_idCnt hp hX hFw hw (le_refl 9) (by omega) t (LaneUbFree.of_inner hnu hw ht), w0BarCnt,
    Wg0.barTot]
  simp only [Wg0.barTot] at hB
  rw [hB, hO, Nat.add_assoc, w0Cnt9_epi _ _ _ (by omega)]
  omega

/-! ### The facts -/

/-- **An exiting lane of warpgroup 0 made at least `2 R + 6` barrier-9 events.** -/
theorem wg0_outExit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {y j pcx : Nat} (hw : warp L y < 4)
    (he : X.get (y, j) = some ⟨pcx, .exit⟩) :
    2 * blocksOf P L (y / L.block) + 6 ≤ (X.tr y).countP (Execution.isBarId 9) := by
  have hy := Frame.lt_of_get hX he
  have hal := LaneUbFree.of_exit hX hy he
  have hB : 3 * blocksOf P L (y / L.block) + 7 ≤ w0BarCnt X y (X.tr y).length := by
    by_contra hlt
    exact (w0_lagB hp hX hFw hw hy (B := 3 * blocksOf P L (y / L.block) + 6) le_rfl
      (by omega) hal).1 j pcx he
  have hc := w0_idCnt hp hX hFw hw (le_refl 9) (by omega) (X.tr y).length hal
  rw [List.take_length] at hc
  rw [hc]
  have h1 := w0IdCnt_mono (R := blocksOf P L (y / L.block)) (p := warp L y % 2) (id := 9) hB
  rw [w0Cnt9_epi _ _ _ (le_refl 7)] at h1
  omega

/-- **The state at a barrier-9 event of ordinal `2 R + 2 + c`** of a lane of warpgroup 0 is
the chunk's named barrier `obar c`. -/
private theorem obar_state (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {y j pc c : Nat} {cnt : Option Nat} {md : BarMode}
    (hy : y < L.threads) (hw : warp L y < 4) (hc : c < 4)
    (he : X.get (y, j) = some ⟨pc, .bar 9 cnt md⟩)
    (hcnt : ((X.tr y).take j).countP (Execution.isBarId 9) =
      2 * blocksOf P L (y / L.block) + 2 + c) :
    ∃ (d : Wg0.Control.D) (n : Cls → Nat),
      Frame.stateAt (thread P L) X y j = some (some (.inr ⟨.inl .wg0, d⟩, n)) ∧
        d.site = .obar ⟨c, hc⟩ := by
  have hub : ∀ f, Kind.bar 9 cnt md ≠ .ub f := fun _ h => by cases h
  have hr : 103 ≤ pc ∧ pc < 1842 := w0_barPc hp hX hFw hw he (le_refl 9)
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, hE, -⟩ := wg0_state hJ hi hev hpc hr
  obtain ⟨-, -, hI⟩ := w0_atBar hp hX hFw hw he hr.1 hσ
  rcases w0_bst hFw hnu hw hy hσ with ⟨_, _, h, -⟩ | ⟨d', n', h, hC, hL, -, hB⟩
  · cases h
  simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  obtain ⟨rfl, -⟩ := h
  have hsb : d.site.isBar = true := Wg0.isBar_of_pc ((Wg0.evK_bar hub hE.2 rfl).imp
    (fun h => h.1) fun h => h.imp (fun h => h.1) fun h => h.1)
  rw [w0_idCnt hp hX hFw hw (le_refl 9) (by omega) j hnu] at hcnt
  have hB' := cnt9_inj hc hI.symm hcnt
  simp only [w0BarCnt, Wg0.barTot] at hB' hB
  rw [hB] at hB'
  refine ⟨d, n, hσ, ?_⟩
  rcases Wg0.bar_ord hsb hC hL with ⟨-, hbx, r, hrR, ho⟩ | ⟨hreg, ho⟩
  · omega
  · exact Wg0.obar_site hc hsb hreg (by omega)

/-- **Before its barrier-9 event of ordinal `2 R + 2 + c`** a lane of warpgroup 0 made its proxy
fence and before it its 32 staging stores of chunk `c`. -/
theorem wg0_outStage (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {y j pc c : Nat} (hy : y < L.threads)
    (hw : warp L y < 4) (hc : c < 4) (he : X.get (y, j) = some ⟨pc, .bar 9 (some 128) .sync⟩)
    (hcnt : ((X.tr y).take j).countP (Execution.isBarId 9) =
      2 * blocksOf P L (y / L.block) + 2 + c) :
    ∃ f < j, X.IsProxyFence (y, f) (.async (some (.shared .cta))) none ∧
      ∀ k < 8, ∀ el < 4, ∃ i < f, ∃ a bs, X.Writes (y, i) a bs ∧ a.size = 4 ∧
        a.loc = wsLoc L (y / L.block) (65536 + 16384 * ((L.tidOf y).x / 64) +
          128 * ((L.tidOf y).x % 64) + 16 * (k ^^^ (L.tidOf y).x % 8) + MemRow.wg0OutOff c +
          4 * el) := by
  have hjl : j < (X.tr y).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨d, n, hσ, hs⟩ := obar_state hp hX hFw hnu hy hw hc he hcnt
  have ho : Wg0.opos d = some (⟨c, hc⟩, 33) := by simp [Wg0.opos, hs]
  have hW := walk hFw hnu hw hy hjl hσ ho
  have ht : tidOf L y < 128 := MemRow.wg0_tid hw
  obtain ⟨hj1, d1, n1, hσ1, ho1⟩ := hW 1 (by omega)
  obtain ⟨e1, he1⟩ := get_lt (X := X) (y := y) (t := j - 1) (by omega)
  obtain ⟨hE1, -⟩ := ev_of hp hX hFw hσ1 ho1 he1 (noUb_kind hnu he1)
  have hs1 : d1.site = .ofpx ⟨c, hc⟩ := by
    rcases Wg0.opos_inv ho1 with ⟨k, -, h⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · have := k.isLt; omega
    · exact h
    all_goals omega
  refine ⟨j - 1, by omega, ⟨e1.pc, ?_⟩, fun k hk el hel => ?_⟩
  · unfold Wg0.EvK at hE1
    rw [hs1] at hE1
    rw [he1, ← hE1]
  obtain ⟨hsj, d2, n2, hσ2, ho2⟩ := hW (33 - (4 * k + el)) (by omega)
  obtain ⟨e2, he2⟩ := get_lt (X := X) (y := y) (t := j - (33 - (4 * k + el))) (by omega)
  obtain ⟨hE2, hub2⟩ := ev_of hp hX hFw hσ2 ho2 he2 (noUb_kind hnu he2)
  rcases Wg0.opos_inv ho2 with ⟨k', hs2, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  rotate_left
  all_goals try omega
  obtain ⟨hel2, ⟨a, bs, hk2, ha, hl⟩ | ⟨f, hf⟩⟩ := Wg0.ost2_acc hp ht hs2 hE2
  · have hkk : k'.val = k := by omega
    have hee : d2.el = el := by omega
    refine ⟨j - (33 - (4 * k + el)), by omega, a, bs, ⟨e2.pc, ?_⟩, ha, ?_⟩
    · rw [he2, ← hk2]
    · rw [hl, hkk, hee]
      rfl
  · exact absurd hf (hub2.1 f)

/-- **A tensor store** is chunk `c`'s of a lane of warps 0 and 1, reading the slots of its tile,
two events after its barrier-9 event of ordinal `2 R + 2 + c`, right after its election, which
named the lane itself. -/
theorem wg0_outKey (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : NoUbInner L X) {g k a : Nat} {s : TensorStore.Spec}
    (hi : X.TensorStoreIssue (g, k) a s) :
    warp L g < 2 ∧ ∃ c < 4, (∀ slot, ∃ h < 64, ∃ k < 8, ∃ el < 4, ∃ y < 4,
      s.sharedLoc slot = wsLoc L (g / L.block) (65536 + 16384 * warp L g + MemRow.wg0OutOff c +
        (128 * h + 16 * (k ^^^ h % 8) + 4 * el + y))) ∧
      ∃ j pc, k = j + 2 ∧ X.get (g, j) = some ⟨pc, .bar 9 (some 128) .sync⟩ ∧
        ((X.tr g).take j).countP (Execution.isBarId 9) =
          2 * blocksOf P L (g / L.block) + 2 + c ∧
        X.get (g, k) = some ⟨[1358, 1516, 1673, 1831].getD c 0, .tensorStore a s⟩ ∧
        ∃ pce inst, X.get (g, j + 1) = some ⟨pce, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩ := by
  obtain ⟨pci, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  have hkl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hr := store_pc hX he rfl
  have hub : ∀ f, Kind.tensorStore a s ≠ .ub f := fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, hE, hw⟩ := wg0_state hJ hi hev hpc hr
  obtain ⟨c, hs⟩ := Wg0.otma_of_ev hE.2 rfl
  have ho : Wg0.opos d = some (c, 34 + 1) := by simp [Wg0.opos, hs]
  obtain ⟨t1, rfl, d1, n1, hσ1, ho1, -, e1, he1, hS1⟩ := back1 hFw hnu hw hg hkl hσ ho
  have hs1 : d1.site = .oel c := by
    rcases Wg0.opos_inv ho1 with ⟨k, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · have := k.isLt; omega
    all_goals first | exact h | omega
  obtain ⟨t2, rfl, d2, n2, hσ2, ho2, hW, -⟩ := back1 hFw hnu hw hg (by omega) hσ1 ho1
  have hs2 : d2.site = .obar c := by
    rcases Wg0.opos_inv ho2 with ⟨k, -, h⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · have := k.isLt; omega
    all_goals first | exact h | omega
  have hw2 := warpW_le1 hp (hW hs1)
  obtain ⟨e2, he2⟩ := get_lt (X := X) (y := g) (t := t2) (by omega)
  obtain ⟨hE2, -⟩ := ev_of hp hX hFw hσ2 ho2 he2 (hnu.kind hw he2 (by omega))
  unfold Wg0.EvK at hE2
  rw [hs2] at hE2
  obtain ⟨c', hc', hpc', hsl⟩ := wg0_tensorStore_slot hp hX hFw he ⟨hw, hr⟩ rfl
  have hcc : c' = c.val := by
    have h1 : pci = Wg0.Site.pc (.otma c) := by rw [← hs]; exact hpc
    rw [h1] at hpc'
    simp only [Wg0.Site.pc] at hpc'
    have := c.isLt
    interval_cases c' <;> fin_cases c <;> simp_all
  subst hcc
  have hpcs : pci = [1358, 1516, 1673, 1831].getD c.val 0 := by
    rw [← hpc']
  obtain ⟨hE1, hu1⟩ := ev_of hp hX hFw hσ1 ho1 he1 (hnu.kind hw he1 (by omega))
  unfold Wg0.EvK at hE1
  rw [hs1] at hE1
  obtain ⟨inst, ld, hk1⟩ : ∃ inst ld, e1.kind = .elect (2 ^ 32 - 1) inst ld := by
    rcases hE1 with h | ⟨f, hf⟩
    · exact h
    · exact (hu1.1 f hf).elim
  have hld := Wg0.oel_leader hS1 hs1 hs hk1
  refine ⟨hw2, c.val, c.isLt, hsl, t2, e2.pc, rfl, by rw [he2, ← hE2], ?_, by rw [← hpcs]; exact he,
    e1.pc, inst, ?_⟩
  · exact obar_cnt hp hX hFw hnu hw hg (by omega) hσ2 hs2
  · rw [he1]
    obtain ⟨pc1, kd⟩ := e1
    simp only at hk1 ⊢
    rw [hk1, hld]

/-- **A tensor store** is chunk `c`'s of a lane of warps 0 and 1, reading the slots of its tile,
after its barrier-9 event of ordinal `2 R + 2 + c`. -/
theorem wg0_outIssue (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : NoUbInner L X) {g k a : Nat} {s : TensorStore.Spec}
    (hi : X.TensorStoreIssue (g, k) a s) :
    warp L g < 2 ∧ ∃ c < 4, (∀ slot, ∃ h < 64, ∃ k < 8, ∃ el < 4, ∃ y < 4,
      s.sharedLoc slot = wsLoc L (g / L.block) (65536 + 16384 * warp L g + MemRow.wg0OutOff c +
        (128 * h + 16 * (k ^^^ h % 8) + 4 * el + y))) ∧
      ∃ j pc, j < k ∧ X.get (g, j) = some ⟨pc, .bar 9 (some 128) .sync⟩ ∧
        ((X.tr g).take j).countP (Execution.isBarId 9) =
          2 * blocksOf P L (g / L.block) + 2 + c := by
  obtain ⟨hw, c, hc, hsl, j, pc, hk, hj, hcnt, -⟩ := wg0_outKey hp hX hFw hnu hi
  exact ⟨hw, c, hc, hsl, j, pc, by omega, hj, hcnt⟩

/-! ### The election and the store of chunk `c` -/

/-- The warp word is at most `1` in warps 0 and 1. -/
private theorem warpW_lt2 (hp : Pre P L m) {g : Nat} (h : warp L g < 2) :
    scmpi .gt .s (warpW L g) 1 = false := by
  have hw : warp L g = warpOf L g := by
    simp only [warp, warpOf, tidOf_x_eq hp, tidOf_eq hp]
  have hl := warpOf_lt hp (g := g)
  rw [hw] at h
  simp only [warpW]
  generalize warpOf L g = k at hl h ⊢
  interval_cases k <;> simp_all (config := { decide := true })

/-- **The `n`-th element satisfying `p`** of a list with more than `n` of them. -/
private theorem nth_countP {α : Type} (p : α → Bool) :
    ∀ (l : List α) {n : Nat}, n < l.countP p →
      ∃ j a, l[j]? = some a ∧ p a = true ∧ (l.take j).countP p = n
  | [], n, h => by simp at h
  | a :: t, n, h => by
    by_cases hp : p a = true
    · rcases n with _ | n
      · exact ⟨0, a, rfl, hp, rfl⟩
      · rw [List.countP_cons_of_pos hp] at h
        obtain ⟨j, b, hj, hb, hc⟩ := nth_countP p t (by omega : n < t.countP p)
        exact ⟨j + 1, b, hj, hb, by simp [List.countP_cons_of_pos hp, hc]⟩
    · rw [List.countP_cons_of_neg hp] at h
      obtain ⟨j, b, hj, hb, hc⟩ := nth_countP p t h
      exact ⟨j + 1, b, hj, hb, by simp [List.countP_cons_of_neg hp, hc]⟩

/-- **One step forward** of a lane in warpgroup 0's machine along its event at `t`. -/
private theorem step_fwd {y t : Nat} {d d' : Wg0.Control.D} {n : Cls → Nat} {e : Event}
    (hσ : Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    (he : (X.tr y)[t]? = some e)
    (hs : Wg0.Control.succ P L y (warpW L y) d e = some (some d')) :
    ∃ n', Frame.stateAt (thread P L) X y (t + 1) = some (some (.inr ⟨.inl .wg0, d'⟩, n')) := by
  rw [Frame.stateAt_succ he, hσ]
  have h : (frag P L y .wg0).next d e = some (some d') := hs
  refine ⟨Code.bump cls n e, ?_⟩
  change (thread P L y).next (.inr ⟨.inl .wg0, d⟩, n) e = _
  rw [next_frag, h]
  rfl

/-- **The election and, for its leader, the store of chunk `c`** (complete execution): a lane of
warp 0 or 1 has a barrier-9 event `j` of ordinal `2 R + 2 + c`, then an election, and if it is the
elected lane the tensor store of chunk `c`. -/
private theorem out_elect (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hC : Complete L X) {y c : Nat}
    (hy : y < L.threads) (hw : warp L y < 2) (hc : c < 4) :
    ∃ j pce inst ld, X.get (y, j + 1) = some ⟨pce, .elect (2 ^ 32 - 1) inst ld⟩ ∧
      (PTX.laneOf L y = ld → ∃ a s, X.get (y, j + 2) =
        some ⟨[1358, 1516, 1673, 1831].getD c 0, .tensorStore a s⟩) := by
  have hw4 : warp L y < 4 := by omega
  obtain ⟨kx, pcx, hkx, hexit⟩ := Frame.Complete.exit_last hC hy (noCanceled hX y)
  have hcnt := wg0_outExit hp hX hFw hw4 hexit
  obtain ⟨j, b, hj, hb, hcj⟩ := nth_countP (Execution.isBarId 9) (X.tr y)
    (n := 2 * blocksOf P L (y / L.block) + 2 + c) (by omega)
  obtain ⟨pcb, kd⟩ := b
  obtain ⟨cnt, md, rfl⟩ : ∃ cnt md, kd = .bar 9 cnt md := by
    cases kd <;> simp [Execution.isBarId] at hb
    rename_i i cnt md
    exact ⟨cnt, md, by rw [hb]⟩
  have hget : X.get (y, j) = some ⟨pcb, .bar 9 cnt md⟩ := hj
  obtain ⟨d, n, hσ, hs⟩ := obar_state hp hX hFw hnu hy hw4 hc hget hcj
  have hjx : j < kx := by
    by_contra hge
    have hl := (List.getElem?_eq_some_iff.mp hj).1
    have : j = kx := by omega
    subst this
    rw [hget] at hexit
    cases hexit
  -- the election
  obtain ⟨n1, hσ1⟩ := step_fwd hσ hj (d' := { d with site := .oel ⟨c, hc⟩ }) (by
    simp only [Wg0.Control.succ, hs, Wg0.Control.afterObar, warpW_lt2 hp hw]
    rfl)
  have ho1 : Wg0.opos { d with site := .oel ⟨c, hc⟩ } = some (⟨c, hc⟩, 34) := rfl
  obtain ⟨e1, he1⟩ := get_lt (X := X) (y := y) (t := j + 1) (by omega)
  obtain ⟨hE1, hu1, -⟩ := ev_of hp hX hFw hσ1 ho1 he1 (noUb_kind hnu he1)
  obtain ⟨inst, ld, hk1⟩ : ∃ inst ld, e1.kind = .elect (2 ^ 32 - 1) inst ld := by
    rcases hE1 with h | ⟨f, hf⟩
    · exact h
    · exact (hu1 f hf).elim
  refine ⟨j, e1.pc, inst, ld, by rw [he1]; obtain ⟨p1, k1⟩ := e1; simp only at hk1; rw [hk1],
    fun hl => ?_⟩
  have hj1 : j + 1 < kx := by
    by_contra hge
    have : j + 1 = kx := by omega
    subst this
    rw [he1] at hexit
    cases hexit
    simp at hk1
  obtain ⟨n2, hσ2⟩ := step_fwd hσ1 he1 (d' := { d with site := .otma ⟨c, hc⟩ }) (by
    simp only [Wg0.Control.succ, hk1, hl]
    rfl)
  have ho2 : Wg0.opos { d with site := .otma ⟨c, hc⟩ } = some (⟨c, hc⟩, 35) := rfl
  obtain ⟨e2, he2⟩ := get_lt (X := X) (y := y) (t := j + 2) (by omega)
  obtain ⟨hE2, hu2, hpc2⟩ := ev_of hp hX hFw hσ2 ho2 he2 (noUb_kind hnu he2)
  obtain ⟨a, s, hk2, -⟩ : ∃ a s, e2.kind = .tensorStore a s ∧ True := by
    rcases hE2 with ⟨a, s, h, -⟩ | ⟨f, hf⟩
    · exact ⟨a, s, h, trivial⟩
    · exact (hu2 f hf).elim
  refine ⟨a, s, ?_⟩
  obtain ⟨p2, k2⟩ := e2
  simp only at hk2 hpc2
  rw [he2, hk2, hpc2]
  simp only [Wg0.Site.pc]

/-- **The store of chunk `c` exists** (complete execution): in every CTA of the grid, warp `w < 2`
has a lane whose tensor store of chunk `c < 4` is an event (the elected lane). -/
theorem wg0_outStore (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hC : Complete L X) {c0 w c : Nat}
    (hc0 : c0 * L.block < L.threads) (hw : w < 2) (hc : c < 4) :
    ∃ g k a s, g / L.block = c0 ∧ warp L g = w ∧
      X.get (g, k) = some ⟨[1358, 1516, 1673, 1831].getD c 0, .tensorStore a s⟩ := by
  have hb : L.block = 384 := hp.block
  have hwp : ∀ g, warp L g = g % 384 / 32 := fun g => by
    simp only [warp, tidOf_x_eq hp]
  have hth : L.threads = L.grid * 384 := by simp only [Launch.threads, hb]
  have hcb : c0 * L.block = c0 * 384 := by rw [hb]
  have hcg : c0 < L.grid := by omega
  have hy0 : c0 * L.block + 32 * w < L.threads := by omega
  have hy0w : warp L (c0 * L.block + 32 * w) = w := by rw [hwp, hb]; omega
  obtain ⟨j0, pce0, inst0, ld, he0, -⟩ := out_elect hp hX hFw hnu hC (c := c) hy0
    (by omega) hc
  have hld : ld < 32 := (hX.elect.1 _ _ _ _ _ he0).2.2.1
  have hyc : (c0 * L.block + 32 * w + ld) / L.block = c0 := by rw [hb]; omega
  have hyt : c0 * L.block + 32 * w + ld < L.threads := by omega
  have hyw : warp L (c0 * L.block + 32 * w + ld) = w := by rw [hwp, hb]; omega
  have hyl : PTX.laneOf L (c0 * L.block + 32 * w + ld) = ld := by
    simp only [PTX.laneOf, hb]
    omega
  obtain ⟨j, pce, inst, ld', he, hst⟩ := out_elect hp hX hFw hnu hC (c := c) hyt
    (by omega) hc
  have hsame : SameWarp L (c0 * L.block + 32 * w + ld) (c0 * L.block + 32 * w) :=
    ⟨⟨hyt, hy0, by rw [hb]; omega⟩, by rw [hb]; omega⟩
  have hld' : ld' = ld := elect_leader hX (e := (c0 * L.block + 32 * w + ld, j + 1))
      (f := (c0 * L.block + 32 * w, j0 + 1)) he he0 hsame
  obtain ⟨a, s, hk⟩ := hst (by rw [hld', hyl])
  exact ⟨_, j + 2, a, s, hyc, hyw, hk⟩
