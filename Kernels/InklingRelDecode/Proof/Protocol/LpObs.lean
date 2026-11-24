-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.LpKv
public import Kernels.InklingRelDecode.Proof.Protocol.LpReach
public import Kernels.InklingRelDecode.Proof.Interface.RsMmaBack
public import Kernels.InklingRelDecode.Proof.Protocol.IpLifeCopy

@[expose] public section

/-!
# Every tensor load of an exited CTA is observed (`Life.CopyObserved`)

A copy issue completes on `kv_ready t` of its CTA `c` (`copy_mbar`). In the slot of `LpKv` it is an
item of use `u = copyUse`, and `3 u + t` is its block, below `num_iters` (`copy_use_lt`). If the
CTA exited, the MMA warp's lead thread exited: it passed the role's last site, where its successful
polls of `kv_ready t` number the blocks of the slot below `num_iters` (`Ring.mma_counts_exec`,
`Interface.fin_iter`), more than `u`; it issued an MMA (`Interface.exists_pv7`), so it is the
package's committing lane `G.cm c`, the slot's consumer. Its poll with `u` earlier ones observes
the copy (`Ring.Kv.copy_observed`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- An observed tensor-load notification is present and observed by the wait on the copy's
mbarrier. -/
theorem obs_load {i w : EvId} {acq : Bool} {ws : MbarScope} {pc a : Nat}
    {sp : TensorCopy.Spec} (he : X.get i = some ⟨pc, .tensorIssue a sp⟩)
    (h : AsyncObserved X i (.notify .load) w acq ws) :
    X.AsyncPresent i (.notify .load) ∧
      WaitObserves X (.async i (.notify .load)) w sp.mbar acq ws := by
  obtain ⟨n, m, hn, hw⟩ := h
  obtain ⟨rfl, o, a', ho, ⟨pc', hti⟩, hm, hnot⟩ := hn
  rw [he] at hti
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hti
  obtain ⟨-, -, hsp⟩ := hti
  refine ⟨⟨o, ho, hnot⟩, ?_⟩
  rw [hsp, hm]
  exact hw

/-- **A tensor copy completes on `kv_ready t` of its own CTA.** -/
theorem copy_mbar (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩) :
    ∃ t < 3, sp.mbar = kvReady L (g / L.block) t := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  rcases copy_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨a, sp, rfl⟩ with
    ⟨d, hσ, i, hi, hs', a', s', hev, -, -, h3, -⟩ | ⟨d, P, hσ, hsh⟩
  · simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
    obtain ⟨-, -, rfl⟩ := hev
    exact ⟨i / 4 % 3, Nat.mod_lt _ (by omega), h3⟩
  · have hcp : Ring.Ld.isCp d.site = true := by
      unfold EvW.LdShape at hsh
      cases hst : d.site <;> rw [hst] at hsh <;> simp at hsh <;> rfl
    obtain ⟨b, -, hev⟩ := Ring.ldShape_cp hsh hcp
    simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
    obtain ⟨-, -, rfl⟩ := hev
    exact ⟨d.i % 3, Nat.mod_lt _ (by omega), rfl⟩

/-- **A thread of warp 7 that exited has an MMA state at `setMaxRegInc`.** -/
theorem exists_setMaxRegInc (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hw7 : g % L.block / 32 = 7)
    (hex : ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩) :
    ∃ j d P, j < (X.tr g).length ∧ St Q L X g j = some (some (.w (.mma d P))) ∧
      d.site = .setMaxRegInc := by
  obtain ⟨kx, pcx, hgetx, hx⟩ := Rr.exit_of_last hX hf hex
  have hkx : kx < (X.tr g).length := len_of_get hgetx
  obtain ⟨x, hσx⟩ : ∃ x : WComp.ExitD, St Q L X g kx = some (some (.w (.exit x))) := by
    rcases hx with ⟨d, hσ, -⟩ | ⟨x, hσ, -⟩
    · exfalso
      obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX hgetx hσ
      have : IsDefault L g := hinv.1
      unfold IsDefault at this
      omega
    · exact ⟨x, hσ⟩
  obtain ⟨j, b, hj, hσj, hwr⟩ := exists_wrap hpre hX hf hR hkx hσx
  have hrw := roleWarp_inv hf.roleWarp j _ (by omega) hσj
  cases b with
  | idle d =>
    simp only [RoleWarp, roleWarp] at hrw
    omega
  | loader d P =>
    simp only [RoleWarp, roleWarp] at hrw
    omega
  | mma d P =>
    refine ⟨j, d, P, by omega, hσj, ?_⟩
    simp only [wrap] at hwr
    split at hwr
    · assumption
    · cases hwr
  | worker w => simp [wrap] at hwr
  | exit x => simp [wrap] at hwr

/-- The number of blocks of a split is at most `2 ^ 24`. -/
theorem numIters_le24 (hpre : Pre Q L mem0) {r : Nat} (hr : r < Q.b) (s : Nat) :
    Q.numIters r s ≤ 2 ^ 24 := by
  have h1 := SmEntry.iters_lt Q r s hpre.splitsPos
  have h2 := hpre.seqRange r hr
  unfold Params.blocks at h1
  omega

/-- The CTA coordinates of two threads of one CTA agree. -/
theorem cta_same {h : Nat} (hc : h / L.block = g / L.block) (d : Dim) :
    ProA.cta L h d = ProA.cta L g d := by
  unfold ProA.cta
  rw [hc]

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X)
  (hb : BaseWordRead L X) (hn : NumWordRead Q L X) (G : Sr.SrPkg L kernel asms mem0 X)

include hpre hX hf hR hb hn in
/-- **In an exited CTA the committing lane has polled every slot for each of its blocks.** For a
CTA `c` that exited, with `1 ≤ num_iters`, the lane `G.cm c` has at least `below t num_iters`
successful polls of `kv_ready t`. -/
theorem mma_polls_exited (hMB : Mma.MmaBcast L X) {c : Nat} (hc : c < L.grid)
(hx : CtaExited L X c) {t : Nat}
    (ht : t < 3) {g0 : Nat} (hg0 : g0 < L.threads) (hgc : g0 / L.block = c)
    (h1 : 1 ≤ Q.numIters (ProA.cta L g0 .z) (ProA.cta L g0 .x)) :
    Ring.below t (Q.numIters (ProA.cta L g0 .z) (ProA.cta L g0 .x)) ≤
      okPolls (kvReady L c t) (X.tr (G.cm c)) := by
  have hbk := hpre.block
  have hth : L.threads = L.grid * L.block := rfl
  have hg7 : c * L.block + 224 < L.threads := by rw [hth, hbk]; nlinarith
  obtain ⟨h7, hw, hlead⟩ := exists_lead hX hbk hg7
  obtain ⟨⟨-, hh7, hcta⟩, hwarp⟩ := hw
  have hc7 : h7 / L.block = c := by rw [← hcta, hbk]; omega
  have hw7 : h7 % L.block / 32 = 7 := by rw [← hwarp, hbk]; omega
  obtain ⟨j, d, P, hj, hσ, hs⟩ := exists_setMaxRegInc hpre hX hf hR hw7 (hx h7 hh7 hc7)
  have hz := cta_same (L := L) (hc7.trans hgc.symm) .z
  have hxx := cta_same (L := L) (hc7.trans hgc.symm) .x
  have hdn : d.n = Q.numIters (ProA.cta L g0 .z) (ProA.cta L g0 .x) := by
    have := mma_iters hpre hX hf hb hn (m := (h7, j)) ⟨P, hσ⟩ (by rw [hs]; nofun)
      (by rw [hs]; nofun)
    rw [this]
    unfold Result.Mma.reqOf Result.Mma.splitOf
    rw [hz, hxx]
  obtain ⟨-, -, hzb⟩ := ProA.cta_lt hpre hg0
  have h24 := numIters_le24 hpre hzb (ProA.cta L g0 .x)
  have hfin := fin_iter hX hlead j hj hσ (by unfold FinSite; rw [hs]; simp) (by omega)
    (by omega)
  obtain ⟨hw4, k0, d0, hk0, h0, hd, hs0, hin, hC, hPl⟩ := mma_anchor_full hpre hX hf hR hj hσ
  have hp0 : Ring.Mm.polled d0 = 0 := by simp [Ring.Mm.polled, hs0]
  have hdn0 : Ring.Mm.done d0 = 0 := by simp [Ring.Mm.done, hs0]
  have hbc := Interface.bcast_of_mma hf.roleWarp hMB hh7 hj.le hσ
  have hcnt := (Ring.mma_counts_exec hpre hw4 hh7 hX hk0 hj h0 hd hin hp0 hdn0 ht
    (hlead.take j) (hbc.take j) (hPl _) (hC _)).1
  have hpol : Ring.Mm.polled d = d.n := by
    have hi0 : d.i ≠ 0 := by omega
    simp [Ring.Mm.polled, hs, hi0]
  rw [hpol, hdn, hc7] at hcnt
  -- the lane issued an MMA, so it is the package's committing lane
  obtain ⟨k', d', -, -, -, -, -, -, ⟨pc, dst, sp, acc, mask, hev⟩, -⟩ :=
    exists_pv7 hpre hX hf hlead hbc (i0 := 1) le_rfl j hj hσ (.inl (by omega))
  have hcm : h7 = G.cm c := (G.lane c hc).mma_thread (x := (h7, k'))
    ⟨dst, sp, acc, mask, pc, hev⟩ hc7
  rw [← hcm, ← hcnt]
  exact (List.take_sublist j _).countP_le

include hpre hX hf hR hp hn in
/-- **The use of a copy is below the blocks of its slot**: `3 u + t < num_iters`. -/
theorem copy_use_lt {c t : Nat} (ht : t < 3) {pArr : EvId} {pCp : Fin 8 → EvId}
    (hP : PreSlot Q L X c t pArr pCp) (cm : Nat) {k pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩) (hm : sp.mbar = kvReady L c t) :
    g / L.block = c ∧ 3 * Ring.Kv.copyUse X (slotOf Q L X c t cm pArr pCp) (g, k) + t <
      Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := len_of_get he
  obtain ⟨-, hgc, hcase⟩ := copy_kvReady hpre hX hf he hm
  refine ⟨hgc, ?_⟩
  have hnpe : npOf Q L c = ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x) := by
    rw [← hgc]; rfl
  have hle : ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x) ≤
      Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
    unfold ProA.numPre; omega
  rcases hcase with ⟨d, hσ⟩ | ⟨d, P, hσ, hcp⟩
  · obtain ⟨⟨i, hi⟩, hnp⟩ := hP.cp he hm hσ
    have hu : Ring.Kv.copyUse X (slotOf Q L X c t cm pArr pCp) (g, k) = 0 := by
      have hcond : (slotOf Q L X c t cm pArr pCp).δ = 1 ∧
          ∃ i, (g, k) = (slotOf Q L X c t cm pArr pCp).pCp i := ⟨by simp [slotOf, hnp], i, hi⟩
      unfold Ring.Kv.copyUse
      simp only [hcond, and_self, ↓reduceIte]
    omega
  · have hnot : ¬ ∃ i : Fin 8, (g, k) = pCp i := by
      rintro ⟨i, hi⟩
      have h1 := (hP.cp_thr i).2
      rw [← hi] at h1
      have := loader_warp hf.roleWarp hk.le hσ
      simp only at h1
      omega
    have hnpre : ¬ PreSite d.site := by
      intro h; rcases h with h | h | h <;> rw [h] at hcp <;> cases hcp
    obtain ⟨hw, k0, d0, hk0, h0, hd, hs0, hi0, hin, -, hPl, hC⟩ :=
      loader_anchor hpre hX hf hR hp hk hσ hnpre
    have hlead := electLead_of_elected hX (copy_lead hX k hk hσ hcp)
    have hm' : sp.mbar = kvReady L (g / L.block) t := by rw [hgc]; exact hm
    obtain ⟨-, -, -, -, -, hblk, -⟩ := Ring.loader_copy_exec hpre hw hg hX hk0 h0 hd
      (hf.ldRng hg hσ) hin hs0
      (by rw [hi0]; exact numPre_le _ _ _) ht (hlead.take k) (hC _) (hPl _) he hm'
    have hI := (loader_inv_at hX hf hk hσ).1
    have hlt : d.i < d.n := (hf.ldRng hg hσ).loop (by
      rcases hst : d.site <;> rw [hst] at hcp <;> first | (cases hcp; done) | rfl)
    have hdn : d.n = Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) :=
      (page_inv hpre hX hf hn k _ hσ).1 (by
        rcases hst : d.site <;> rw [hst] at hcp <;> first | (cases hcp; done) | rfl)
    have hu : Ring.Kv.copyUse X (slotOf Q L X c t cm pArr pCp) (g, k) =
        ((X.tr g).take k).countP (issuesTo (kvReady L c t)) / 8 +
          (if t < npOf Q L c then 1 else 0) := by
      have hcond : ¬ ((slotOf Q L X c t cm pArr pCp).δ = 1 ∧
          ∃ i, (g, k) = (slotOf Q L X c t cm pArr pCp).pCp i) := fun h => hnot h.2
      unfold Ring.Kv.copyUse
      simp only [hcond, ↓reduceIte]
      rfl
    rw [hu, hnpe]
    rw [hgc, hi0] at hblk
    unfold Ring.loaderBlock Ring.loaderUse Ring.blockOf at hblk
    split at hblk <;> split <;> omega

include hpre hX hf hR hp hb hn G in
/-- **`Life.CopyObserved`**: every tensor load whose mbarrier's CTA exited is observed by a poll of
the CTA's committing MMA lane, given the prologue's events on the ring (`PreRing`). -/
theorem copyObserved_of (hMB : Mma.MmaBcast L X) (hpr : PreRing Q L X) :
    Life.CopyObserved L X := by
  intro g k pc a s he hx
  obtain ⟨t, ht, hm⟩ := copy_mbar hpre hX hf he
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hc : g / L.block < L.grid := ProA.grid_lt hg
  obtain ⟨pArr, pCp, hP⟩ := hpr (g / L.block) hc t ht
  have H := slot_hyp hpre hX hf hR hp G hc ht hP
  obtain ⟨-, hlt⟩ := copy_use_lt hpre hX hf hR hp hn ht hP (G.cm (g / L.block)) he hm
  have hxc : CtaExited L X (g / L.block) := by rw [hm] at hx; exact hx
  have hpol := mma_polls_exited hpre hX hf hR hb hn G hMB hc hxc ht hg rfl (by omega)
  have hpolls : Ring.Kv.copyUse X (slotOf Q L X (g / L.block) t (G.cm (g / L.block)) pArr pCp)
      (g, k) + 1 ≤ okPolls (slotOf Q L X (g / L.block) t (G.cm (g / L.block)) pArr pCp).full
        ((X.tr (slotOf Q L X (g / L.block) t (G.cm (g / L.block)) pArr pCp).cm).take
          (X.tr (G.cm (g / L.block))).length) := by
    show _ ≤ okPolls (kvReady L (g / L.block) t)
      ((X.tr (G.cm (g / L.block))).take (X.tr (G.cm (g / L.block))).length)
    rw [List.take_length]
    unfold Ring.below at hpol
    omega
  obtain ⟨j, pcw, p, acq, sc, -, hew, hcw⟩ := MbarRing.Poll.exists_nth hpolls
  have hobs := Ring.Kv.copy_observed hX H he hm hew hcw
  obtain ⟨hpres, hwo⟩ := obs_load he hobs
  obtain ⟨hcm1, hcm2⟩ := (G.lane (g / L.block) hc).cm_ok
  refine ⟨G.cm (g / L.block), j, true, sc, hcm1, ?_, hpres, hwo⟩
  rw [hm, hcm2]
  rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Lp
