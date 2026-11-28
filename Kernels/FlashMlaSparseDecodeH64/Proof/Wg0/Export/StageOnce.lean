-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.PlaceWalk
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Pred
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Measure
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Objs
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Lemmas.Protocol.UnitHandoff
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.OutSeq

@[expose] public section

/-! # One staging store per site

A lane of warpgroup 0 makes each staging store (chunk `c`, store `k`, element `el`) once: the
machine's place grows along the lane's trace, strictly at an event that counts, so two events at
one site (the same place) are one event (`wg0_stage_once`). With `MemRow.wg0Ost2_inj` two staging
stores of the warpgroup writing one byte are the same event of the same lane. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.MbarRing MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

/-- A site at the pc of a staging store is that store's site. -/
private theorem site_eq_ost2 (s : Wg0.Site)
    (h : ∃ c : Fin 4, ∃ k : Fin 8, s.pc = Wg0.ost2Base c + k.val) :
    ∃ c k, s = .ost2 c k := by
  cases s with
  | ost2 c k => exact ⟨c, k, rfl⟩
  | sld a k => exfalso; revert a k; decide
  | pst k | pld k => exfalso; revert k; decide
  | ost c | rld c | rldw c | rst c | rstw c | old c | oldw c | ofpx c | obar c | oel c
    | otma c => exfalso; revert c; decide
  | _ => exfalso; obtain ⟨c, k, h⟩ := h; revert c k; decide

/-- **The state at a staging store**: site `ost2 c k`, element `el`, its address, and the launch's
length words. -/
private theorem stage_state (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) {i pc : Nat} {a : Acc}
    {bs : List Byte} (h : X.get (y, i) = some ⟨pc, .wr a bs⟩) (hs : MemRow.Wg0Stage L y pc a) :
    ∃ (c : Fin 4) (k : Fin 8) (d : Wg0.Control.D) (n : Cls → Nat),
      Frame.stateAt (thread P L) X y i = some (some (.inr ⟨.inl .wg0, d⟩, n)) ∧
      d.site = .ost2 c k ∧ d.el < 4 ∧
      a.loc = wsLoc L (y / L.block) (65536 + 16384 * (tidOf L y / 64) + 128 * (tidOf L y % 64) +
        16 * (k.val ^^^ tidOf L y % 8) + MemRow.wg0OutOff c.val + 4 * d.el) ∧
      d.l0 = lenWA P L (y / L.block) ∧ d.l1 = lenWB P L (y / L.block) := by
  have hy : y < L.threads := Frame.lt_of_get hX h
  have hub : ∀ f, (⟨pc, .wr a bs⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw h hub
  obtain ⟨c0, hc0, k0, hk0, el0, -, hpc0, -⟩ := hs
  have hr : 103 ≤ pc ∧ pc < 1842 := by
    rcases (by omega : c0 = 0 ∨ c0 = 1 ∨ c0 = 2 ∨ c0 = 3) with rfl | rfl | rfl | rfl <;>
      simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at hpc0 <;> omega
  obtain ⟨d, n, rfl, -, hE, -⟩ := wg0_state hJ hi hev hpc hr
  have hpc' : pc = d.site.pc := hpc
  obtain ⟨c, k, hsite⟩ := site_eq_ost2 d.site ⟨⟨c0, hc0⟩, ⟨k0, hk0⟩, by
    rw [← hpc']
    simpa [Wg0.ost2Base] using hpc0⟩
  have ht : tidOf L y < 128 := MemRow.wg0_tid hw
  obtain ⟨hel, ⟨a', bs', hk', ha, hl⟩ | ⟨f, hf⟩⟩ := Wg0.ost2_acc hp ht hsite hE.2
  · simp only [Kind.wr.injEq] at hk'
    obtain ⟨rfl, -⟩ := hk'
    have hL := w0_bst_pre hFw (noUbBefore_of_get hX h) hw hy hσ
    rcases hL with ⟨d0, n0, h0, -⟩ | ⟨d0, n0, h0, -, hL, -⟩
    · simp at h0
    · simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h0
      obtain ⟨rfl, -⟩ := h0
      obtain ⟨-, -, h1, h2⟩ := hL
      have hn : 2 ≤ d.site.lens := by rw [hsite]; simp [Wg0.Site.lens]
      exact ⟨c, k, d, n, hσ, hsite, hel, hl, h1 (by omega), h2 hn⟩
  · exact absurd hf (hub f)

/-- **Two staging stores of warpgroup 0 covering one byte are one event**: the same lane (the
address determines the thread) and, its states being at one site and element, hence at one
place, the same event of it (the place grows strictly along the lane). -/
theorem wg0_stage_once (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {y y' i i' pc pc' : Nat} (hw : warp L y < 4)
    (hw' : warp L y' < 4) {a a' : Acc} {bs bs' : List Byte} {l : Loc}
    (h : X.get (y, i) = some ⟨pc, .wr a bs⟩) (h' : X.get (y', i') = some ⟨pc', .wr a' bs'⟩)
    (hs : MemRow.Wg0Stage L y pc a) (hs' : MemRow.Wg0Stage L y' pc' a')
    (hc : a.Covers l) (hc' : a'.Covers l) : y = y' ∧ i = i' := by
  have hy : y < L.threads := Frame.lt_of_get hX h
  have hy' : y' < L.threads := Frame.lt_of_get hX h'
  obtain ⟨c, k, d, n, hσ, hsite, hel, hloc, hl0, hl1⟩ := stage_state hp hX hFw hw h hs
  obtain ⟨c', k', d', n', hσ', hsite', hel', hloc', hl0', hl1'⟩ :=
    stage_state hp hX hFw hw' h' hs'
  obtain ⟨-, -, -, -, -, -, -, -, hsz⟩ := hs
  obtain ⟨-, -, -, -, -, -, -, -, hsz'⟩ := hs'
  have ht : tidOf L y < 128 := MemRow.wg0_tid hw
  have ht' : tidOf L y' < 128 := MemRow.wg0_tid hw'
  obtain ⟨hsp, hcta, hlo, hhi⟩ := hc
  obtain ⟨-, hcta', hlo', hhi'⟩ := hc'
  rw [hloc] at hcta hlo hhi
  rw [hloc'] at hcta' hlo' hhi'
  rw [hsz] at hhi
  rw [hsz'] at hhi'
  simp only [wsLoc] at hcta hcta' hlo hhi hlo' hhi'
  have hc4 := c.isLt
  have hc4' := c'.isLt
  have hal : ∀ c : Fin 4, MemRow.wg0OutOff c.val % 4 = 0 := by decide
  have h1 := hal c
  have h2 := hal c'
  have hoff : 16384 * (tidOf L y / 64) + 128 * (tidOf L y % 64) +
      16 * (k.val ^^^ tidOf L y % 8) + MemRow.wg0OutOff c.val + 4 * d.el =
      16384 * (tidOf L y' / 64) + 128 * (tidOf L y' % 64) +
      16 * (k'.val ^^^ tidOf L y' % 8) + MemRow.wg0OutOff c'.val + 4 * d'.el := by
    omega
  obtain ⟨htt, hcc, hkk, hee⟩ := MemRow.wg0Ost2_inj ht ht' hc4 hc4' k.isLt k'.isLt hel hel' hoff
  have hyy : y = y' := by
    have hb := hp.block
    have hx := tidOf_x_eq hp y
    have hx' := tidOf_x_eq hp y'
    rw [hb] at hcta hcta'
    simp only [tidOf] at htt
    rw [hx, hx'] at htt
    have e1 := Nat.div_add_mod y 384
    have e2 := Nat.div_add_mod y' 384
    omega
  subst hyy
  have hcc' : c = c' := Fin.ext hcc
  have hkk' : k = k' := Fin.ext hkk
  subst hcc' hkk'
  have hpl : Wg0.place d = Wg0.place d' := by
    simp only [Wg0.place, hsite, hsite', Wg0.regPlace, Wg0.Site.reg, Wg0.elOff, hee, hl0, hl0',
      hl1, hl1']
  refine ⟨rfl, ?_⟩
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · have := place_lt hFw hw hy (noUbBefore_of_get hX h') h (by simp [Event.counts]) hlt hσ hσ'
    omega
  · exact heq
  · have := place_lt hFw hw hy (noUbBefore_of_get hX h) h' (by simp [Event.counts]) hgt hσ' hσ
    omega

/-! ### The poll of `svDone` before the epilogue's stores -/

/-- The sites of the staging stores and of the output tensor stores are the epilogue's, after
the SV poll. -/
private theorem site_epi1 (s : Wg0.Site)
    (h : (∃ c : Fin 4, ∃ k : Fin 8, s.pc = Wg0.ost2Base c + k.val) ∨
      ∃ c : Fin 4, s.pc = [1358, 1516, 1673, 1831].getD c.val 0) :
    s.reg = .epi ∧ s.idx = 1 ∧ 2 ≤ s.lens := by
  cases s with
  | ost2 c k => exact ⟨rfl, rfl, by simp [Wg0.Site.lens]⟩
  | otma c => exact ⟨rfl, rfl, by simp [Wg0.Site.lens]⟩
  | sld a k => exfalso; revert a k; decide
  | pst k | pld k => exfalso; revert k; decide
  | ost c | rld c | rldw c | rst c | rstw c | old c | oldw c | ofpx c | obar c
    | oel c => exfalso; revert c; decide
  | _ => exfalso; revert h; decide

/-- A successful poll of `svDone` of a lane of warpgroup 0 is at pc 1184, an acquire of CTA
scope (the other polls are on other objects). -/
private theorem svPoll_pc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) {jw pc p : Nat} {j : Fin 2} {acq : Bool}
    {sc : MbarScope}
    (he : X.get (y, jw) = some ⟨pc, .wait (loc L y (.svDone j)) p true acq sc⟩) :
    pc = 1184 ∧ acq = true ∧ sc = .cta := by
  have hin := wg0_inRole hp hX hFw hw he (.inl ⟨_, _, _, _, rfl⟩)
  simp only [Wg0.inRole, decide_eq_true_eq] at hin
  have hub : ∀ f, Kind.wait (loc L y (.svDone j)) p true acq sc ≠ .ub f := fun _ h => by
    cases h
  obtain ⟨d, hR, hE, -⟩ := wg0_at hp hX hFw he hub (by simp only; omega)
  have hcls := Wg0.ev_class hp hR (wg0_take_noUb hX he)
    (fun l => wg0_okPolls hp hX hFw hw jw l) hE hub (by simp only; omega)
  simp only [Wg0.PcClass, Wait, Kind.wait.injEq] at hcls
  rcases hcls with ⟨-, ok, hl, -⟩ | ⟨-, ok, hl, -⟩ | ⟨h1, ok, -, -, -, ha, hs⟩ | ⟨hno, -⟩
  · exact absurd (Wg0.loc_inj.mp hl) (fun h => by cases h)
  · exact absurd (Wg0.loc_inj.mp hl) (fun h => by cases h)
  · exact ⟨h1, ha, hs⟩
  · exact (hno _ _ _ _ _ rfl).elim

/-- **Before an epilogue store, the lane's poll of `svDone`**: a lane of warpgroup 0 at an event
of the epilogue after the SV poll made a successful poll of `svDone` of the CTA's last block's
slot, at pc 1184. -/
private theorem epi_poll (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) {i pc : Nat} {k : Kind}
    (h : X.get (y, i) = some ⟨pc, k⟩) (hub : ∀ f, k ≠ .ub f) (hr : 103 ≤ pc ∧ pc < 1842)
    (hsite : ∀ s : Wg0.Site, s.pc = pc → s.reg = .epi ∧ s.idx = 1 ∧ 2 ≤ s.lens) :
    ∃ jw p, jw < i ∧ X.get (y, jw) = some ⟨1184, .wait (mbarLoc L (y / L.block)
      (.svDone (slot2 (blocksOf P L (y / L.block) - 1)))) p true true .cta⟩ := by
  have hy : y < L.threads := Frame.lt_of_get hX h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw h hub
  obtain ⟨d, n, rfl, -, hE, -⟩ := wg0_state hJ hi hev hpc hr
  have hpc' : pc = d.site.pc := hpc
  obtain ⟨hreg, hidx, hlens⟩ := hsite d.site hpc'.symm
  rcases w0_bst_pre hFw (noUbBefore_of_get hX h) hw hy hσ with
    ⟨d0, n0, h0, -⟩ | ⟨d0, n0, h0, hC, hL, -⟩
  · simp at h0
  simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h0
  obtain ⟨rfl, -⟩ := h0
  have hb := Wg0.rounds_blocks hL hlens
  unfold Wg0.RefCore Wg0.RefAt at hC
  rw [hreg] at hC
  simp only [hidx, ↓reduceIte] at hC
  obtain ⟨-, hn, -⟩ := hC
  have hsv : (Wg0.objs L y).sv ((blocksOf P L (y / L.block) - 1) % 2) =
      loc L y (.svDone (slot2 (blocksOf P L (y / L.block) - 1))) :=
    Wg0.o_sv hp (Nat.mod_lt _ (by decide))
  have hc1 : 0 + 1 ≤ okPolls (loc L y (.svDone (slot2 (blocksOf P L (y / L.block) - 1))))
      ((X.tr y).take i) := by
    have h2 := hn (loc L y (.svDone (slot2 (blocksOf P L (y / L.block) - 1))))
    simp only at h2
    rw [wg0_okPolls hp hX hFw hw i, h2, Wg0.acq_sv]
    have hb' : Wg0.rounds (Wg0.Control.D.words d).l0 (Wg0.Control.D.words d).l1 =
        blocksOf P L (y / L.block) := hb
    simp only [Wg0.svSlot, hb', hsv, Wg0.ind, ite_true]
    omega
  obtain ⟨jw, pcp, p, acq, sc, hjw, hget, -⟩ := UnitHandoff.exists_poll hc1
  obtain ⟨rfl, rfl, rfl⟩ := svPoll_pc hp hX hFw hw hget
  exact ⟨jw, p, hjw, hget⟩

/-- **A staging store follows the lane's poll of `svDone`** (pc 1184, the CTA's last block's
slot): the epilogue's stores are made after the SV poll. -/
theorem wg0_stage_poll (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i pc : Nat} (hw : warp L y < 4) {a : Acc}
    {bs : List Byte} (h : X.get (y, i) = some ⟨pc, .wr a bs⟩) (hs : MemRow.Wg0Stage L y pc a) :
    ∃ jw p, jw < i ∧ X.get (y, jw) = some ⟨1184, .wait (mbarLoc L (y / L.block)
      (.svDone (slot2 (blocksOf P L (y / L.block) - 1)))) p true true .cta⟩ := by
  obtain ⟨c0, hc0, k0, hk0, el0, -, hpc0, -⟩ := hs
  have hr : 103 ≤ pc ∧ pc < 1842 := by
    rcases (by omega : c0 = 0 ∨ c0 = 1 ∨ c0 = 2 ∨ c0 = 3) with rfl | rfl | rfl | rfl <;>
      simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at hpc0 <;> omega
  exact epi_poll hp hX hFw hw h (fun _ h => by cases h) hr fun s hs' =>
    site_epi1 s (.inl ⟨⟨c0, hc0⟩, ⟨k0, hk0⟩, by
      rw [hs']; simpa [Wg0.ost2Base] using hpc0⟩)

/-- **An output tensor store follows the lane's poll of `svDone`.** -/
theorem wg0_store_poll (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i pc a : Nat} (hw : warp L y < 4)
    {s : TensorStore.Spec} (h : X.get (y, i) = some ⟨pc, .tensorStore a s⟩)
    (hpc : ∃ c < 4, pc = [1358, 1516, 1673, 1831].getD c 0) :
    ∃ jw p, jw < i ∧ X.get (y, jw) = some ⟨1184, .wait (mbarLoc L (y / L.block)
      (.svDone (slot2 (blocksOf P L (y / L.block) - 1)))) p true true .cta⟩ := by
  obtain ⟨c, hc, rfl⟩ := hpc
  have hr : 103 ≤ [1358, 1516, 1673, 1831].getD c 0 ∧ [1358, 1516, 1673, 1831].getD c 0 < 1842 := by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;> decide
  exact epi_poll hp hX hFw hw h (fun _ h => by cases h) hr fun s hs' =>
    site_epi1 s (.inr ⟨⟨c, hc⟩, hs'⟩)

/-- The site of an output load's pc is of the epilogue, after the SV poll. -/
private theorem site_old (s : Wg0.Site) (c : Fin 4) (h : s.pc = (Wg0.Site.old c).pc) :
    s.reg = .epi ∧ s.idx = 1 ∧ 2 ≤ s.lens := by
  revert h
  fin_cases c <;> (cases s <;> (try (rename_i x; fin_cases x)) <;>
    (try (rename_i y; fin_cases y)) <;> decide)

/-- **An output load follows the lane's poll of `svDone`** (pc 1184, the CTA's last block's
slot). -/
theorem wg0_old_poll (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i pc a : Nat} {vals : List Value} {sh : TcShape}
    (hw : warp L y < 4) (h : X.get (y, i) = some ⟨pc, .tc (.ld a vals sh)⟩)
    (hpc : ∃ c < 4, pc = [1201, 1361, 1519, 1676].getD c 0) (hr : 103 ≤ pc ∧ pc < 1842) :
    ∃ jw p, jw < i ∧ X.get (y, jw) = some ⟨1184, .wait (mbarLoc L (y / L.block)
      (.svDone (slot2 (blocksOf P L (y / L.block) - 1)))) p true true .cta⟩ := by
  obtain ⟨c, hc, rfl⟩ := hpc
  exact epi_poll hp hX hFw hw h (fun _ h => by cases h) hr fun s hs' =>
    site_old s ⟨c, hc⟩ hs'

/-- The site of the closing barrier's pc is `ebar`. -/
private theorem site_ebar (s : Wg0.Site) (h : s.pc = 1835) : s = .ebar := by
  revert h
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals decide

/-- **The closing barrier of warpgroup 0 follows the lane's poll of `svDone`** (pc 1184, the CTA's
last block's slot). -/
theorem wg0_bar12_poll (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i : Nat} (hw : warp L y < 4)
    (h : X.get (y, i) = some ⟨1835, .bar 12 none .sync⟩) :
    ∃ jw p, jw < i ∧ X.get (y, jw) = some ⟨1184, .wait (mbarLoc L (y / L.block)
      (.svDone (slot2 (blocksOf P L (y / L.block) - 1)))) p true true .cta⟩ :=
  epi_poll hp hX hFw hw h (fun _ h => by cases h) ⟨by omega, by omega⟩ fun s hs' => by
    rw [site_ebar s hs']
    exact ⟨rfl, rfl, by simp [Wg0.Site.lens]⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
