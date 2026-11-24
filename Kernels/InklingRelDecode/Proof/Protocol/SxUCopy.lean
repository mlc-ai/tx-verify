-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SxRingUse
public import Kernels.InklingRelDecode.Proof.Interface.LpPreProof
public import Kernels.InklingRelDecode.Proof.Interface.PshWarp

@[expose] public section

/-!
# Two copies of one use of a KV slot that write one byte are one copy

`copy_same_use`: two tensor-copy write stages of the same shared byte, of copies completing on
`kv_ready t` of CTA `c` with the same use of the slot (`Ring.Kv.copyUse` of `Lp.slotOf`), are the
same stage: the same issue event and the same element `(x, y, z)`.

* Two prologue copies (`pro_copy`): the copy at site `ptc j` by a thread of warp `w < 2` writes the
  box `(j % 2, j % 4 / 2, w)` of slot `j / 4` (`ProA.copyDst_form`), and its thread is the warp's
  elected lane `cpThr c w` (`Lp.cpThr_eq`). One byte fixes the box, so `j` and `w`, so the thread
  and its state (`Lp.pro_site_unique`).
* Two loader copies (`ld_copy`): both are by `cpThread c` (`Lp.loader_copy_src`); the copy at site
  `s` writes the box `ldBox s` of slot `d.i % 3`, and its count of earlier issues to `kv_ready t` is
  `cpIn s` modulo 8 (`Ring.loader_copy_exec`), where `cpIn s` is a function of the box
  (`cpIn_box`). The use is the count divided by 8, plus one if the slot was preloaded; so one byte
  and one use fix the count, and two issues of one thread with the same count are one event
  (`same_count`).
* A prologue copy has use 0 and a loader copy of a preloaded slot use at least 1.

The element: a KV copy's box writes the byte `dst + swizzle (128 y + 2 x + z)`, injective in
`(x, y, z)` (`copy_elem`, `TensorCopy.box_offset_inj`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sx
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty kvCopySpec)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **A KV copy writes each byte from one element.** -/
theorem kv_elem {cta col row dst : Nat} {bar : Loc} {x y z x' y' z' : Nat} {l : Loc}
    (h1 : TensorCopy.writeLoc (kvCopySpec Q cta col row dst bar) x y z = some l)
    (h2 : TensorCopy.writeLoc (kvCopySpec Q cta col row dst bar) x' y' z' = some l) :
    x = x' ∧ y = y' ∧ z = z' := by
  obtain ⟨hx, hy, hz⟩ := TensorCopy.writeLoc_bounds h1
  obtain ⟨hx', hy', hz'⟩ := TensorCopy.writeLoc_bounds h2
  have h0 : TensorTile.count (kvCopySpec Q cta col row dst bar).descriptor.box 0 = 64 := by
    simp [kvCopySpec, mapKv, TensorTile.count, TensorTile.step]
  have hR : TensorTile.rows (kvCopySpec Q cta col row dst bar).descriptor.box = 64 := by
    simp [kvCopySpec, mapKv, TensorTile.rows, TensorTile.rowsOf, TensorTile.count,
      TensorTile.step]
  have hfb : (kvCopySpec Q cta col row dst bar).descriptor.format.bytes = 2 := by
    simp [kvCopySpec, mapKv, TensorDescriptor.Format.bytes]
  have hsw : (kvCopySpec Q cta col row dst bar).descriptor.swizzle = .b128 := rfl
  rw [h0] at hx hx'
  rw [hR] at hy hy'
  rw [hfb] at hz hz'
  rw [Ring.Foot.box_writeLoc2 h0 hR hfb hsw hx hy hz] at h1
  rw [Ring.Foot.box_writeLoc2 h0 hR hfb hsw hx' hy' hz', ← h1] at h2
  have ha := congrArg Loc.addr (Option.some.inj h2)
  simp only [Nat.add_left_cancel_iff] at ha
  have := TensorCopy.box_offset_inj hx hz hx' hz' ha.symm
  omega

/-- **A copy writes each byte from one element.** -/
theorem copy_elem (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩) {x y z x' y' z' : Nat} {l : Loc}
    (h1 : TensorCopy.writeLoc sp x y z = some l) (h2 : TensorCopy.writeLoc sp x' y' z' = some l) :
    x = x' ∧ y = y' ∧ z = z' := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hTT : TT Q L X (g, k) := fun h => hf.tracked g (k + 1) hg h
  obtain ⟨col, row, dst, bar, hk, -, -, -⟩ :=
    Interface.copy_spec_at hpre hX hf.sound hf.ldRng hg he ⟨a, sp, rfl⟩ hTT
  simp only [Kind.tensorIssue.injEq] at hk
  obtain ⟨-, rfl⟩ := hk
  exact kv_elem h1 h2

/-- **The prologue's copy: its site, its thread and its box.** -/
theorem pro_copy (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k pc a : Nat} {sp : TensorCopy.Spec} {d : ProA.D}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩)
    (hσ : St Q L X g k = some (some (.d (.pro d)))) :
    ∃ j < 12, d.site = ProA.ptcSite j ∧ g % L.block / 32 < 2 ∧
      g = Lp.cpThr L X (g / L.block) (g % L.block / 32) ∧
      sp.mbar = (EvD.kvReadyOf (j / 4)).loc L (g / L.block) ∧
      ∀ x y z l, TensorCopy.writeLoc sp x y z = some l →
        boxBase L (j / 4) (j % 2) (j % 4 / 2) (g % L.block / 32) ≤ l.addr ∧
        l.addr < boxBase L (j / 4) (j % 2) (j % 4 / 2) (g % L.block / 32) + 8192 := by
  have hb : L.block = 256 := hpre.block
  have hth : L.threads = L.grid * L.block := rfl
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := len_of_get he
  have hTT : TT Q L X (g, k) := fun h => hf.tracked g (k + 1) hg h
  obtain ⟨col, row, dst, bar, hk', -, -, -⟩ :=
    Interface.copy_spec_at hpre hX hf.sound hf.ldRng hg he ⟨a, sp, rfl⟩ hTT
  simp only [Kind.tensorIssue.injEq] at hk'
  obtain ⟨-, hspec⟩ := hk'
  have hsb : ProA.SbRoom L := by
    have := hpre.sharedRange
    unfold sharedBytes at this
    unfold ProA.SbRoom
    omega
  rcases copy_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨a, sp, rfl⟩ with
    ⟨d', hσ', j, hj, hsj, a', s', hev, -, -, hmb, hsb', -⟩ | ⟨d', P, hσ', -⟩
  · rw [hσ] at hσ'
    simp only [Option.some.injEq, TSt.d.injEq, DComp.St.pro.injEq] at hσ'
    subst hσ'
    simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
    obtain ⟨-, -, rfl⟩ := hev
    obtain ⟨hI, hdef⟩ := Lp.pro_inv_at hX hf he hσ
    obtain ⟨hne, -, hmem⟩ := Lp.ptc_props j hj
    obtain ⟨k0, e0, d0, hk0, he0, hσ0, hn0⟩ := Interface.pro_pred hk.le hσ (by rw [hsj]; exact hne)
    obtain ⟨⟨mask, inst, hel⟩, h59⟩ := ProA.next_into_ptc hn0 (by rw [hsj]; exact hmem)
    have ht := ProA.tid_of_p59 (by rw [Lp.tid_eq]; omega) h59
    rw [Lp.tid_eq] at ht
    have hel' : Elected (X.tr g) (laneOf L g) :=
      ⟨e0, List.mem_of_getElem? he0, mask, inst, hel⟩
    have hlead := electLead_of_elected hX hel'
    have hwg : SameWarp L (g / L.block * L.block + 32 * (g % L.block / 32)) g := by
      refine ⟨⟨?_, hg, ?_⟩, ?_⟩
      · rw [hth, hb] at hg ⊢; rw [hb] at ht; omega
      · rw [hb] at ht ⊢; omega
      · rw [hb] at ht ⊢; omega
    have hthr := Lp.cpThr_eq hX hwg hlead hel'
    have hdst : dst = ProA.copyDst L g d.dt j := by
      have := hsb'
      rw [hspec] at this
      simp only [EvW.kvCopySpec, Loc.mk.injEq] at this
      exact this.2.2
    rw [ProA.copyDst_form L g d.dt hsb hj, Interface.pro_half hpre hX hf hσ hj hsj,
      Lp.tid_eq] at hdst
    refine ⟨j, hj, hsj, by omega, hthr.symm, hmb, fun x y z l hl => ?_⟩
    rw [hspec] at hl
    obtain ⟨-, -, h4, h5⟩ := Ring.Foot.copy_foot Q (g / L.block) col row dst bar hl
    have hw : g % L.block / 32 % 2 = g % L.block / 32 := by omega
    rw [hw] at hdst
    unfold boxBase
    omega
  · rw [hσ] at hσ'; cases hσ'

/-- The count of a loader copy site is a function of its box. -/
theorem cpIn_box (s : Loader.Site) (h : Ring.Ld.isCp s = true) :
    ∃ (v : Bool) (sl hh : Nat), EvW.ldBox s = some (v, sl, hh) ∧ sl ≤ 1 ∧ hh ≤ 1 ∧
      Ring.Ld.cpIn s = 4 * sl + 2 * (if v then 1 else 0) + hh := by
  cases s <;> simp [Ring.Ld.isCp] at h <;> simp [EvW.ldBox, Ring.Ld.cpIn]

/-- **A loader copy on `kv_ready t`: its box, its slot and its count.** -/
theorem ld_copy (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X) {t : Nat}
    (ht : t < 3) {k pc a : Nat} {sp : TensorCopy.Spec} {d : Loader.D} {P : Loader.Pro}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩)
    (hm : sp.mbar = kvReady L (g / L.block) t)
    (hσ : St Q L X g k = some (some (.w (.loader d P)))) (hcp : Ring.Ld.isCp d.site = true) :
    ∃ (v : Bool) (sl hh : Nat), sl ≤ 1 ∧ hh ≤ 1 ∧
      ((X.tr g).take k).countP (issuesTo (kvReady L (g / L.block) t)) % 8 =
        4 * sl + 2 * (if v then 1 else 0) + hh ∧
      ∀ x y z l, TensorCopy.writeLoc sp x y z = some l →
        L.sharedBase + 32768 * t + (if v then 98304 else 0) + 8192 * sl + 16384 * hh ≤ l.addr ∧
        l.addr < L.sharedBase + 32768 * t + (if v then 98304 else 0) + 8192 * sl + 16384 * hh +
          8192 := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := len_of_get he
  have hnpre : ¬ Lp.PreSite d.site := by
    intro h; rcases h with h | h | h <;> rw [h] at hcp <;> cases hcp
  obtain ⟨hw, k0, d0, hk0, h0, hd, hs0, hi0, hin, -, hPl, hC⟩ :=
    Lp.loader_anchor hpre hX hf hR hp hk hσ hnpre
  have hlead := electLead_of_elected hX (Lp.copy_lead hX k hk hσ hcp)
  obtain ⟨-, hs3, -, ⟨b, hb, rfl⟩, hmod, -, -⟩
    := Ring.loader_copy_exec hpre hw hg hX hk0 h0 hd (hf.ldRng hg hσ)
    hin hs0 (by rw [hi0]; exact Lp.numPre_le _ _ _) ht (hlead.take k) (hC _) (hPl _) he hm
  obtain ⟨v, sl, hh, hb', hsl, hhh, hcpIn⟩ := cpIn_box d.site hcp
  rw [hb] at hb'
  cases hb'
  refine ⟨v, sl, hh, hsl, hhh, hmod.trans hcpIn, fun x y z l hl => ?_⟩
  have hl' := hl
  unfold EvW.ldCopy at hl'
  obtain ⟨-, -, h4, h5⟩ := Ring.Foot.copy_foot Q (g / L.block) _ _ _ _ hl'
  unfold EvW.ldDst at h4 h5
  simp only at h4 h5
  rw [hs3] at h4 h5
  exact ⟨h4, h5⟩

/-- **Two issues to one mbarrier of one thread with the same count before them are one event.** -/
theorem same_count {m : Loc} {k1 k2 : Nat} {e1 e2 : Event} (h1 : X.get (g, k1) = some e1)
    (h2 : X.get (g, k2) = some e2) (hi1 : issuesTo m e1 = true) (hi2 : issuesTo m e2 = true)
    (hc : ((X.tr g).take k1).countP (issuesTo m) = ((X.tr g).take k2).countP (issuesTo m)) :
    k1 = k2 := by
  have key : ∀ {a b : Nat} {ea : Event}, X.get (g, a) = some ea → issuesTo m ea = true → a < b →
      ((X.tr g).take a).countP (issuesTo m) < ((X.tr g).take b).countP (issuesTo m) := by
    intro a b ea ha hia hab
    have hs := countP_take_succ (issuesTo m) (l := X.tr g) (k := a) ha
    simp only [hia, ↓reduceIte] at hs
    have hle : ((X.tr g).take (a + 1)).countP (issuesTo m) ≤
        ((X.tr g).take b).countP (issuesTo m) :=
      (List.take_sublist_take_left (show a + 1 ≤ b by omega)).countP_le
    omega
  rcases lt_trichotomy k1 k2 with h | h | h
  · have := key h1 hi1 h
    omega
  · exact h
  · have := key h2 hi2 h
    omega

/-- **Two write stages of one byte, of copies on slot `t` of CTA `c` with the same use, are one
stage.** -/
theorem copy_same_use (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X)
    {c t : Nat} (ht : t < 3) {pArr : EvId} {pCp : Fin 8 → EvId}
    (hP : Lp.PreSlot Q L X c t pArr pCp) (cm : Nat)
    {i1 i2 : EvId} {x y z x' y' z' : Nat} {l : Loc}
    (hw1 : AsyncCovers X i1 (.write (.load x y z)) l)
    (hw2 : AsyncCovers X i2 (.write (.load x' y' z')) l)
    (hm1 : ∀ pc a sp, X.get i1 = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = kvReady L c t)
    (hm2 : ∀ pc a sp, X.get i2 = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = kvReady L c t)
    (heq : Ring.Kv.copyUse X (Lp.slotOf Q L X c t cm pArr pCp) i1 =
      Ring.Kv.copyUse X (Lp.slotOf Q L X c t cm pArr pCp) i2) :
    i1 = i2 ∧ x = x' ∧ y = y' ∧ z = z' := by
  obtain ⟨pc1, a1, sp1, he1, hl1⟩ := copy_write_at hw1
  obtain ⟨pc2, a2, sp2, he2, hl2⟩ := copy_write_at hw2
  have hm1' := hm1 _ _ _ he1
  have hm2' := hm2 _ _ _ he2
  suffices hid : i1 = i2 by
    subst hid
    rw [he1] at he2
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at he2
    obtain ⟨-, -, rfl⟩ := he2
    obtain ⟨g1, k1⟩ := i1
    exact ⟨rfl, copy_elem hpre hX hf he1 hl1 hl2⟩
  obtain ⟨g1, k1⟩ := i1
  obtain ⟨g2, k2⟩ := i2
  have hb : L.block = 256 := hpre.block
  have hk1 : k1 < (X.tr g1).length := len_of_get he1
  have hk2 : k2 < (X.tr g2).length := len_of_get he2
  obtain ⟨-, hc1, hcase1⟩ := Lp.copy_kvReady hpre hX hf he1 hm1'
  obtain ⟨-, hc2, hcase2⟩ := Lp.copy_kvReady hpre hX hf he2 hm2'
  -- the use of a loader copy
  have hld : ∀ {g k : Nat} {d : Loader.D} {P : Loader.Pro},
      St Q L X g k = some (some (.w (.loader d P))) → k < (X.tr g).length →
      Ring.Kv.copyUse X (Lp.slotOf Q L X c t cm pArr pCp) (g, k) =
        ((X.tr g).take k).countP (issuesTo (kvReady L c t)) / 8 +
          (if t < Lp.npOf Q L c then 1 else 0) := by
    intro g k d P hσ hk
    have hnot : ¬ ∃ i : Fin 8, (g, k) = pCp i := by
      rintro ⟨i, hi⟩
      have h1 := (hP.cp_thr i).2
      rw [← hi] at h1
      have := Lp.loader_warp hf.roleWarp hk.le hσ
      simp only at h1
      omega
    have hcond : ¬ ((Lp.slotOf Q L X c t cm pArr pCp).δ = 1 ∧
        ∃ i, (g, k) = (Lp.slotOf Q L X c t cm pArr pCp).pCp i) := fun h => hnot h.2
    unfold Ring.Kv.copyUse
    simp only [hcond, ↓reduceIte]
    rfl
  -- the use of a prologue copy
  have hpro : ∀ {g k pc a : Nat} {sp : TensorCopy.Spec} {d : ProA.D},
      X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = kvReady L c t →
      St Q L X g k = some (some (.d (.pro d))) →
      Ring.Kv.copyUse X (Lp.slotOf Q L X c t cm pArr pCp) (g, k) = 0 ∧ t < Lp.npOf Q L c := by
    intro g k pc a sp d he hm hσ
    obtain ⟨⟨i, hi⟩, hnp⟩ := hP.cp he hm hσ
    have hcond : (Lp.slotOf Q L X c t cm pArr pCp).δ = 1 ∧
        ∃ i, (g, k) = (Lp.slotOf Q L X c t cm pArr pCp).pCp i :=
      ⟨by simp [Lp.slotOf, hnp], i, hi⟩
    unfold Ring.Kv.copyUse
    simp only [hcond, and_self, ↓reduceIte, true_and]
    exact hnp
  rcases hcase1 with ⟨d1, hσ1⟩ | ⟨d1, P1, hσ1, hcp1⟩ <;>
    rcases hcase2 with ⟨d2, hσ2⟩ | ⟨d2, P2, hσ2, hcp2⟩
  · -- two prologue copies
    obtain ⟨j1, hj1, hs1, hw1', hthr1, hmb1, hbx1⟩ := pro_copy hpre hX hf he1 hσ1
    obtain ⟨j2, hj2, hs2, hw2', hthr2, hmb2, hbx2⟩ := pro_copy hpre hX hf he2 hσ2
    obtain ⟨-, ht1⟩ := Lp.kvReady_loc_eq (hmb1.symm.trans hm1')
    obtain ⟨-, ht2⟩ := Lp.kvReady_loc_eq (hmb2.symm.trans hm2')
    obtain ⟨a1l, a1h⟩ := hbx1 x y z l hl1
    obtain ⟨a2l, a2h⟩ := hbx2 x' y' z' l hl2
    unfold boxBase at a1l a1h a2l a2h
    have hq1 : j1 / 4 = t := by omega
    have hq2 : j2 / 4 = t := by omega
    rw [hq1] at a1l a1h
    rw [hq2] at a2l a2h
    have hA1 : (l.addr - L.sharedBase) / 8192 =
        4 * t + 12 * (j1 % 2) + j1 % 4 / 2 + 2 * (g1 % L.block / 32) := by omega
    have hA2 : (l.addr - L.sharedBase) / 8192 =
        4 * t + 12 * (j2 % 2) + j2 % 4 / 2 + 2 * (g2 % L.block / 32) := by omega
    have key : 12 * (j1 % 2) + (j1 % 4 / 2 + 2 * (g1 % L.block / 32)) =
        12 * (j2 % 2) + (j2 % 4 / 2 + 2 * (g2 % L.block / 32)) := by omega
    have hb1 : j1 % 2 < 2 := Nat.mod_lt _ (by omega)
    have hb2 : j2 % 2 < 2 := Nat.mod_lt _ (by omega)
    have hc1' : j1 % 4 / 2 < 2 := by omega
    have hc2' : j2 % 4 / 2 < 2 := by omega
    have hv : j1 % 2 = j2 % 2 ∧ j1 % 4 / 2 = j2 % 4 / 2 ∧
        g1 % L.block / 32 = g2 % L.block / 32 := by
      generalize j1 % 2 = a1 at key hb1
      generalize j2 % 2 = a2 at key hb2
      generalize j1 % 4 / 2 = s1 at key hc1' ⊢
      generalize j2 % 4 / 2 = s2 at key hc2' ⊢
      generalize g1 % L.block / 32 = w1 at key hw1' ⊢
      generalize g2 % L.block / 32 = w2 at key hw2' ⊢
      omega
    have hj : j1 = j2 := by omega
    have hw : g1 % L.block / 32 = g2 % L.block / 32 := hv.2.2
    have hgg : g1 = g2 := by rw [hthr1, hthr2, hc1, hc2, hw]
    subst hj hgg
    have hk := Lp.pro_site_unique hk1.le hk2.le hσ1 hσ2 (hs1.trans hs2.symm)
      (hs2 ▸ (Lp.ptc_props j1 hj1).1)
    rw [hk]
  · -- a prologue copy and a loader copy
    exfalso
    obtain ⟨hu1, hnp⟩ := hpro he1 hm1' hσ1
    simp only [hu1, hld hσ2 hk2, hnp, ↓reduceIte] at heq
    omega
  · exfalso
    obtain ⟨hu2, hnp⟩ := hpro he2 hm2' hσ2
    simp only [hu2, hld hσ1 hk1, hnp, ↓reduceIte] at heq
    omega
  · -- two loader copies
    obtain ⟨hcp1', -⟩ := Lp.loader_copy_src hpre hX hf hR hp ht he1 hm1' hc1 hσ1 hcp1
    obtain ⟨hcp2', -⟩ := Lp.loader_copy_src hpre hX hf hR hp ht he2 hm2' hc2 hσ2 hcp2
    have hgg : g1 = g2 := hcp1'.trans hcp2'.symm
    subst hgg
    obtain ⟨v1, sl1, hh1, hsl1, hhh1, hmod1, hbx1⟩ :=
      ld_copy hpre hX hf hR hp ht he1 (by rw [hc1]; exact hm1') hσ1 hcp1
    obtain ⟨v2, sl2, hh2, hsl2, hhh2, hmod2, hbx2⟩ :=
      ld_copy hpre hX hf hR hp ht he2 (by rw [hc1]; exact hm2') hσ2 hcp2
    obtain ⟨a1l, a1h⟩ := hbx1 x y z l hl1
    obtain ⟨a2l, a2h⟩ := hbx2 x' y' z' l hl2
    rw [hc1] at hmod1 hmod2
    rw [hld hσ1 hk1, hld hσ2 hk2] at heq
    have hcnt : ((X.tr g1).take k1).countP (issuesTo (kvReady L c t)) =
        ((X.tr g1).take k2).countP (issuesTo (kvReady L c t)) := by
      cases v1 <;> cases v2 <;> simp only [Bool.false_eq_true, ite_true, ite_false] at * <;>
        omega
    have hi1 : issuesTo (kvReady L c t) ⟨pc1, .tensorIssue a1 sp1⟩ = true := by
      rw [issuesTo_tensorIssue, hm1']; simp
    have hi2 : issuesTo (kvReady L c t) ⟨pc2, .tensorIssue a2 sp2⟩ = true := by
      rw [issuesTo_tensorIssue, hm2']; simp
    rw [same_count he1 he2 hi1 hi2 hcnt]

end
end PTX.Kernels.InklingRelDecode.Proof.Sx
