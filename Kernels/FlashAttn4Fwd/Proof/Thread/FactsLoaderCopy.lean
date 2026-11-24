-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderRing
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem
public import Kernels.FlashAttn4Fwd.Proof.Interface.Score
public import Kernels.FlashAttn4Fwd.Proof.Interface.P2
public import Kernels.FlashAttn4Fwd.Proof.Interface.OAcc
public import Kernels.FlashAttn4Fwd.Proof.Interface.Stats
public import Kernels.FlashAttn4Fwd.Proof.Interface.Output
public import Lemmas.Tensor.BoxWrite
public import Lemmas.TensorStore.StoreWrite

@[expose] public section

/-! # The loader's thread facts: what its copies are and where they complete

Every tensor copy is the loader's copy of a use (`Loader.copy_origin`), completing on the
use's ring full barrier (`AsyncFacts.copy_ring`), so on no other barrier of the table: no
handshake, P-ready, S-full, O-full, credit, staged or free barrier (`Loader.copy_mbar_ne`).

A copy on a ring full barrier is `copySpec` of its earlier copies there (`RingCopies.copy`):
its map is the launch's map of its use's kind (`Pre.mapQ`, `mapK`, `mapV` at the parameter the
copy reads, `Loader.copy_desc`), its coordinates are those of its use's item and block
(`Loader.use_item`), its destination is box `j` of the barrier's region, it completes on the
even CTA's barrier, and it is a tile-mode `cta_group::2` copy through a `.shared::cluster`
barrier address (`CopyIs`).

A copy writes its box (64 FP16 columns per row, 128-byte swizzle) at its destination
(`TensorCopy.box_writeLoc`, `writeLoc_bounds`): box `j` of the barrier's region, `copyBytes`
long, inside the region (`RingFacts.write`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Loader

/-- The descriptor of a copy is the launch's map of its use's kind. -/
theorem copy_desc (hpre : Pre P L mem0) {c : CopyId} {a : Nat}
    {desc : TensorDescriptor.Descriptor 3} (hmap : ∃ decl, L.paramObjects c.map = some (decl, a))
    (hd : L.tensorMaps a = some ⟨3, desc⟩) : desc = copyMap P (c.bar L) := by
  obtain ⟨decl, hdecl⟩ := hmap
  have key : ∀ {pa : Nat} {dd : TensorDescriptor.Descriptor 3},
      L.tensorMaps pa = some ⟨3, dd⟩ → pa = a → desc = dd := by
    intro pa dd h1 h2
    subst h2
    rw [h1] at hd
    exact eq_of_heq (Sigma.mk.inj (Option.some.inj hd)).2.symm
  obtain ⟨u, j, i, t⟩ := c
  have hev := uB_even L i
  cases u <;> simp only [CopyId.map, CopyId.bar, CopyId.use, copyMap] at hdecl ⊢
  · rw [hpre.paramK] at hdecl
    split_ifs with hh
    · exact key hpre.mapK (Prod.mk.inj (Option.some.inj hdecl)).2
    · exfalso; omega
  · rw [hpre.paramQ] at hdecl
    exact key hpre.mapQ (Prod.mk.inj (Option.some.inj hdecl)).2
  · rw [hpre.paramQ] at hdecl
    exact key hpre.mapQ (Prod.mk.inj (Option.some.inj hdecl)).2
  · rw [hpre.paramV] at hdecl
    split_ifs with hh
    · exfalso; omega
    · exact key hpre.mapV (Prod.mk.inj (Option.some.inj hdecl)).2
  · rw [hpre.paramK] at hdecl
    split_ifs with hh
    · exact key hpre.mapK (Prod.mk.inj (Option.some.inj hdecl)).2
    · exfalso; omega
  · rw [hpre.paramV] at hdecl
    split_ifs with hh
    · exfalso; omega
    · exact key hpre.mapV (Prod.mk.inj (Option.some.inj hdecl)).2

/-- The box of a copy's map: 64 FP16 columns per row, `copyBytes / 128` rows, 128-byte swizzle. -/
theorem copyMap_box (c : CopyId) :
    TensorTile.count (copyMap P (c.bar L)).box 0 = 64 ∧
      TensorTile.rows (copyMap P (c.bar L)).box = (c.bar L).copyBytes / 128 ∧
      (copyMap P (c.bar L)).format = .f16 ∧ (copyMap P (c.bar L)).swizzle = .b128 := by
  obtain ⟨u, j, i, t⟩ := c
  have hev := uB_even L i
  cases u <;> simp only [CopyId.bar, CopyId.use, copyMap, FBar.copyBytes] <;>
    (try split_ifs) <;>
    simp [mapQ, mapK, mapV, encodeTiled, TensorTile.count, TensorTile.step, TensorTile.rows,
      TensorTile.rowsOf]

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (Proof.code L) X)
include hpre hX ht

/-- **A copy completes on no barrier but a ring full barrier.** -/
theorem copy_mbar_ne {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get i = some ⟨pc, .tensorIssue a sp⟩) {b : FBar} (hb : b.isFull = false) (c : Nat) :
    sp.mbar ≠ b.loc L c := by
  obtain ⟨g, k⟩ := i
  obtain ⟨d, -, -, -, -, -, u, j, -, hci, -⟩ := copy_origin hpre hX ht he
  intro h
  have hbb := (FBar.loc_inj (hci.mbar.symm.trans h)).1
  rw [← hbb, bar_isFull] at hb
  cases hb

end Loader

/-- Four coordinates as a list and as a vector. -/
theorem vec_getD {a b c d a' b' c' d' : Nat} (ha : a = a') (hb : b = b') (hc : c = c')
    (hd : d = d') (x : Fin 4) :
    (([a, b, c, d].getD x.val 0 : Nat) : Int) = ![(a' : Int), (b' : Int), (c' : Int), (d' : Int)] x
    := by
  subst ha hb hc hd
  fin_cases x <;> rfl

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **`AsyncFacts.copy_ring`**: every tensor copy completes on a ring barrier. -/
theorem AsyncFacts_copy_ring : ∀ {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec},
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → ∃ (b : FBar) (c : Nat), b.ring ∧ sp.mbar = b.loc L c :=
    by
  rintro ⟨g, k⟩ pc a sp he
  obtain ⟨d, -, -, -, -, -, u, j, -, hci, -⟩ := Loader.copy_origin hpre hX ht he
  exact ⟨_, _, Loader.bar_ring L _, hci.mbar⟩

/-- **`TmemFacts.hs_tensor`**: no tensor copy completes on a handshake barrier. -/
theorem TmemFacts_hs_tensor : ∀ {i : EvId} {pc a cta : Nat} {sp : TensorCopy.Spec},
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ FBar.loc L cta .dealloc :=
  fun he => Loader.copy_mbar_ne hpre hX ht he (b := .dealloc) rfl _

/-- **`PReadyFacts.p_tensor`**: no tensor copy completes on a P-ready object. -/
theorem PReadyFacts_p_tensor : ∀ {i : EvId} {pc a c st : Nat} {sp : TensorCopy.Spec}, st < 2 →
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ pReadyBar L c st :=
  fun hst he => Loader.copy_mbar_ne hpre hX ht he (b := .pReady ⟨_, hst⟩) rfl _

/-- **`SFullFacts.s_tensor`**: no tensor copy completes on an S-full object. -/
theorem SFullFacts_s_tensor : ∀ {i : EvId} {pc a c st : Nat} {sp : TensorCopy.Spec}, st < 2 →
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ sFullBar L c st :=
  fun hst he => Loader.copy_mbar_ne hpre hX ht he (b := .sFull ⟨_, hst⟩) rfl _

/-- **`OFullFacts.o_tensor`**: no tensor copy completes on an O-full object. -/
theorem OFullFacts_o_tensor : ∀ {i : EvId} {pc a c st : Nat} {sp : TensorCopy.Spec}, st < 2 →
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ oFullBar L c st :=
  fun hst he => Loader.copy_mbar_ne hpre hX ht he (b := .oFull ⟨_, hst⟩) rfl _

/-- **`P2Facts.p2_tensor`**: no tensor copy completes on a second P-ready object. -/
theorem P2Facts_p2_tensor : ∀ {i : EvId} {pc a c st : Nat} {sp : TensorCopy.Spec}, st < 2 →
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ pReady2Bar L c st :=
  fun hst he => Loader.copy_mbar_ne hpre hX ht he (b := .pReady2 ⟨_, hst⟩) rfl _

/-- **`StatsFacts.credit_tensor`**: no tensor copy completes on a credit barrier. -/
theorem StatsFacts_credit_tensor : ∀ {i : EvId} {pc a c st : Nat} {sp : TensorCopy.Spec},
    st < 2 → X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ statsBar L c st :=
  fun hst he => Loader.copy_mbar_ne hpre hX ht he (b := .stats ⟨_, hst⟩) rfl _

/-- **`OutputFacts.stage_tensor`**: no tensor copy completes on a staged or free barrier. -/
theorem OutputFacts_stage_tensor : ∀ {i : EvId} {pc a c st : Nat} {sp : TensorCopy.Spec},
    st < 2 → X.get i = some ⟨pc, .tensorIssue a sp⟩ →
      sp.mbar ≠ stagedBar L c st ∧ sp.mbar ≠ freeBar L c st :=
  fun hst he => ⟨Loader.copy_mbar_ne hpre hX ht he (b := .oStaged ⟨_, hst⟩) rfl _,
    Loader.copy_mbar_ne hpre hX ht he (b := .oFree ⟨_, hst⟩) rfl _⟩

/-- **`RingCopies.copy`**: a copy on a ring full barrier is `copySpec` of its thread and its
earlier copies there. -/
theorem RingCopies_copy : ∀ {g k pc a c : Nat} {b : FBar} {sp : TensorCopy.Spec},
    g < L.threads → X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = b.loc L c →
      b.isFull → sp = copySpec P L g b (((X.tr g).take k).countP (issuesTo (b.loc L c))) := by
  intro g k pc a c b sp _ he hm _
  obtain ⟨d, -, -, hJ, hi, -, u, j, hs, hci, hcnt⟩ := Loader.copy_origin hpre hX ht he
  obtain ⟨hb, hc⟩ := FBar.loc_inj (hm.symm.trans hci.mbar)
  subst hb hc
  obtain ⟨-, hj⟩ := Loader.copy_round hs hJ hi
  obtain ⟨hdiv, hmod⟩ := Loader.before_div (c := ⟨u, j, d.i, d.t⟩) hj
  obtain ⟨hitem, hblock⟩ := Loader.use_item hpre hs hi
  rw [← hm, hcnt]
  obtain ⟨⟨outer, desc, origin, sb, rows⟩, mbar, ca, grp⟩ := sp
  obtain ⟨hmap, hout, horig, hdst, hmb, -, hdesc, hrows, hca, hgrp⟩ := hci
  simp only at hout hrows hca hgrp hdst hmb hdesc horig
  subst hout hrows hca hgrp hdst hmb
  have hD := Loader.copy_desc hpre hmap hdesc
  subst hD
  simp only [copySpec, hdiv, hmod, TensorCopy.Spec.mk.injEq, TensorBox.mk.injEq, heq_eq_eq,
    true_and, and_true]
  have hone := hi.one u j (.inr hs)
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  have hev := Loader.uB_even L i
  have hrk : Work.rank L g = ctaOf L g % 2 := rfl
  refine ⟨⟨funext fun x => ?_, ?_⟩, rfl⟩
  all_goals try rw [horig x]
  all_goals simp only [copyOrigin, hitem]
  all_goals cases u <;> simp only [Loader.UseK.copies] at hone
  · have hb := hblock _ rfl
    simp only [Loader.CopyId.bar, Loader.CopyId.use, Loader.CopyId.block] at hb ⊢
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    refine vec_getD ?_ ?_ rfl rfl x <;> (try rw [hb]) <;> rfl
  · refine vec_getD rfl ?_ rfl rfl x
    simp [Loader.CopyId.stage, hrk]
  · refine vec_getD rfl ?_ rfl rfl x
    simp [Loader.CopyId.stage, hrk]; omega
  · have hb := hblock _ rfl
    simp only [Loader.CopyId.bar, Loader.CopyId.use, Loader.CopyId.block] at hb ⊢
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    refine vec_getD ?_ ?_ rfl rfl x <;> (try rw [hb]) <;> rfl
  · have hb := hblock _ rfl
    simp only [Loader.CopyId.bar, Loader.CopyId.use, Loader.CopyId.block] at hb ⊢
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    refine vec_getD ?_ ?_ rfl rfl x <;> (try rw [hb]) <;> rfl
  · have hb := hblock _ rfl
    simp only [Loader.CopyId.bar, Loader.CopyId.use, Loader.CopyId.block] at hb ⊢
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    refine vec_getD ?_ ?_ rfl rfl x <;> (try rw [hb]) <;> rfl
  all_goals
    simp only [Loader.CopyId.dst, Loader.CopyId.bar, Loader.CopyId.use, Loader.CopyId.stage,
      FBar.regionOff, FBar.copyBytes, Loc.mk.injEq, true_and, reduceCtorEq, ↓reduceIte,
      Fin.isValue, Fin.val_zero, Fin.val_one]
    (try split_ifs) <;> omega

/-- **`RingFacts.write`**: a tensor write is a copy's on a ring full barrier of the pair's even
CTA, into that barrier's region of its own CTA. -/
theorem RingFacts_write : ∀ {g k x y z : Nat} {l : Loc},
    AsyncCovers X (g, k) (.write (.load x y z)) l →
      ∃ pc a sp, ∃ b : FBar, X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ ∧ b.isFull ∧
        sp.mbar = b.loc L (pairBase L g) ∧ InRegion L (ctaOf L g) b l := by
  rintro g k x y z l ⟨acc, w, ⟨-, sp, a, ⟨pc, he⟩, hloc, hsz⟩, hcov⟩
  obtain ⟨d, -, -, -, hi, -, u, j, hs, hci, -⟩ := Loader.copy_origin hpre hX ht he
  refine ⟨pc, a, sp, _, he, Loader.bar_isFull L _, hci.mbar, ?_⟩
  have hl := Acc.loc_of_one hcov hsz
  subst hl
  have hone := hi.one u j (.inr hs)
  obtain ⟨⟨outer, desc, origin, sb, rows⟩, mbar, ca, grp⟩ := sp
  obtain ⟨hmap, hout, -, hdst, -, -, hdesc, -, -, -⟩ := hci
  simp only at hout hdst hdesc
  subst hout hdst
  have hD := Loader.copy_desc hpre hmap hdesc
  subst hD
  obtain ⟨h0, hR, hfm, hsw⟩ := Loader.copyMap_box (P := P) (L := L) ⟨u, j, d.i, d.t⟩
  obtain ⟨hx, hy, hb⟩ := TensorCopy.writeLoc_bounds hloc
  simp only at hx hy hb
  rw [h0] at hx
  rw [hR] at hy
  rw [hfm] at hb
  rw [TensorCopy.box_writeLoc h0 hR hfm hsw (by omega) (by omega) hb] at hloc
  have hoff := TensorCopy.box_offset_lt
    (base := L.sharedBase + Loader.CopyId.dst L ⟨u, j, d.i, d.t⟩) (by omega) hy hb
  simp only [Option.some.injEq] at hloc
  rw [← hloc]
  have hev := Loader.uB_even L d.i
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only at hoff ⊢ <;>
    cases u <;> simp only [Loader.UseK.copies] at hone <;>
    simp only [Loader.CopyId.dst, Loader.CopyId.bar, Loader.CopyId.use, Loader.CopyId.stage,
      FBar.regionOff, FBar.regionSize, FBar.copyBytes, reduceCtorEq, ↓reduceIte] at hoff ⊢ <;>
    (try split_ifs at hoff ⊢) <;> omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof
