-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.SourceDef
public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.OOrder

@[expose] public section

/-! # The sources of the Tensor Memory loads

A softmax load of tile `u` reads the last QK MMA of tile `u` writing the cell (`soft_source`), a
correction load of credit `q` the last PV MMA of the tile before (`corr_source`), given the values
of the MMAs. -/
namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel} {A : List Assumption}

theorem loadCell32 {h i a j : Nat} {vals : List Value} (hl : X.TLd (h, i) a vals .s32x32b)
    (hj : j < vals.length) : LoadCell L X (h, i) j (tcDataCell32 L h a j) :=
  ⟨a, vals, _, hl, hj, (tcDataCell_s32x32b _ _ _ _).symm⟩

/-- The MMAs writing one cell are one thread's. -/
theorem mma_lead (ht : ScoreFacts L X) {x : EvId} {cell : Cell} (hx : IsMma X x)
    (hc : X.MmaCell x cell) : x.1 / L.block = cell.cta := by
  obtain ⟨d, s, acc, mask, hi⟩ := hx
  obtain ⟨-, -, st, -, h | h⟩ := ht.mma_cells hi
  · exact (h cell hc).2.symm
  · exact (h cell hc).2.symm

theorem mma_thread (ht : ScoreFacts L X) {x y : EvId} {cell : Cell} (hx : IsMma X x)
    (hy : IsMma X y) (hxc : X.MmaCell x cell) (hyc : X.MmaCell y cell) : x.1 = y.1 :=
  ht.tc_one hx (.inl hy) (by rw [mma_lead ht hx hxc, mma_lead ht hy hyc])

/-- **The last MMA.** Among the MMAs writing a cell with `F ≤ F x0`, one of the greatest index
has `F = F x0`, given a monotone `F`. -/
theorem last_mma (ht : ScoreFacts L X) {cell : Cell} (F : EvId → Nat)
    (hmono : ∀ g k k', k ≤ k' → F (g, k) ≤ F (g, k')) {x0 : EvId} (h0 : IsMma X x0)
    (hc0 : X.MmaCell x0 cell) :
    ∃ src, IsMma X src ∧ X.MmaCell src cell ∧ F src = F x0 ∧
      ∀ x, IsMma X x → X.MmaCell x cell → F x ≤ F src → x = src ∨ x.2 < src.2 := by
  classical
  let Q : Nat → Prop := fun k => IsMma X (x0.1, k) ∧ X.MmaCell (x0.1, k) cell ∧
    F (x0.1, k) ≤ F x0
  have hQ0 : Q x0.2 := ⟨h0, hc0, le_rfl⟩
  have hle : x0.2 ≤ (X.tr x0.1).length := (isMma_lt h0).le
  obtain ⟨k, hk, hge, hmax⟩ : ∃ k, Q k ∧ x0.2 ≤ k ∧
      ∀ m, m ≤ (X.tr x0.1).length → Q m → m ≤ k :=
    ⟨Nat.findGreatest Q _, Nat.findGreatest_spec hle hQ0, Nat.le_findGreatest hle hQ0,
      fun m hm hQm => Nat.le_findGreatest hm hQm⟩
  obtain ⟨hk1, hk2, hk3⟩ := hk
  refine ⟨(x0.1, k), hk1, hk2, le_antisymm hk3 (hmono x0.1 x0.2 k hge), ?_⟩
  rintro ⟨xa, xb⟩ hx hxc hFx
  have hxg : xa = x0.1 := mma_thread ht hx h0 hxc hc0
  subst hxg
  have hQx : Q xb := ⟨hx, hxc, hFx.trans hk3⟩
  have hlt : xb ≤ k := hmax xb (isMma_lt hx).le hQx
  rcases Nat.lt_or_eq_of_le hlt with h | h
  · exact .inr h
  · exact .inl (by rw [h])

/-- **A softmax load register's source is an MMA**, given the values of the MMAs writing the
loaded cell that completed before the load. -/
theorem soft_source (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X)
    (ht : ScoreFacts L X) (ho : OAccFacts L X) (hP : PReadyHandoff L X)
    (h2 : P2Gate L X) (hS : SFullHandoff L X) (hT : SourceFacts L X) {h i a j : Nat}
    (hv : ∀ {x d s acc mask}, X.MmaIssue x d s acc mask → X.MmaCell x (tcDataCell32 L h a j) →
      DoneBefore L X x (h, i) → CompletedValues L A X x)
    {vals : List Value} (hh : h < L.threads)
    (hw : Prologue.warpIndex L h < 8) (hld : X.TLd (h, i) a vals .s32x32b) (hj : j < vals.length) :
    ∃ src value, ReadSource L X .ld src (h, i) (tcDataCell32 L h a j) ∧
      Wrote L A X src (tcDataCell32 L h a j) value ∧ IsMma X src := by
  obtain ⟨x0, hx0, hxc0, hn⟩ := hT.soft_cover hh hw hld hj
  obtain ⟨src, hsrc, hsc, hF, hlast⟩ := last_mma ht
    (fun x => sCommits L X x.1 (Prologue.warpIndex L h / 4) x.2)
    (fun g k k' hk => countP_take_mono _ (X.tr g) hk) hx0 hxc0
  have hcnt : sCommits L X src.1 (Prologue.warpIndex L h / 4) src.2 + 1 = sPolls L X h
      (Prologue.warpIndex L h / 4) i := by
    omega
  have hS' := (ht.soft_ld hh hw hld).1 j hj
  have hst : Prologue.warpIndex L h / 4 < 2 := by omega
  obtain ⟨d, s, acc, mask, hsi⟩ := id hsrc
  have hlead : src.1 / L.block = h / L.block := by
    rw [← (mma_s ht hsi hsc hS' hst _ hsc).2]
    rfl
  have hdone := s_doneBefore ht hS hh hw hsrc hlead hcnt.le (tLd_lt hld)
  obtain ⟨value, hres⟩ := hv hsi hsc hdone (hdone.done hX.tcCommit) _ hsc
  have hla : Tmem.Pair.Access L X (h, i) (tcDataCell32 L h a j) :=
    .inr (.inl ⟨j, loadCell32 hld hj⟩)
  exact ⟨src, value, s_readSource hpre ht ho hP h2 hS hh hw hld hj hsrc hsc hcnt hlast
    (fun cta r hr hcov rel hrel => .inl (hT.live hla cta r hr hcov rel hrel)), .inl hres, hsrc⟩

/-- **A correction load register's source is an MMA**, given the values of the MMAs writing the
loaded cell that completed before the load. -/
theorem corr_source (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X)
    (ht : ScoreFacts L X) (ho : OAccFacts L X) (hP : PReadyHandoff L X)
    (hR : OReady L X) (hT : SourceFacts L X) {h i a j : Nat}
    (hv : ∀ {x d s acc mask}, X.MmaIssue x d s acc mask → X.MmaCell x (tcDataCell32 L h a j) →
      DoneBefore L X x (h, i) → CompletedValues L A X x)
    {vals : List Value} (hh : h < L.threads)
    (h8 : 8 ≤ Prologue.warpIndex L h) (h12 : Prologue.warpIndex L h < 12) (hld : X.TLd (h, i) a
        vals .s32x32b)
    (hj : j < vals.length) :
    ∃ src value, ReadSource L X .ld src (h, i) (tcDataCell32 L h a j) ∧
      Wrote L A X src (tcDataCell32 L h a j) value ∧ IsMma X src := by
  obtain ⟨st, -, hcells, -, -⟩ := ho.corr_ld hh h8 h12 hld
  have hO := hcells j hj
  obtain ⟨x0, hx0, hxc0, hn⟩ := hT.corr_cover hh h8 h12 hld hj hO
  obtain ⟨src, hsrc, hsc, hF, hlast⟩ := last_mma ht (fun x => pPolls L X x.1 st x.2)
    (fun g k k' hk => countP_take_mono _ (X.tr g) hk) hx0 hxc0
  have hcnt : pPolls L X src.1 st src.2 = pArr L X h st i := hF.trans hn
  obtain ⟨d, s, acc, mask, hsi⟩ := id hsrc
  have hcs : src.1 / L.block = (tcDataCell32 L h a j).cta := mma_cta ht hsi hsc hO
  have hdone : DoneBefore L X src (h, i) :=
    hR hh h8 h12 (.inl hld) hcells hsrc ⟨_, hsc, hO⟩ hcs hcnt.le
  obtain ⟨value, hres⟩ := hv hsi hsc hdone (hdone.done hX.tcCommit) _ hsc
  have hla : Tmem.Pair.Access L X (h, i) (tcDataCell32 L h a j) :=
    .inr (.inl ⟨j, loadCell32 hld hj⟩)
  exact ⟨src, value, o_readSource hpre ht ho hP hR hh h8 h12 hld hj hO hsrc hsc hcnt hlast
    (fun cta r hr hcov rel hrel => .inl (hT.live hla cta r hr hcov rel hrel)), .inl hres, hsrc⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
