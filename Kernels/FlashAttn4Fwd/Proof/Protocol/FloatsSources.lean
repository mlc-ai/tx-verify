-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.FloatsLoad
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ScoreHandoff
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OAcc

@[expose] public section

/-! # The sources of the Tensor Memory loads

`loadSources` proves `Floats.LoadSources`: each register of a Tensor Memory load has a read source
that is an MMA. A softmax load of tile `u` reads the last QK MMA of tile `u` writing the cell
(`Score.s_readSource`; the stores of `P` into the columns of `S` are not floats and are not
sources, since the S-full object orders the QK MMAs of tile `u` before the load and the P-ready
object the load before the next tile's MMAs). A correction load of credit `q` reads the last PV
MMA of tile `q - 1` writing the cell (`OAcc.o_readSource`).

The theorems `Score.s_readSource` and `OAcc.o_readSource` take the source as an argument. Here it
is constructed (`last_mma`): among the MMAs of the cell's issuing thread whose commit or poll
count is at most the tile's, the one of the greatest index. It exists by the cover premises
(`SoftCover`, `CorrCover`: the MMAs of tile `u` write every cell of the tile's region), and its
count is the tile's. The values and the release order are premises of the value and lifetime
protocols (`hv`, `TmemLive`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma

noncomputable section

namespace Floats

variable {P : Params} {L : Launch} {X : Execution} {K : Kernel} {mem0 : Mem0}

/-- **SoftCover**: the QK MMAs of the score tile a softmax load reads write each cell it loads. -/
def SoftCover (L : Launch) (X : Execution) : Prop :=
  ∀ {h i a j : Nat} {vals : List Value}, h < L.threads → warpOf L h < 8 →
    X.TLd (h, i) a vals .s32x32b → j < vals.length →
    ∃ x, IsMma X x ∧ X.MmaCell x (tcDataCell32 L h a j) ∧
      sCommits L X x.1 (warpOf L h / 4) x.2 + 1 = sPolls L X h (warpOf L h / 4) i

/-- **CorrCover**: the PV MMAs of the tile before a correction load's credit write each cell it
loads. -/
def CorrCover (L : Launch) (X : Execution) : Prop :=
  ∀ {h i a j st : Nat} {vals : List Value}, h < L.threads → 8 ≤ warpOf L h →
    warpOf L h < 12 → X.TLd (h, i) a vals .s32x32b → j < vals.length →
    InO st (tcDataCell32 L h a j) →
    ∃ x, IsMma X x ∧ X.MmaCell x (tcDataCell32 L h a j) ∧
      pPolls L X x.1 st x.2 = pArr L X h st i

/-- **TmemLive**: an access completes before every release of an allocation that covers its cell
(through the paired allocation for a cell of the other CTA of the pair, EXT-PAIR-ALLOC-ORDER). -/
def TmemLive (L : Launch) (X : Execution) : Prop :=
  ∀ {e : EvId} {cell : Cell}, Tmem.Pair.Access L X e cell →
    ∀ cta r, r ∈ X.tmemHistory cta → Tmem.Pair.Covers L X r cell.cta e cell.column →
      ∀ d, Tmem.Pair.ReleaseOf L X r d → TcMma.CompletedBefore L X e d

/-- The MMAs writing one cell are one thread's. -/
theorem mma_lead (ht : ScoreFacts L X) {x : EvId} {cell : Cell} (hx : IsMma X x)
    (hc : X.MmaCell x cell) : ctaOf L x.1 = leadCta cell.cta := by
  obtain ⟨d, s, acc, mask, hi⟩ := hx
  obtain ⟨-, -, -, st, -, h | h⟩ := ht.mma_cells hi
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
  have hle : x0.2 ≤ (X.tr x0.1).length := h0.lt.le
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
  have hlt : xb ≤ k := hmax xb hx.lt.le hQx
  rcases Nat.lt_or_eq_of_le hlt with h | h
  · exact .inr h
  · exact .inl (by rw [h])

/-- **A softmax load register's source is an MMA**, given the values of the MMAs writing the
loaded cell that completed before the load. -/
theorem soft_source (hpre : Pre P L mem0) (hX : Consistent L K asms mem0 X)
    (ht : ScoreFacts L X) (ho : OAccFacts L X) (hP : Score.PReadyHandoff L X)
    (h2 : Score.P2Gate L X) (hS : Score.SFullHandoff L X) (hc : SoftCover L X) {h i a j : Nat}
    (hv : ∀ {x d s acc mask}, X.MmaIssue x d s acc mask → X.MmaCell x (tcDataCell32 L h a j) →
      DoneBefore L X x (h, i) → CompletedValues L asms X x)
    (hl : TmemLive L X) {vals : List Value} (hh : h < L.threads)
    (hw : warpOf L h < 8) (hld : X.TLd (h, i) a vals .s32x32b) (hj : j < vals.length) :
    ∃ src value, ReadSource L X .ld src (h, i) (tcDataCell32 L h a j) ∧
      Wrote L asms X src (tcDataCell32 L h a j) value ∧ IsMma X src := by
  obtain ⟨x0, hx0, hxc0, hn⟩ := hc hh hw hld hj
  obtain ⟨src, hsrc, hsc, hF, hlast⟩ := last_mma ht
    (fun x => sCommits L X x.1 (warpOf L h / 4) x.2)
    (fun g k k' hk => countP_take_mono _ (X.tr g) hk) hx0 hxc0
  have hcnt : sCommits L X src.1 (warpOf L h / 4) src.2 + 1 = sPolls L X h (warpOf L h / 4) i := by
    omega
  have hS' := (ht.soft_ld hh hw hld).1 j hj
  have hst : warpOf L h / 4 < 2 := by omega
  obtain ⟨d, s, acc, mask, hsi⟩ := id hsrc
  have hlead : leadCta (ctaOf L src.1) = leadCta (ctaOf L h) := by
    rw [(Score.mma_in ht hsrc).2, ← (Score.mma_s ht hsi hsc hS' hst _ hsc).2]
    rfl
  have hdone := Score.s_doneBefore ht hS hh hw hsrc hlead hcnt.le (Score.TLd.lt hld)
  obtain ⟨value, hres⟩ := hv hsi hsc hdone (hdone.done hX.tcCommit) _ hsc
  have hla : Tmem.Pair.Access L X (h, i) (tcDataCell32 L h a j) :=
    .inr (.inl ⟨j, loadCell32 hld hj⟩)
  exact ⟨src, value, Score.s_readSource hpre ht ho hP h2 hS hh hw hld hj hsrc hsc hcnt hlast
    (fun cta r hr hcov rel hrel => .inl (hl hla cta r hr hcov rel hrel)), .inl hres, hsrc⟩

/-- **A correction load register's source is an MMA**, given the values of the MMAs writing the
loaded cell that completed before the load. -/
theorem corr_source (hpre : Pre P L mem0) (hX : Consistent L K asms mem0 X)
    (ht : ScoreFacts L X) (ho : OAccFacts L X) (hP : Score.PReadyHandoff L X)
    (hR : OAcc.OReady L X) (hc : CorrCover L X) {h i a j : Nat}
    (hv : ∀ {x d s acc mask}, X.MmaIssue x d s acc mask → X.MmaCell x (tcDataCell32 L h a j) →
      DoneBefore L X x (h, i) → CompletedValues L asms X x)
    (hl : TmemLive L X) {vals : List Value} (hh : h < L.threads)
    (h8 : 8 ≤ warpOf L h) (h12 : warpOf L h < 12) (hld : X.TLd (h, i) a vals .s32x32b)
    (hj : j < vals.length) :
    ∃ src value, ReadSource L X .ld src (h, i) (tcDataCell32 L h a j) ∧
      Wrote L asms X src (tcDataCell32 L h a j) value ∧ IsMma X src := by
  obtain ⟨st, -, hcells, -, -⟩ := ho.corr_ld hh h8 h12 hld
  have hO := hcells j hj
  obtain ⟨x0, hx0, hxc0, hn⟩ := hc hh h8 h12 hld hj hO
  obtain ⟨src, hsrc, hsc, hF, hlast⟩ := last_mma ht (fun x => pPolls L X x.1 st x.2)
    (fun g k k' hk => countP_take_mono _ (X.tr g) hk) hx0 hxc0
  have hcnt : pPolls L X src.1 st src.2 = pArr L X h st i := hF.trans hn
  obtain ⟨d, s, acc, mask, hsi⟩ := id hsrc
  have hcs : ctaOf L src.1 = leadCta (tcDataCell32 L h a j).cta := OAcc.mma_cta ht hsi hsc hO
  have hdone : DoneBefore L X src (h, i) :=
    hR hh h8 h12 hld hcells hsrc ⟨_, hsc, hO⟩ hcs hcnt.le
  obtain ⟨value, hres⟩ := hv hsi hsc hdone (hdone.done hX.tcCommit) _ hsc
  have hla : Tmem.Pair.Access L X (h, i) (tcDataCell32 L h a j) :=
    .inr (.inl ⟨j, loadCell32 hld hj⟩)
  exact ⟨src, value, OAcc.o_readSource hpre ht ho hP hR hh h8 h12 hld hj hO hsrc hsc hcnt hlast
    (fun cta r hr hcov rel hrel => .inl (hl hla cta r hr hcov rel hrel)), .inl hres, hsrc⟩

/-- **Every register of a Tensor Memory load has a read source that is an MMA.** -/
theorem loadSources (hpre : Pre P L mem0) (hX : Consistent L K asms mem0 X)
    (ht : ScoreFacts L X) (ho : OAccFacts L X) (hP : Score.PReadyHandoff L X)
    (h2 : Score.P2Gate L X) (hS : Score.SFullHandoff L X) (hR : OAcc.OReady L X)
    (hsc : SoftCover L X) (hcc : CorrCover L X)
    (hv : ∀ {i d s acc mask}, X.MmaIssue i d s acc mask → CompletedValues L asms X i)
    (hl : TmemLive L X) : LoadSources L X := by
  intro h i a j vals hh hld hj
  obtain ⟨-, h12⟩ := ht.tc_role (.inl hld)
  by_cases h8 : warpOf L h < 8
  · exact soft_source hpre hX ht ho hP h2 hS hsc (fun hx _ _ => hv hx) hl hh h8 hld hj
  · exact corr_source hpre hX ht ho hP hR hcc (fun hx _ _ => hv hx) hl hh (by omega) h12 hld hj

end Floats

end
end PTX.Kernels.FlashAttn4Fwd.Proof
