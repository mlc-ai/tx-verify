-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Mma
public import Lemmas.Flow.NotCommit
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Desc
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.LocCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode
import Lemmas.Tensor.LoadBox

@[expose] public section

/-! # The use of a dequantized tile an MMA reads

-- domain: consistent

A QK MMA reads the K tile and a PV MMA the V tile of block `r` in the dequantized tile
`r % 2` (`mmaFoot_pv`). At the MMA the lane has polled `dequantReady (r % 2)` for the uses among
blocks `0 … r` and committed `svDone (r % 2)` for those among blocks `0 … r - 1`
(`Mma.cnt_ready`, `Mma.cnt_sv`): `u + 1` and `u` for `u = ringUses 2 (r % 2) r`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MmaFoot MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The issuing CTA's group of one is the CTA alone. -/
private theorem group_self' (hp : Pre P L m) {g : Nat} (hg : g < L.threads) :
    L.ctaGroup (g / L.block) .one = some [g / L.block] := by
  have hb : 0 < L.block := by rw [hp.block]; decide
  exact ctaGroup_self hp ((Nat.div_lt_iff_lt_mul hb).2 hg)

/-- **The use of a dequantized tile an MMA reads**: a QK or PV MMA of the MMA warp whose operand
byte `l` is in the tile `h0` of its CTA follows `u + 1` successful polls of `dequantReady h0` and
`u` commits to `svDone h0`. -/
theorem mma_dqUse (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc b : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (he : X.get (g, k) = some ⟨pc, .tc (.mma b s acc mask)⟩)
    (hat : MbarRow.MmaAt L g pc) {isB : Bool} {idx : Nat} {l : Loc} {h0 : Fin 2}
    (hF : X.MmaFootprint (g, k) isB idx l) (hl0 : MemRow.LocIn L (g / L.block) (.dequant h0) l) :
    1853 < pc ∧ ∃ u, okPolls (mbarLoc L (g / L.block) (.dequantReady h0)) ((X.tr g).take k) =
        u + 1 ∧
      ((X.tr g).take k).countP
        (PTX.Flow.commitsTo (mbarLoc L (g / L.block) (.svDone h0))) = u := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  obtain ⟨hw, hlo, hhi⟩ := hat
  have hgs := group_self' hp hg
  have hB128 := Mma.base_128 hp 0 rfl
  simp only [Nat.add_zero] at hB128
  have hub : ∀ f, (⟨pc, .tc (.mma b s acc mask)⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  rcases hF with ⟨dc, s', acc', mask', ⟨pc', hget⟩, hl⟩ | ⟨c', j, cta, ⟨pc', hget⟩, -, hcj, -, hl⟩
  swap
  · rw [hget] at he
    cases he
  rw [hget] at he
  cases he
  obtain ⟨d, hR, ⟨hpc, hE⟩, hlv, -⟩ := mma_at hp hX hFw hget hub ⟨hlo, hhi⟩
  have hc := hR (take_noUb hX hget)
  have hcount : ∀ r k', 1 ≤ k' → 1853 < pc → (∀ c, c ≠ .ub →
      ((X.tr g).take k).countP (Mma.cls c) = Mma.cntAt (Mma.objs L g) 31 r k' false c) →
      h0.val = r % 2 →
      1853 < pc ∧ ∃ u,
        okPolls (mbarLoc L (g / L.block) (.dequantReady h0)) ((X.tr g).take k) = u + 1 ∧
        ((X.tr g).take k).countP (PTX.Flow.commitsTo
          (mbarLoc L (g / L.block) (.svDone h0))) = u := by
    intro r k' hk1 hpc' hn hh
    refine ⟨hpc', ringUses 2 h0.val r, ?_, ?_⟩
    · have hP := lane4_okPolls hp hX hFw hw k (loc L g (.dequantReady h0))
      rw [hn _ (by simp), Mma.cnt_ready hp] at hP
      simp only [loc] at hP
      rw [hP]
      unfold Mma.useAt Mma.ind
      simp only [hh, and_self, hk1, ↓reduceIte]
    · have hC := lane4_commits hp hX hFw hw k (loc L g (.svDone h0))
      rw [hn _ (by simp), Mma.cnt_sv hp] at hC
      simp only [loc] at hC
      rw [flow_commitsTo, hC]
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  obtain ⟨-, -, hlo0, hhi0⟩ := id hl0
  have h0lt := h0.isLt
  simp only [Region.lo, Region.size] at hlo0 hhi0
  cases site
  case qk i =>
    obtain ⟨⟨-, -, -, -, -, hpha, -⟩, hn⟩ := (Mma.core_loop (by rfl)).mp hc
    have hh : cnt.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
    dsimp only at hpha
    subst hpha
    rcases hE with ⟨s'', hk, haT, hdi, ⟨ctas, hct, hcl, -⟩, -, hBd⟩ | ⟨f, hf⟩
    · cases hk
      have hD := qkD_eq hdi
      rw [hD, show qkD.group = .one from rfl, hgs] at hct
      cases hct
      cases isB
      · simp [tmemA_none haT] at hl
      · rw [Mma.qkBW_decode hp hh i.isLt] at hBd
        obtain ⟨h1, h2, h3, h4⟩ := key_foot hD
          (Mma.base_128 hp (65536 * (cnt.toNat % 2)) (by omega)) i.isLt
          (Option.some.inj hBd).symm hl
        exact hcount cnt.toNat _ (by simp only [Mma.Site.idx]; omega)
          (by simp only [Mma.Site.pc] at hpc; split_ifs at hpc <;> omega) hn (by omega)
    · cases hf
  case pv i =>
    obtain ⟨⟨-, -, -, -, -, hpha, -⟩, hn⟩ := (Mma.core_loop (by rfl)).mp hc
    have hh : cnt.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
    dsimp only at hpha
    subst hpha
    rcases hE with ⟨s'', hk, haT, hdi, ⟨ctas, hct, hcl, hch⟩, hAd, hBd⟩ | ⟨f, hf⟩
    · cases hk
      have hD := pvD_eq hdi
      rw [hD, show pvD.group = .one from rfl, hgs] at hct
      cases hct
      cases isB
      · rw [Mma.pvAW_decode hp i.isLt] at hAd
        obtain ⟨h1, h2, h3, h4⟩ := prob_foot hD i.isLt (Option.some.inj hAd).symm haT hl
        omega
      · rw [Mma.pvBW_decode hp hh i.isLt] at hBd
        obtain ⟨h1, h2, h3, h4⟩ := value_foot hD
          (Mma.base_128 hp (65536 * (cnt.toNat % 2)) (by omega)) i.isLt
          (Option.some.inj hBd).symm hl
        exact hcount cnt.toNat _ (by simp only [Mma.Site.idx]; omega)
          (by simp only [Mma.Site.pc] at hpc; split_ifs at hpc <;> omega) hn (by omega)
    · cases hf
  case leave i => exact absurd rfl (hlv i)
  all_goals simp [Mma.EvK, Mma.PollEv, Mma.CommitEv] at hE

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
