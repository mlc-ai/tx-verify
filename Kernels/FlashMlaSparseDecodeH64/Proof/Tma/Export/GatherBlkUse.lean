-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.GatherVocab
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.CoordLoad
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Lemmas.Flow.Counted
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.GatherDst
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.ClsRd
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.ObjCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefStep

@[expose] public section

/-! # The block of a gather and its raw tile use

A gather `q` of the TMA lane in block `r` (`64 r + ...` coordinate reads before it, the count
`tma_gatherBlk` names) loads raw tile `slot2 r` on `rawReady` after `16 u + q` earlier loads on it,
`u = ringUses 2 (slot2 r) r` (`tma_gatherBlkUse`): `tma_gatherBlk` and `tma_gatherUse` both come
from the lane's loop counter, which is `r`; this file states them for one gather. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- **A gather's block, tile and use.** -/
theorem tma_gatherBlkUse (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hat : MbarRow.TmaAt L g e.pc) {a : Nat}
    {s : TensorCopy.Spec} (hk : e.kind = .tensorIssue a s) :
    ∃ q < 16, ∃ r, e.pc = gatherPc q ∧
      ((X.tr g).take k).countP tmaRd = 64 * r + (if q = 15 then 64 else 4 * q + 8) ∧
      s.mbar = mbarLoc L (g / L.block) (.rawReady (MbarRow.slot2 r)) ∧
      s.sharedBase = ⟨.shared, g / L.block, L.sharedBase +
        (36864 * (MbarRow.slot2 r).val + (131072 + 2304 * q))⟩ ∧
      ((X.tr g).take k).countP (issuesTo (mbarLoc L (g / L.block) (.rawReady (MbarRow.slot2 r)))) =
        16 * ringUses 2 (MbarRow.slot2 r) r + q := by
  have hub : ∀ f, e.kind ≠ .ub f := by intro f h; rw [hk] at h; cases h
  obtain ⟨hw5, hr⟩ := hat
  obtain ⟨d0, -, -, ⟨hpc, hE⟩, hl', hw⟩ := tma_at hp hX hFw he hub hr
  obtain ⟨i, hs⟩ := Tma.ev_gather hl' ⟨hpc, hE⟩ hk
  have hpcR : 2165 < e.pc ∧ e.pc < 2332 := by
    rw [hpc, hs]
    exact (by decide : ∀ i : Fin 16, 2165 < (Tma.Site.gather i).pc ∧
      (Tma.Site.gather i).pc < 2332) i
  obtain ⟨d, n, t, ins, o, q, hσ, hat', hs', hc, hf, hmain, hL, hev, hn⟩ :=
    tma_gather_at_n hp hX hFw he hpcR hk
  have hpcq : e.pc = gatherPc q.val := by
    have h1 : e.pc = d.site.pc := hev.1
    rw [h1, hs']; unfold Tma.Site.pc gatherPc; rfl
  obtain ⟨-, hK⟩ := hev
  simp only [Tma.EvK, hs'] at hK
  obtain ⟨a', s', hK, hmb⟩ | ⟨f, hK⟩ := hK
  · rw [hk] at hK
    simp only [Kind.tensorIssue.injEq] at hK
    obtain ⟨-, rfl⟩ := hK
    obtain ⟨-, -, -, -, -, hbuf, -⟩ := hL
    refine ⟨q.val, q.isLt, d.cnt.toNat, hpcq, ?_, ?_, ?_, ?_⟩
    · have := hn .rd (by simp)
      rw [show Tma.cls .rd = tmaRd from funext Tma.cls_rd] at this
      rw [this]
      simp only [Tma.cntAt, Tma.proCnt, Tma.loopCnt, Bool.false_eq_true, ↓reduceIte, hs',
        Tma.Site.rdN]
      omega
    · exact hmb.trans ((Tma.raw_of hbuf).trans (Tma.raw_loc hp (MbarRow.slot2 d.cnt.toNat)))
    · have hb2 := Nat.mod_lt d.cnt.toNat (by decide : 0 < 2)
      obtain ⟨hsb, -⟩ := Tma.gather_dst hp hat' hs' hc hf hmain hb2 hbuf hk
      exact hsb
    · show ((X.tr g).take k).countP
        (issuesTo (MbarRow.loc L g (.rawReady (MbarRow.slot2 d.cnt.toNat)))) = _
      rw [lane5_issues hp hX hFw hw, hn _ (by simp), Tma.tcnt_gather hp]
      simp [Tma.ind, hs', Tma.Site.gN, MbarRow.slot2]
  · rw [hk] at hK
    cases hK

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
