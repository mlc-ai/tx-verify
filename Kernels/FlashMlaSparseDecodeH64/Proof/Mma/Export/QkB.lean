-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MmaSlot
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot
public import Lemmas.Flow.Counted
public import Lemmas.Flow.NotCommit
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Desc
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.LocCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode

@[expose] public section

/-! # The B operand and the tile use of a QK MMA

A QK MMA (D at column 400) of the MMA warp is QK MMA `k` of a block `d` (the `24 d + k`-th MMA
issue): its B descriptor is the key layout of the dequantized tile `d % 2` (`keyDesc`, `qkD`), and
at it the lane has polled `dequantReady (d % 2)` `u + 1` times and committed `svDone (d % 2)`
`u` times, `u = ringUses 2 (d % 2) d` (`mma_qkB`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MmaFoot MbarRow

private theorem cls_mma (e : Event) : Mma.cls .mma e = isMmaIssue e := by
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | wait q p ok a sc => cases ok <;> simp [Mma.cls, Mma.inRole, Mma.kindOf, isMmaIssue]
  | tc t => cases t <;> simp [Mma.cls, Mma.inRole, Mma.kindOf, isMmaIssue]
  | _ => simp [Mma.cls, Mma.inRole, Mma.kindOf, isMmaIssue]

private theorem issues_eq (xs : List Event) : xs.countP (Mma.cls .mma) = mmaIssues xs :=
  List.countP_congr fun e _ => by rw [cls_mma]

/-- **A QK MMA's B operand and tile use**: block `d`, step `k`, the descriptor `qkD`, B at the key
layout of tile `d % 2`, and the uses of that tile. -/
theorem mma_qkB (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {y i pc : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (he : X.get (y, i) = some ⟨pc, .tc (.mma 400 s acc mask)⟩)
    (hat : MbarRow.MmaAt L y pc) :
    ∃ d k, k < 16 ∧ mmaIssues ((X.tr y).take i) = 24 * d + k ∧ s.descriptor = qkD ∧
      s.b = keyDesc (L.sharedBase + 65536 * (d % 2)) k ∧
      s.lowCta = y / L.block ∧ ∀ j : Fin 2, j.val = d % 2 →
        okPolls (mbarLoc L (y / L.block) (.dequantReady j)) ((X.tr y).take i) =
          ringUses 2 j.val d + 1 ∧
        ((X.tr y).take i).countP (PTX.Flow.commitsTo (mbarLoc L (y / L.block) (.svDone j))) =
          ringUses 2 j.val d := by
  obtain ⟨hw, hlo, hhi⟩ := hat
  have hg : y < L.threads := Frame.lt_of_get hX he
  have hb : 0 < L.block := by rw [hp.block]; decide
  have hgs : L.ctaGroup (y / L.block) .one = some [y / L.block] :=
    ctaGroup_self hp ((Nat.div_lt_iff_lt_mul hb).2 hg)
  obtain ⟨d, hR, ⟨hpc, hE⟩, hl, -⟩ := mma_at hp hX hFw he (fun _ h => by cases h) ⟨hlo, hhi⟩
  have hc := hR (take_noUb hX he)
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site
  case leave s' => exact absurd rfl (hl s')
  case qk k =>
    obtain ⟨⟨-, -, -, -, -, hpha, -⟩, hn⟩ := (Mma.core_loop (by rfl)).mp hc
    have hh : cnt.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
    dsimp only at hpha
    subst hpha
    rcases hE with ⟨s'', hk, haT, hdi, ⟨ctas, hct, hcl, -⟩, -, hBd⟩ | ⟨f, hf⟩
    · cases hk
      have hD := qkD_eq hdi
      rw [hD, show qkD.group = .one from rfl, hgs] at hct
      cases hct
      simp only [List.head?_cons, Option.some.injEq] at hcl
      rw [Mma.qkBW_decode hp hh k.isLt] at hBd
      have hkk := k.isLt
      refine ⟨cnt.toNat, k.val, hkk, ?_, hD, (Option.some.inj hBd).symm, hcl.symm,
        fun j hj => ⟨?_, ?_⟩⟩
      · rw [← issues_eq, hn _ (by simp)]
        simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.idx, Mma.mmaIn,
          show ¬ 2 + k.val ≤ 1 by omega, show 2 + k.val ≤ 18 by omega]
      · have hP := lane4_okPolls hp hX hFw hw i (loc L y (.dequantReady j))
        rw [hn _ (by simp), Mma.cnt_ready hp] at hP
        simp only [loc] at hP
        rw [hP]
        unfold Mma.useAt Mma.ind
        have hk1 : 1 ≤ (Mma.Site.qk k).idx := by simp only [Mma.Site.idx]; omega
        simp only [hj, true_and, hk1, ↓reduceIte]
      · have hC := lane4_commits hp hX hFw hw i (loc L y (.svDone j))
        rw [hn _ (by simp), Mma.cnt_sv hp] at hC
        simp only [loc] at hC
        rw [flow_commitsTo, hC]
    · cases hf
  all_goals simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE
  case pv k =>
    obtain ⟨⟨h4, -⟩, -⟩ := hE
    simp only [Mma.pvCol] at h4
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
