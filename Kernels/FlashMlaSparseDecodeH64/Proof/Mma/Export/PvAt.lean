-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MmaSlot
public import Lemmas.Flow.Counted
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Desc
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.LocCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Desc
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode
import Lemmas.Flow.Polls
import Lemmas.Flow.NotCommit
import Lemmas.Protocol.CountNth

@[expose] public section

/-! # What a PV MMA is: its slot, block, accumulate flag and descriptors

A PV MMA (D below column 256) of the MMA lane is PV MMA `k < 8` at `pvPc k`, with D at
`128 (k % 2)`, the `24 d + 16 + k`-th MMA issue of the lane (`d` the block), accumulating iff
`2 ≤ k` or `1 ≤ d`; its descriptor is `pvD`, its A the P tile's `probDesc (sharedBase + 204800) k`,
in shared memory (`mma_pvAt`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem cls_mma' (e : Event) : Mma.cls .mma e = isMmaIssue e := by
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | wait q p ok a sc => cases ok <;> simp [Mma.cls, Mma.inRole, Mma.kindOf, isMmaIssue]
  | tc t => cases t <;> simp [Mma.cls, Mma.inRole, Mma.kindOf, isMmaIssue]
  | _ => simp [Mma.cls, Mma.inRole, Mma.kindOf, isMmaIssue]

private theorem issues_eq' (xs : List Event) : xs.countP (Mma.cls .mma) = mmaIssues xs :=
  List.countP_congr fun e _ => by rw [cls_mma']

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **A PV MMA of the lane**: PV MMA `k` of block `d`. -/
theorem mma_pvAt {i pc bb : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb s acc mask)⟩) (hat : MmaAt L g pc)
    (hb : bb < 256) :
    ∃ d k, k < 8 ∧ pc = TmemRow.pvPc k ∧ bb = 128 * (k % 2) ∧
      mmaIssues ((X.tr g).take i) = 24 * d + 16 + k ∧ (acc = true ↔ (2 ≤ k ∨ 1 ≤ d)) ∧
      s.descriptor = MmaFoot.pvD ∧ s.aTmem = none ∧
      s.a = MmaFoot.probDesc (L.sharedBase + 204800) k ∧
      (∀ j : Fin 2, okPolls (mbarLoc L (g / L.block) (.soReady j)) ((X.tr g).take i) =
        ringUses 2 j (d + 1)) ∧
      s.b = MmaFoot.valueDesc (L.sharedBase + 65536 * (d % 2)) k ∧ s.lowCta = g / L.block ∧
      ∀ j : Fin 2, j.val = d % 2 →
        okPolls (mbarLoc L (g / L.block) (.dequantReady j)) ((X.tr g).take i) =
          ringUses 2 j.val d + 1 ∧
        ((X.tr g).take i).countP (PTX.Flow.commitsTo (mbarLoc L (g / L.block) (.svDone j))) =
          ringUses 2 j.val d := by
  obtain ⟨hw, hlo, hhi⟩ := hat
  have hg : g < L.threads := Frame.lt_of_get hX hx
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hgs : L.ctaGroup (g / L.block) .one = some [g / L.block] :=
    ctaGroup_self hp ((Nat.div_lt_iff_lt_mul hbl).2 hg)
  obtain ⟨d, hR, ⟨hpc, hE⟩, hl, -⟩ := mma_at hp hX hFw hx (fun _ h => by cases h) ⟨hlo, hhi⟩
  have hc := hR (take_noUb hX hx)
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site
  case pv k =>
    obtain ⟨⟨-, -, hR26, hrR, hcnt, hpha, -⟩, hn⟩ := (Mma.core_loop (by rfl)).mp hc
    rcases hE with ⟨s', hk, haT, hdi, ⟨ctas, hct, hcl, -⟩, hAd, hBd⟩ | ⟨f, hf⟩
    · simp only [Kind.tc.injEq, TcKind.mma.injEq] at hk
      obtain ⟨hbb, rfl, hacc, -⟩ := hk
      have hk8 := k.isLt
      have hpc' : pc = TmemRow.pvPc k.val := by
        simp only [Mma.Site.pc] at hpc
        simp only [TmemRow.pvPc]
        exact hpc
      have hh : cnt.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
      simp only at hpha
      subst hpha
      rw [MmaFoot.pvD_eq hdi, show MmaFoot.pvD.group = .one from rfl, hgs] at hct
      cases hct
      simp only [List.head?_cons, Option.some.injEq] at hcl
      rw [Mma.pvBW_decode hp hh k.isLt] at hBd
      refine ⟨cnt.toNat, k.val, hk8, hpc', ?_, ?_, ?_, MmaFoot.pvD_eq hdi, haT, ?_, ?_,
        (Option.some.inj hBd).symm, hcl.symm, fun j hj => ⟨?_, ?_⟩⟩
      · rw [hbb]
      · rw [← issues_eq', hn _ (by simp)]
        simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.idx, Mma.mmaIn,
          show ¬ 21 + k.val ≤ 1 by omega, show ¬ 21 + k.val ≤ 18 by omega,
          show ¬ 21 + k.val ≤ 20 by omega]
        omega
      · rw [hacc]
        simp only at hR26 hrR hcnt
        have hr32 : cnt.toNat < 2 ^ 32 := by omega
        obtain ⟨a, ha⟩ : ∃ a, cnt.toNat = a := ⟨_, rfl⟩
        rw [ha] at hcnt hr32 ⊢
        rw [hcnt]
        unfold Mma.pvAcc
        by_cases h2 : k.val < 2
        · simp only [h2, ↓reduceIte]
          rw [Arith32.scmpi_ne_b_W hr32 (by norm_num) (by norm_num)]
          by_cases ha0 : a = 0
          · have e0 : Arith32.scmpi .ne .b (Arith32.i32 0) 0 = false := by decide
            simp [ha0, Arith32.sel, e0]
            omega
          · have e1 : Arith32.scmpi .ne .b (Arith32.i32 1) 0 = true := by decide
            simp [ha0, Arith32.sel, e1]
            omega
        · simp only [h2, ↓reduceIte]
          simp
          omega
      · rw [Mma.pvAW_decode hp k.isLt] at hAd
        exact (Option.some.inj hAd).symm
      · intro j
        have hP := lane4_okPolls hp hX hFw hw i (loc L g (.soReady j))
        rw [hn _ (by simp), Mma.cnt_so hp] at hP
        simp only [loc] at hP
        rw [hP]
        simp only [Mma.Site.idx]
        unfold Mma.useAt Mma.ind ringUses
        split_ifs <;> omega
      · have hP := lane4_okPolls hp hX hFw hw i (loc L g (.dequantReady j))
        rw [hn _ (by simp), Mma.cnt_ready hp] at hP
        simp only [loc] at hP
        rw [hP]
        unfold Mma.useAt Mma.ind
        have hk1 : 1 ≤ (Mma.Site.pv k).idx := by simp only [Mma.Site.idx]; omega
        simp only [hj, true_and, hk1, ↓reduceIte]
      · have hC := lane4_commits hp hX hFw hw i (loc L g (.svDone j))
        rw [hn _ (by simp), Mma.cnt_sv hp] at hC
        simp only [loc] at hC
        rw [flow_commitsTo, hC]
    · cases hf
  case qk k =>
    rcases hE with ⟨s', hk, -⟩ | ⟨f, hf⟩
    · simp only [Kind.tc.injEq, TcKind.mma.injEq] at hk
      have h4 : Mma.qkCol = 400 := rfl
      omega
    · cases hf
  case leave i => exact absurd rfl (hl i)
  all_goals simp [Mma.EvK, Mma.PollEv, Mma.CommitEv] at hE

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
