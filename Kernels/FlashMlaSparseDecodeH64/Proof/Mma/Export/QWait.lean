-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.LocCnt

@[expose] public section

/-! # The query wait comes before the query copies

A `tcgen05.cp` of the MMA lane (pcs 1936 to 1980) follows the lane's one successful poll of
`qTma` (pc 1931): the lane has made exactly one successful poll of `qTma` before it
(`mma_cp_qWait`, from the role's counts at the copy sites `qCopy k`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A copy of the MMA lane follows its poll of `qTma`**: one successful poll of `qTma` of its
CTA precedes the copy. -/
theorem mma_cp_qWait (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i pc : Nat} {c : TcCopy.Spec}
    (hi : X.get (g, i) = some ⟨pc, .tc (.cp c)⟩) (hat : MmaAt L g pc) :
    okPolls (mbarLoc L (g / L.block) .qTma) ((X.tr g).take i) = 1 := by
  obtain ⟨hw, hlo, hhi⟩ := hat
  obtain ⟨d, hR, ⟨hpc, hE⟩, hl, -⟩ := mma_at hp hX hFw hi (fun _ h => by cases h) ⟨hlo, hhi⟩
  have hc := hR (take_noUb hX hi)
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE
  case leave s => exact absurd rfl (hl s)
  case qCopy k =>
    have hn := Mma.pro_cnt hc ⟨rfl, by simp, by simp⟩ (c := .acq (loc L g .qTma)) (by simp)
    have hP := lane4_okPolls hp hX hFw hw i (loc L g .qTma)
    simp only at hn
    rw [← hP] at hn
    rw [hn]
    simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.pro, Mma.obj_qTma hp, Mma.obj_qUt hp,
      Mma.obj_ready hp, Mma.obj_so hp, Mma.useAt, ringUses, Mma.mloc_eq_iff, Mma.ind]
    omega

/-- **An MMA of the lane follows its poll of `qTma`**: one successful poll of `qTma` of its CTA
precedes the MMA. -/
theorem mma_mma_qWait (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i pc dc : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.get (g, i) = some ⟨pc, .tc (.mma dc sp acc mask)⟩) (hat : MmaAt L g pc) :
    okPolls (mbarLoc L (g / L.block) .qTma) ((X.tr g).take i) = 1 := by
  obtain ⟨hw, hlo, hhi⟩ := hat
  obtain ⟨d, hR, ⟨hpc, hE⟩, hl, -⟩ := mma_at hp hX hFw hi (fun _ h => by cases h) ⟨hlo, hhi⟩
  have hc := hR (take_noUb hX hi)
  have hP := lane4_okPolls hp hX hFw hw i (loc L g .qTma)
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE
  case leave s => exact absurd rfl (hl s)
  all_goals
    obtain ⟨-, hn⟩ := (Mma.core_loop (by rfl)).mp hc
    have hn1 := hn (.acq (loc L g .qTma)) (by simp)
    simp only at hn1
    rw [← hP] at hn1
    simp only [loc] at hn1 ⊢
    rw [hn1]
    simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.obj_qTma hp, Mma.obj_qUt hp,
      Mma.obj_ready hp, Mma.obj_so hp, Mma.useAt, ringUses, Mma.mloc_eq_iff, Mma.ind]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
