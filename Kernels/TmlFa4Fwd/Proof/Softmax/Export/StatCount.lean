-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.MemWrite
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Mem
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.Softmax.MbarSite
import Kernels.TmlFa4Fwd.Proof.SmWarp.P2Count
import Kernels.TmlFa4Fwd.Proof.SmWarp.Counts
import Kernels.TmlFa4Fwd.Proof.Lib.NoPicked
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem

@[expose] public section

/-! # The softmax lanes' counts at their statistics stores

A store follows one more credit poll than the lane's arrivals on its barrier with the correction
warps. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (ptsOf passed before inBias inPlain)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat}

private theorem stat_tab (b : Bool) : (∀ s ∈ Softmax.allSites,
    ((∃ r, s = .stat r) ∨ ∃ r, s = .fin r) →
    (ptsOf b (.acquire 192)).countP (before s) = (ptsOf b .nb).countP (before s) + 1) ∧
    (ptsOf b (.acquire 192)).countP inBias = (ptsOf b .nb).countP inBias ∧
    (ptsOf b (.acquire 192)).countP inPlain = (ptsOf b .nb).countP inPlain := by
  refine ⟨?_, by cases b <;> decide +kernel, by cases b <;> decide +kernel⟩
  rintro s - (⟨r, rfl⟩ | ⟨r, rfl⟩) <;> revert b r <;> decide +kernel

/-- **A statistics store's counts.** -/
theorem soft_stat_wr (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h < 8) {pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (h, k) = some ⟨pc, .wr a bs⟩) :
    okPolls (sobj L h 192) ((X.tr h).take k) =
      ((X.tr h).take k).countP (Execution.isBarId (Prologue.warpIndex L h + 3)) + 1 := by
  rcases soft_counts hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, hev, hx⟩ | ⟨d, c, rb, rp, ns, nv, hQ, hF, hev, hc⟩
  · exact (start_mem hev hx trivial).elim
  have hs : (∃ r, d.site = .stat r) ∨ ∃ r, d.site = .fin r := by
    cases hs : d.site <;> simp only [Softmax.Ev, hs] at hev
    case stat r => exact .inl ⟨r, rfl⟩
    case fin r => exact .inr ⟨r, rfl⟩
    all_goals exfalso
    all_goals try simp only [Epilogue.Ev, Softmax.Site.toE, Softmax.tcLdOrUb] at hev
    all_goals repeat' split at hev
    all_goals first | contradiction | simp_all [Softmax.rdOrUb]
  obtain ⟨t1, t2, t3⟩ := stat_tab (Softmax.lz L h)
  rw [soft_isBarId hw, soft_okPolls hw, hc _ rfl, hc _ rfl, hQ.cnt _ rfl, hQ.cnt _ rfl, passed,
    passed, t1 _ (Softmax.mem_allSites _) hs, t2, t3]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
