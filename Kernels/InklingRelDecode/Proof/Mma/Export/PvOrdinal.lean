-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.History
import Kernels.InklingRelDecode.Proof.Mma.Machine
public import Kernels.InklingRelDecode.Proof.Lib.MmaPcs

/-! # A PV step has an ordinal of a block

A PV issue of a lane of the MMA warp is made at a PV site of the loop, after as many PV polls as
the loop's counter, which is at most the number of blocks. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Flow PTX.Frame

private theorem pv_site' (j : Fin 8) : ∀ s : Site, pvPc j = s.pc → s = .pv j := by
  fin_cases j <;> intro s <;> cases s <;>
    repeat' first | decide +kernel | (rename_i j'; revert j')

/-- **The PV polls before a PV issue are at most the number of blocks.** -/
public theorem pv_ordinal_le {Q L m X g k d s acc mask} {j : Fin 8} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (warp : g % L.block / 32 = 7)
    (he : X.get (g, k) = some ⟨Lib.pvIssue j, .tc (.mma d s acc mask)⟩) :
    pollRound 2510 ((X.tr g).take k) ≤ Lib.blocksOf Q L (g / L.block) := by
  have pcs : Lib.pvIssue j = pvPc j := by fin_cases j <;> rfl
  have range : 2422 < pvPc j ∧ pvPc j < 2557 ∧ pvPc j ≠ 2422 := by fin_cases j <;> decide
  obtain ⟨w, x, r, d', n, hs, inv⟩ := worker_event hp hX hf he (by simp)
    (by rw [pcs]; exact range.1.trans' (by decide)) (by rw [pcs]; exact range.2.1)
    (by rw [pcs]; exact range.2.2)
  cases r with
  | loader =>
    have wrong : g % L.block / 32 = 6 := inv.1
    omega
  | mma =>
    obtain ⟨_, ref, -, hp', -⟩ := inv
    have hi := (reached_table hf (lt_of_get hX he) (noUbBefore_of_get hX he) hs).1
    have loop : Mma.Inv d' := hi.1
    have pc := event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
    obtain ⟨st, i, v⟩ := d'
    obtain rfl := pv_site' j st (by rw [← pcs]; exact pc)
    have limit := ref_count ref rfl
    change low v = Lib.blocksOf Q L (g / L.block) at limit
    have pv := (fcount hs (.poll 2510)).symm.trans hp'
    change pollRound 2510 _ = i at pv
    change 0 < i ∧ i ≤ low v ∧ _ at loop
    rw [pv]
    omega

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
