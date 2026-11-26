-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Origin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane

@[expose] public section

/-! # The MMA warp's query loads: their box origin

A tensor load of the MMA warp is one of the eight query loads; its box starts at column `64 c`,
head `0` of the query row and batch of the lane's CTA (`%ctaid.x`, `%ctaid.y`), and is a tile
(no gather rows). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The origin of a query load**: a tensor load of the MMA warp has the origin
`(64 c, 0, %ctaid.x, %ctaid.y)` for a `c < 8` and no gather rows. -/
theorem mma_loadOrigin (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : MbarRow.MmaAt L g e.pc) {a : Nat} {s : TensorCopy.Spec}
    (hk : e.kind = .tensorIssue a s) :
    s.rows = none ∧ ∃ c < 8, BoxOrigin s.origin [64 * c, 0, ctaidX L g, ctaidY L g] := by
  obtain ⟨-, hlo, hhi⟩ := hat
  obtain ⟨d, -, ⟨-, hE⟩, hlv, -⟩ :=
    mma_at hp hX hFw he (fun _ h => by rw [hk] at h; cases h) ⟨hlo, hhi⟩
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  cases site
  case qLoad i =>
    rcases hE with ⟨a', s', hk', -, -, -, -, -, hrows, hor⟩ | ⟨f, hf⟩
    · cases hk'
      exact ⟨hrows, i.val, i.isLt, hor⟩
    · cases hf
  case leave i => exact absurd rfl (hlv i)
  all_goals simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
