-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Origin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Desc

@[expose] public section

/-! # The query loads of the MMA warp: map, box and origin

A tensor load of the MMA warp is load `a < 8` of the query (`mma_qLoad_spec`): it reads through
the query map, its box starts at feature `64 a` of head 0 of query `ctaid.x` of batch `ctaid.y`,
it has no row coordinates, and its shared box starts `8192 a` bytes after the shared base, in the
issuing CTA. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The spec of a query load**: its index `a < 8`, the query map, the shared box at
`S + 8192 a` of the issuing CTA, no row coordinates, and the box origin `(64 a, 0, q, e)`. -/
theorem mma_qLoad_spec (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc al : Nat} {s : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue al s⟩) (hat : MbarRow.MmaAt L g pc) :
    ∃ a < 8, (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
        ⟨3, mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass⟩ ∧
      s.sharedBase = ⟨.shared, g / L.block, L.sharedBase + 8192 * a⟩ ∧ s.rows = none ∧
      BoxOrigin s.origin [64 * a, 0, ctaidX L g, ctaidY L g] := by
  obtain ⟨-, hlo, hhi⟩ := hat
  obtain ⟨d, -, ⟨-, hE⟩, hlv, -⟩ :=
    mma_at hp hX hFw he (fun _ h => by cases h) ⟨hlo, hhi⟩
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site
  case qLoad i =>
    simp only [Mma.EvK] at hE
    rcases hE with ⟨a', s', hk', -, -, hsb, -, ⟨bb, hb, hmap⟩, hrows, horg⟩ | ⟨f, hf⟩
    · cases hk'
      refine ⟨i.val, i.isLt, ?_, hsb, hrows, horg⟩
      rw [hp.param1Object, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨-, rfl⟩ := hb
      rw [hp.mapQBind] at hmap
      exact (Option.some.inj hmap).symm
    · cases hf
  case leave i => exact absurd rfl (hlv i)
  all_goals simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
