-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Lib.StaticCode
public import Kernels.TmlFa4Fwd.Spec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A commit's target -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A commit's targets are the issuing CTA's barrier**: in a one-dimensional launch with
clusters of one CTA, a commit resolves (`noTcCommitUnsafe`) to the issuer's CTA alone. -/
theorem commit_target (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k pc : Nat}
    {s : TcCommit.Spec} {rank : Fin 16} {l : Loc}
    (he : X.get (g, k) = some ⟨pc, .tc (.commit s)⟩) (ht : TcCommit.target s rank = some l) :
    l = ⟨.shared, g / L.block, s.mbar.addr⟩ := by
  have hsafe : TcCommitIssueSafe L (g, k) s := by
    by_contra hn
    exact noTcCommitUnsafe hp hX ⟨(g, k), s, ⟨pc, he⟩, hn⟩
  obtain ⟨-, hres, -⟩ := hsafe
  have hOne := hp.cluster.2.2
  have h1 := hp.cluster.1
  unfold TcCommit.resolve at hres
  split_ifs at hres
  simp only [Option.some.injEq] at hres
  rw [← hres] at ht ⊢
  unfold TcCommit.target at ht
  split_ifs at ht with hr
  simp only [Option.some.injEq] at ht
  subst ht
  simp only [Launch.oneDim_clusterSizeOf hOne, h1] at hr
  simp only [Launch.oneDim_clusterStart hOne, Launch.oneDim_clusterOfCta hOne, h1,
    Nat.div_one, Nat.mul_one]
  have : rank.val = 0 := by omega
  rw [this, Nat.add_zero]

end
end PTX.Kernels.TmlFa4Fwd.Proof
