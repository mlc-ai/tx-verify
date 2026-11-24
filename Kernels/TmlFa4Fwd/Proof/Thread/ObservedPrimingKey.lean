-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInitialKeyGroup
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingPacketGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX
open PTX.Kernels.TmlFa4Fwd.Loader (packetPlanePc kCopyPc)

/-- A member of the published priming K group is the actual vector on its destination. -/
theorem PublishedCopyGroup.primingKeyMember {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} (group : PublishedCopyGroup l X issue) {target : Loc}
    (hIssue : X.AsyncArrive issue target true)
    (hPacket : group.publication.packet = ⟨.priming, .key⟩)
    {j : Nat} {spec : AsyncCopy.Spec} (hMember : (j, spec) ∈ group.copies) :
    ∃ pair : Fin 16, ∃ upper : Bool, PrimingKeyVector X (issue.1, j) pair upper spec ∧
      let addr := kvCopyAddress l.sharedBase group.publication.slot (issue.1 % l.block) pair upper
      spec.dst = {loc := ⟨.shared, issue.1 / l.block, addr⟩, size := 16} := by
  have hPeriod := congrArg Packet.period hPacket
  obtain ⟨site, hSite, hGeometry⟩ := primingGroupGeometry hp hX group hIssue hPeriod
  rw [hPacket] at hSite
  have hZero : site = 0 := by fin_cases site <;> first | rfl | cases hSite
  subst site
  obtain ⟨pair, upper, hGet, hDst⟩ := hGeometry hMember
  have hPc : packetPlanePc 0 pair upper = kCopyPc pair + if upper then 1 else 0 := by
    fin_cases pair <;> cases upper <;> decide
  exact ⟨pair, upper, by simpa only [PrimingKeyVector, hPc] using hGet, hDst⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
