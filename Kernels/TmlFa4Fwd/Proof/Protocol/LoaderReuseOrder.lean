-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderOperandCoverage
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderGuardedGroup
import Lemmas.Async.AsyncChain

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy
open Thread.Loader (OrderedGuardedReuse PublishedCopyGroup readyObject earlierPublication
  positiveGenerationOrderedGuard CachePlane copyDestination)
open Thread.Mma (EmptyReleaseAt)
open Thread.Mma.Observation (emptyObject)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- An observed release orders its completed operand read before every overlapping
vector of the guarded group. -/
theorem observedOperandBeforeGroupReuse {publication mma : EvId} {slot : Fin 3}
    {g k d index j : Nat} {isB accum : Bool} {mask : List Nat} {op : TcMma.OperandSpec} {loc : Loc}
    {spec : Spec} (guard : OrderedGuardedReuse l X publication slot)
    (group : PublishedCopyGroup l X publication)
    (release : EmptyReleaseAt l X (emptyObject l guard.acquire.1 slot) g k)
    (hSeen : MbarObserved X release.record.id (.thread guard.acquire))
    (hMma : X.MmaIssue mma d op accum mask) (hEarlier : TraceBefore X mma (g, release.index))
    (hOperand : op.byteLoc (if isB then .b else .a) index = some loc)
    (hMember : (j, spec) ∈ group.copies) (hCover : spec.dst.Covers loc) :
    X.AsyncPresent mma (.mmaRead isB index) ∧
      modelCausality l X loc (.async mma (.mmaRead isB index))
        (.async (publication.1, j) (.write .copy)) :=
  observedOperandBeforeReuse hp hX release hSeen guard.empty hMma hEarlier hOperand
    (guard.resumesCopy group hMember) ((group.member j spec).mp hMember).2.2 hCover

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
