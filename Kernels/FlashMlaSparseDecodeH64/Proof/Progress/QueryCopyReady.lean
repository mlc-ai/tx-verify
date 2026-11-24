-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.QueryCopyWaitBlocker
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.QueryCopy

public section

/-! # Progress of the actual query-copy waits -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

variable (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) (hub : ¬ HasUb X)
    (hguarded : SyncGuarded L kernel X) (hp : Frame.Pending L X g)
include hpre hmax hs ht hub hguarded hp

/-- Once the issuing lane has committed, a query-copy poll in that CTA has an extension.
The extension captures a query operand, finishes its copy, delivers its commit, or polls. -/
theorem no_pending_query_copy_wait_of_commit (hrel : PTX.Step.Released L X g) {d : Machine.ThreadD}
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    (hd : QueryWait d true) {issuer j tag : Nat} {q : Wg1Mma.D} {sp : TcCommit.Spec} {rank : Fin 16}
    (he : X.get (issuer, j) = some ⟨tag, .tc (.commit sp)⟩)
    (hq : Frame.stateAt (Machine.code P L) X issuer j = some (some (.mma q)))
    (hSite : q.site = .qCopyCommit)
    (hTarget : TcCommit.target sp rank = some (Protocol.QueryCopy.object L (ctaOf L g))) :
    False := by
  obtain ⟨_, _, _, hi, hn, hDone⟩ :=
    query_copy_wait_missing_chunk hpre hmax hs ht hub hp hrel hσ hd he hq hSite hTarget
  exact hmax.not_grows
    (query_copy_pending_extension hpre hmax.1 hs ht hi hn hDone hguarded)

/-- The elected MMA lane's pending query-copy poll always has its earlier commit. -/
theorem no_pending_mma_query_copy_wait (hrel : PTX.Step.Released L X g) {d : Wg1Mma.D}
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.mma d)))
    (hd : d.site = .qCopyWait) : False := by
  obtain ⟨_, _, _, hi, hn, hDone⟩ := pending_mma_query_copy_missing_chunk
    hpre hmax hs ht hub hp hrel hσ hd
  exact hmax.not_grows (query_copy_pending_extension hpre hmax.1 hs ht hi hn hDone hguarded)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
