-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
public import Kernels.InklingRelDecode.Proof.Common.Export.Mbar
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.InitFirst
public import Kernels.InklingRelDecode.Proof.Protocol.Life.Use
public import Kernels.InklingRelDecode.Proof.Protocol.Life.Loads
public import Kernels.InklingRelDecode.Proof.Protocol.Life.Commit
public import Kernels.InklingRelDecode.Proof.Protocol.Life.Mma
public import Kernels.InklingRelDecode.Proof.Protocol.Life.Scores
public import Kernels.InklingRelDecode.Proof.Top.Safe.UbWeaken

@[expose] public section

/-! # ERR-SHARED-LIFETIME: shared memory outlives its asynchronous uses

By `Life.no_sharedLifetime` (`Protocol/Life/Use.lean`): every use of shared memory is of the issuing
lane's CTA, a thread's instruction precedes its lane's exit, and an asynchronous use finishes
before an exit of its exited CTA when its operation does: an MMA by the poll of `o_final`
(`Life.mma_finished`), a commit's arrival by the polls of its barrier or the next commit's chain
(`Life.commit_finished`), a tensor load's arrival by a poll of `kv_ready` (`Life.load_observed`).
The score commits are observed by lane zero's score polls (`Life.score_observed`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem Safe.noSharedLifetime (hp : Pre Q L m) {X : Execution} (base : Iface.BaseRead L X)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hu : ¬HasUb X)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) :
    ¬ SharedLifetimeUnsafe L kernel Assumptions.all X :=
  Protocol.Life.no_sharedLifetime hp hX hf rows base
    (Protocol.Life.load_notified hX
      (Protocol.Life.load_observed hp hX hf rows init (NoUbOutside.of_noUb hu)))
    (Protocol.Life.mma_finished hp hX hf rows init base)
    (Protocol.Life.commit_finished hp hX hf rows init
      (Protocol.Life.score_observed hp hX hf rows init fun _ => NoUbLane.of_noUb hu _))

end PTX.Kernels.InklingRelDecode.Proof.Top
