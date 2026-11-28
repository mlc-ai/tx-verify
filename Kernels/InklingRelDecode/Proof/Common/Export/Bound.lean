-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Common.Bound
import Lemmas.Kernel.BoundU

namespace PTX.Kernels.InklingRelDecode.Proof.Export

public theorem thread_counts {Q L m} (hp : Pre Q L m) :
    ∃ N, ∀ X, Consistent L kernel Assumptions.all m X → Follow Q L X → RoleBytes L X →
      ∀ g<L.threads, (X.tr g).countP Event.counts≤N := by
  refine ⟨launchRank+9,fun X hX hf words g hg => ?_⟩
  have h := Frame.count_leU (fun g hg => thread_sound hp hg) hX hg (control_tracked hp hX)
    threadRank (fun _ => false) 0 fun _ _ _ ev he hs hi _ move => by
      have next := rank_next hp hX hf words he hs hi move
      cases e : ev.counts <;> simpa [e] using next
  have bound := initial_rank (Q := Q) (L := L) (g := g)
  omega

end PTX.Kernels.InklingRelDecode.Proof.Export
