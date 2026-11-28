-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Kernel.Goals
import Kernels.InklingRelDecode.Proof.Common.Export.Bound
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Lemmas.Kernel.Correct

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

theorem Bound.terminates {Q L m} (hp : Pre Q L m)
    (hF : ∀ X, Consistent L kernel Assumptions.all m X → Follow Q L X) :
    BoundGoal kernel Assumptions.all L m := by
  obtain ⟨N, bound⟩ := Export.thread_counts hp
  exact terminates_of_count N
    (fun X hX => bound X hX (hF X hX) (fun he => Protocol.Shared.role_bytes hp hX he))
    fun _ hX _ _ ⟨_, he⟩ => (Lib.no_copy hX he).elim

end PTX.Kernels.InklingRelDecode.Proof.Top
