-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MetadataReads
import Kernels.TmlFa4Fwd.Proof.Thread.OutputMetadataReads
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxCuQFootprint
import Kernels.TmlFa4Fwd.Proof.CorrectionSchedulerEntry
import Kernels.TmlFa4Fwd.Proof.LoaderCuQ
import Kernels.TmlFa4Fwd.Proof.MmaQueryStartupPrefix
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX Prologue

/-- A lane's initial cumulative query offset observation in any scheduler role. -/
@[no_expose] def InitialCuQRead (X : Execution) (i : EvId) (a : Acc)
    (bytes : List (Option Byte)) : Prop :=
  ∃ site ∈ [186, 1940, 2776, 3110, 7761], X.get i = some ⟨site, .rd a bytes⟩

theorem InitialCuQRead.reads {X : Execution} {i : EvId} {a : Acc}
    {bytes : List (Option Byte)} (h : InitialCuQRead X i a bytes) : X.Reads i a bytes := by
  obtain ⟨site, _, he⟩ := h
  exact ⟨site, he⟩

/-- Every observed initial lane word has the launch offset footprint for its own lane.
The address is available before assuming anything about its returned bytes. -/
theorem InitialCuQRead.footprint {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {a : Acc}
    {bytes : List (Option Byte)} (h : InitialCuQRead X i a bytes) :
    laneOf l i.1 ≤ p.batch ∧
      a = {loc := globalLoc (p.cuQBase + 4 * laneOf l i.1), size := 4} := by
  obtain ⟨g, j⟩ := i
  obtain ⟨site, hSite, he⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  rcases hSite with rfl | rfl | rfl | rfl | rfl
  · exact (TmlFa4Fwd.Loader.firstCuQReadFootprint hp hX he).2
  · exact (Mma.firstCuQReadFootprint hp hX he).2
  · exact (Output.firstSchedulerCuQFootprint hp hX he).2
  · have hRole := roleBodyPcOfEvent hp hX he (by change 173 < 3110; decide)
      (by change 3110 ∉ registerHintSites; decide)
    have hWarp : warpIndex l g < 8 := by
      change roleBodyPc (warpIndex l g) 3110 at hRole
      unfold roleBodyPc at hRole
      rcases hRole with h | h
      · cases h
      · split_ifs at h <;> omega
    exact Softmax.firstCuQReadFootprint hp hX hWarp he
  · exact (Correction.firstCuQReadFootprint hp hX he).2

end PTX.Kernels.TmlFa4Fwd.Thread
