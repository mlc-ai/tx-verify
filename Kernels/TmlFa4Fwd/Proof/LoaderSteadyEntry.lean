-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut
public import Kernels.TmlFa4Fwd.Proof.LoaderRingEntry
public import Kernels.TmlFa4Fwd.Proof.LoaderTripStart

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem steadyBeforeGate :
    ((kernel.code.drop 1355).take (1384 - 1355)).all
      (fun ins => loaderPipelineCutOp 1355 1384 1743 [7181, 1091] ins.op) = true := by
  set_option maxRecDepth 100000 in decide +kernel

private theorem steadyBeforeSeed :
    ((kernel.code.drop 481).take (1353 - 481)).all
      (fun ins => loaderPipelineCutOp 481 1353 1743 [1091] ins.op) = true := by
  set_option maxRecDepth 100000 in decide +kernel

private theorem seedSteadyPrefix {l : Launch} {g trips : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hTrip : trips < 2 ^ 31) (hs : At s 1353 [(1091, b32 trips)]) :
    loaderVisitsAt 1743 vs ≤ 5 * (trips + 1) + 4 := by
  obtain ⟨u, hu, hU⟩ := loaderSteadyCounterInit (g := g) hTrip s hs
  rcases loaderLocalWalkCut hu hw with hShort | ⟨pre, tail, hTrace, hLen, hTail⟩
  · have h := loaderVisitsAt_le_length 1743 vs
    omega
  have hK : min trips 9 < 2 ^ 31 := by omega
  have hOnGate {t ts tv} (ht : At t 1384 [(7181, b32 (min trips 9)), (1091, b32 trips)])
      (hv : Walk kernel Assumptions.all l g t ts tv) :
      loaderVisitsAt (ringCounterSite 1).branch tv ≤ 5 * (trips + 1) + 2 := by
    have h := loaderSteadyPrefixFromGate hv hTrip hK ht
    change loaderVisitsAt 1743 tv ≤ _
    omega
  have hFull := loaderPrefixThroughCheckpoint 1
    (F := [(7181, b32 (min trips 9)), (1091, b32 trips)])
    (lower := 1355) (cut := 1384) (by decide) (by decide) (by decide)
    ⟨_, Flow.code_1384, rfl⟩ steadyBeforeGate hOnGate hTail
    (by rw [hU.1]; decide) (ringShapeOfAt hU) hU.2.2.2.2
  change loaderVisitsAt 1743 tail ≤ 5 * (trips + 1) + 2 at hFull
  rw [hTrace]
  have h := loaderVisitsAt_le_append 1743 pre tail
  omega

/-- The actual priming and warm steps preserve the remaining trip count through
the steady-ring seed. The resulting bound covers incomplete executions. -/
theorem loaderSteadyPrefixFromPriming {l : Launch} {g trips : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hTrip : trips < 2 ^ 31) (hs : At s 481 [(1091, b32 trips)]) :
    loaderVisitsAt 1743 vs ≤ 5 * (trips + 1) + 4 :=
  loaderPrefixThroughCheckpoint 1 (F := [(1091, b32 trips)])
    (lower := 481) (cut := 1353) (by decide) (by decide) (by decide)
    ⟨_, Flow.code_1353, rfl⟩ steadyBeforeSeed
    (fun ht hw => seedSteadyPrefix hw hTrip ht) hw
    (by rw [hs.1]; decide) (ringShapeOfAt hs) hs.2.2.2.2

end
end PTX.Kernels.TmlFa4Fwd.Loader
