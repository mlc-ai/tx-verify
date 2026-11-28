-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Time
public import Kernels.InklingRelDecode.Proof.Epilogue.Requests
import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Load
import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Tail
import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Close
import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Live
import Kernels.InklingRelDecode.Proof.Epilogue.Strict.SafeB

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
open PTX

public theorem regBand (d) :
    (Epilogue.requestPhase d.site = 2 → Epilogue.time d ≤ Epilogue.startTime + 280) ∧
    (Epilogue.requestPhase d.site = 3 → Epilogue.startTime + 280 < Epilogue.time d) ∧
    (Epilogue.requestPhase d.site = 2 → d.site ≠ .setMax →
      Epilogue.time d < Epilogue.startTime + 280) := by
  obtain ⟨s,v⟩ := d
  refine ⟨fun h => ?_,fun h => ?_,fun h h' => ?_⟩
  all_goals cases s
  all_goals simp_all [Epilogue.requestPhase, Epilogue.time, Epilogue.Site.position]
  all_goals omega

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
