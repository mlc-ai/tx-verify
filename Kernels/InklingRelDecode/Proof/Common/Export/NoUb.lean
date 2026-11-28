-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
import Kernels.InklingRelDecode.Proof.Common.WorkerNoUb
import Kernels.InklingRelDecode.Proof.Startup.Export.NoUb

@[expose] public section

/-! # An undefined-behaviour event is in a data lane past the startup

Every worker lane is free of undefined behaviour (`worker_noUb`), and so is a lane all of whose
events up to the one at hand are at pcs of the startup (`Startup.Export.noUb_early`). So an
undefined-behaviour event of a consistent execution is in a data lane (index below 128 in its
block) that has executed an instruction at pc 27 or above. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

theorem ub_past_startup (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) (words : RoleBytes L X)
    (pair : CountBytes Q L X) {g k pc : Nat} {f : Fault}
    (he : X.get (g, k) = some ⟨pc, .ub f⟩) :
    g % L.block < 128 ∧ ∃ j ≤ k, ∃ e, X.get (g, j) = some e ∧ 27 ≤ e.pc := by
  have hg := Frame.lt_of_get hX he
  refine ⟨?_, ?_⟩
  · by_contra hw
    exact worker_noUb hp hX hf base words pair hg (by omega) he f rfl
  · by_contra left
    refine Startup.Export.noUb_early hp hX hf base hg he (fun j hj e' hj' => ?_) f rfl
    by_contra big
    exact left ⟨j, hj, e', hj', by omega⟩

end PTX.Kernels.InklingRelDecode.Proof.Export
