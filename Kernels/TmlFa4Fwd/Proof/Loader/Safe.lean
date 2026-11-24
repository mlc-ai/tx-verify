-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
public import Lemmas.Flow.UbStop
import Kernels.TmlFa4Fwd.Flow.Code.Part010
import Kernels.TmlFa4Fwd.Flow.Code.Part011
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part018
import Kernels.TmlFa4Fwd.Flow.Code.Part021
import Kernels.TmlFa4Fwd.Flow.Code.Part029
import Lemmas.Flow.TmplOkSync

@[expose] public section

/-! # The loader warps' elections are no undefined behaviour

Every election of the loader (warp 14's TMA groups, `te`, and the drain's, `de`) has the
immediate full mask, so it is never undefined behaviour (`elect_imm_ok`). The copies, the tensor
copies, the local stores and the reads are not covered here (`DECISIONS.md`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {g w : Nat} {ent : Nat → Value}

set_option maxHeartbeats 4000000 in
/-- **No election of a loader lane is undefined behaviour.** -/
theorem elect_safe {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[(code p L g w ent).pc d]? = some ins)
    (hf : Fires ((code p L g w ent).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : (∃ a b, d.site = .te a b) ∨ d.site = .de) (f : Fault) : e.kind ≠ .ub f := by
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v, k⟩ := d
  intro hk
  have hu := fires_ub hf hk
  rcases hs with ⟨a, b, rfl⟩ | rfl
  · fin_cases a <;> fin_cases b <;>
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      exact elect_imm_ok f hu
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact elect_imm_ok f hu

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
