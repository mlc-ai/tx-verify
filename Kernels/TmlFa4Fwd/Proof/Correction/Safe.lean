-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part131
import Kernels.TmlFa4Fwd.Flow.Code.Part143
import Lemmas.Flow.UbFree

@[expose] public section

/-! # The correction warps' closing barrier and Tensor Memory store waits are no undefined
behaviour

The arrival at named barrier 2 (`barEnd`, `bar.arrive 2, 416` with immediate operands) is not
undefined behaviour (`barArrive_imm_ok`), and a `tcgen05.wait::st` (`rwait`) needs only a launch
of whole warps. `misc_safe` collects these sites; the Tensor Memory loads and stores and the
final and LSE stores are not covered here (`DECISIONS.md`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option maxHeartbeats 4000000 in
/-- **The correction warps' closing arrival and Tensor Memory store waits are no undefined
behaviour.** -/
theorem misc_safe (hp : Pre p L m) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hc : kernel.code[(code p L g).pc d]? = some ins)
    (hf : Fires ((code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : (∃ l, d.site = .barEnd l) ∨ ∃ st, d.site = .rwait st) (f : Fault) :
    e.kind ≠ .ub f := by
  have hblk : L.block % 32 = 0 := by rw [hp.block]
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v, k⟩ := d
  intro hk
  have hu := fires_ub hf hk
  rcases hs with ⟨l, rfl⟩ | ⟨st, rfl⟩
  · cases l <;>
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      exact barArrive_imm_ok (by decide) (by decide) (by decide) (by decide) f hu
  · fin_cases st <;>
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      revert hu
      simp [eventTmpl, tcTmpl, hblk, ofExec, pure, Except.pure]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
