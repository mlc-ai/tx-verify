-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.OutStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.KindsS

@[expose] public section

/-! # The strict data step of an election

`dsS_el`: `Kinds.ds_el` without the dead alternative (`DataStepE`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- **An election** into a leader register and a predicate the facts do not name. -/
theorem dsS_el {d : D} {e : Event} {s s' : Site} {ty : Option DType} {r p : Nat} {mask : Opnd}
    (hs : d.c.site = s) (hna : s ≠ .arrS)
    (hc : kernel.code[s.pc]? = some ⟨none, .warp ⟨.elect, ty, [some r, some p], [], some mask⟩⟩)
    (he : Control.elems s = 1) (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = [])
    (hr : ∀ q ∈ wF (scX L) s d.b, q.1 ≠ r) (hp : ∀ q ∈ wF (scX L) s d.b, q.1 ≠ p)
    (hR : ∀ e, ReachS kernel Assumptions.all L g (s.pc + 1) (wF (scX L) s d.b)
      (wF (scX L) s' (record d.c e d.b))) :
    DataStepE (code P L g w) (dF L) d e := by
  refine DataStepE.elect (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc) ?_
  intro hi mk inst ld d' t hn hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  refine fin_reachS (hs ▸ hna) (hsucc c') (fun h1 => ?_) (fun _ _ => hR _)
  obtain ⟨hp', hsb, ha, hf, hF⟩ := at_site hs hat (el0 hs hi he) (hs ▸ h1) hst
  exact ⟨by simp only [PTX.next, setReg]; omega, hsb, ha, hf,
    holds_update (holds_update hF hr) (fun q hq => hp q hq)⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
