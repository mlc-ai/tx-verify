-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
public import Kernels.TmlFa4Fwd.Proof.Softmax.RefDef

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
noncomputable section

/-- The original softmax ledger, indexed by the scheduler fields of a control state. -/
abbrev Ref (p : Params) (L : Launch) (g : Nat) (dn : D × (Cnt → Nat)) :=
  Softmax.Ref p L g (dn.1.scheduler, dn.2)

theorem ref_init {p L g} : Ref p L g ((code p L g).init, fun _ => 0) :=
  ⟨refCounts_init p L g⟩

theorem ref_erase {p L g d n} (h : Softmax.Ref p L g (d,n)) : Ref p L g (erase d,n) := by
  obtain ⟨⟨rb,rp,h⟩⟩ := h
  exact ⟨⟨rb, rp, h.cnt, h.elect, h.barr, h.pre, h.bias, h.plain, h.after, h.fin, h.noTile, h.wait⟩⟩

/-- Scheduler operands have reference sources. Score and bias payloads have no control
obligation. -/
def Expect (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .sld .. | .bld .. => True
  | _ => ExpectD p L g d.scheduler e

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
