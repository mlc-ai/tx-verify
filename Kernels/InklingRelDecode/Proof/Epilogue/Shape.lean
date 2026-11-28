-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Ev
import Kernels.InklingRelDecode.Flow.Code.Part040
import Lemmas.Flow.Ledger
import Lemmas.Flow.TcTmpl
import Lemmas.Flow.Events

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue
open PTX PTX.Flow PTX.Proof Control

set_option maxRecDepth 100000
theorem object_shape {Q L m g ent v s t ins ev o} (hp : Pre Q L m)
    (ht : (code ent L g).AtD ⟨s,v⟩ t) (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl Assumptions.all L g t ins.op) ev o) : ObjectEv L g s ev := by
  rintro rfl
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2565)
  obtain ⟨_,_,_,_,regs⟩ := ht
  have range := hp.sharedRange
  have align := hp.sharedAlignment
  have small : L.sharedBase + Iface.oFinal < 2^32 := by
    change L.sharedBase+213328 < 2^32
    unfold sharedBytes at range; omega
  have addr := holds_mem regs (mem_factsFrom (show 624 ∈ ctlLive 2565 by decide))
  change t.regs 624 = some (b32 ((L.sharedBase+Iface.oFinal)%2^32)) at addr
  rw [Nat.mod_eq_of_lt small] at addr
  have loc : mbarLoc L g t 624 0 = .ok (MbarRow.loc L g Iface.oFinal) := by
    apply mbarLoc_b32 addr small
    unfold Iface.oFinal; omega
  have par := holds_mem regs (mem_factsFrom (show 1760 ∈ ctlLive 2565 by decide))
  exact fires_wait_exact (by rfl) loc (readBits_b32 (a := 0) par (by decide)) hf

end PTX.Kernels.InklingRelDecode.Proof.Epilogue
