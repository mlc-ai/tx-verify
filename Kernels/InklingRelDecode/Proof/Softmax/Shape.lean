-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Ev
import Kernels.InklingRelDecode.Flow.Code.Part015
import Kernels.InklingRelDecode.Flow.Code.Part019
import Kernels.InklingRelDecode.Flow.Code.Part034
import Lemmas.Flow.CtlStepsU
import Lemmas.Flow.Events
import Lemmas.Flow.Ledger
import Lemmas.Flow.TcTmpl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Proof PTX.Flow Control

set_option maxRecDepth 100000
variable {Q : Params} {L : Launch} {m : Mem0} {g i : Nat} {v : Carry} {e : Entry}
  {ev : Event} {o : Option TState} {t : TState} {ins : Instr}

private theorem regs {d : D} (ht : (code e L g).AtD d t) : Holds t.regs ((code e L g).facts d) := by
  obtain ⟨_,_,_,_,h⟩ := ht
  exact h

private theorem shared_reg {s : Site} {r a}
    (hp : Pre Q L m) (ht : (code e L g).AtD ⟨s,i,v⟩ t)
    (hr : r ∈ ctlLive s.pc) (hv : valueOf e L g ⟨s,i,v⟩ r = u32 (L.sharedBase+a))
    (bound : a < sharedBytes) (aligned : a%8=0) :
    mbarLoc L g t r 0 = .ok (MbarRow.loc L g a) := by
  have range := hp.sharedRange
  have align := hp.sharedAlignment
  have ha : L.sharedBase+a < 2^32 := by omega
  have val := holds_mem (regs ht) (mem_factsFrom_eq hr hv)
  rw [u32,Nat.mod_eq_of_lt ha] at val
  exact mbarLoc_b32 val ha (by omega)

private theorem poll {pc dst base par a q} (loc : mbarLoc L g t base 0 =
    .ok (MbarRow.loc L g a)) (reg : t.regs par = some (b32 q)) (small : q < 2)
    (hf : Fires pc (eventTmpl Assumptions.all L g t (.mbarWait dst base 0 (.reg par) true .cta))
      ev o) : PTX.MbarRow.Wait ev (MbarRow.loc L g a) q := by
  obtain ⟨ok,h⟩ := fires_wait_exact (by rfl) loc (readBits_b32 reg (by omega)) hf
  refine ⟨ok,?_⟩
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show q < 2^64 by omega),
    Nat.mod_eq_of_lt small] using h

theorem object_shape {s : Site} (hp : Pre Q L m) (ht : (code e L g).AtD ⟨s,i,v⟩ t)
    (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl Assumptions.all L g t ins.op) ev o) :
    ObjectEv L g i s ev := by
  cases s <;> try trivial
  case waitS =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1257)
    apply poll (base := 874) (par := 875) _ _ (by omega) hf
    · apply shared_reg hp ht (by decide : 874 ∈ ctlLive 1257)
      · change u32 (L.sharedBase+i%2*8+213280) = u32 (L.sharedBase+(213280+8*(i%2)))
        congr 1; omega
      · change 213280 + 8*(i%2) < 213340; omega
      · change (213280 + 8*(i%2))%8=0; omega
    · exact holds_mem (regs ht) (mem_factsFrom (show 875 ∈ ctlLive 1257 by decide))
  case waitO =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2239)
    apply poll (base := 623) (par := 1532) _ _ (by omega) hf
    · exact shared_reg hp ht (by decide : 623 ∈ ctlLive 2239) rfl (by decide) (by decide)
    · exact holds_mem (regs ht) (mem_factsFrom (show 1532 ∈ ctlLive 2239 by decide))
  case arrive =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1013)
    apply fires_arrive_exact (b := 0) (n := 1) (by rfl) _ (by rfl) (by rfl) hf
    apply shared_reg hp ht (by decide : 1709 ∈ ctlLive 1013)
    · change u32 (L.sharedBase+i%2*8+213296) = u32 (L.sharedBase+(213296+8*(i%2)))
      congr 1; omega
    · unfold Iface.pReady MbarRow.slot2 sharedBytes; omega
    · unfold Iface.pReady MbarRow.slot2; omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax
