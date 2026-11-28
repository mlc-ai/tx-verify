-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Sub
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Read

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

/-- If the saved right operand lacks bits, the local subtraction after a request
read faults. Rebuilding malformed bytes faults before the subtraction. -/
theorem read_fault {L g t ev u dst src diff pc} {op : MemAccess} {b : Value}
    (kind : op.kind = .load) (nc : op.nc = false) (ext : op.ext = .same)
    (regs : op.regs = [dst]) (pc_t : t.pc=pc) (sub : t.sub=0) (acc : t.acc=[])
    (hf : t.fault=none) (rhs : t.regs src = some b) (fresh : src ≠ dst)
    (bad : ¬b.regBits.isSome)
    (fetch : kernel.code[pc+1]? = some ⟨none,.int ⟨.sub,.int .s 32,false,[some diff],
      [.reg dst,.reg src]⟩⟩) (hs : Assumptions.emuSites.contains (pc+1) = false)
    (fire : Fires pc (eventTmpl Assumptions.all L g t (.mem op)) ev (some u)) :
    Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u := by
  obtain ⟨a,bs,rfl,rfl⟩ := fires_load kind nc fire ext
  rw [regs]
  cases h : rebuild 3 bs with
  | error f => exact Machine.dead_of_fault (f := f) (by simp [afterLoad,h])
  | ok v =>
    rw [afterLoad_ok sub acc h]
    let s := {(setReg t dst v) with pc := t.pc+1,sub := 0,acc := []}
    have p : s.pc = pc+1 := congrArg (·+1) pc_t
    have hv : s.regs dst = some v := by simp [s,setReg]
    have hy : s.regs src = some b := by simpa [s,setReg,fresh] using rhs
    let ii : IntInstr := ⟨.sub,.int .s 32,false,[some diff],[.reg dst,.reg src]⟩
    cases ex : execInt L g s ii with
    | ok z => exact (bad (sub_result hv hy ex).2).elim
    | error f =>
      exact dead_of_error (t := s) (p ▸ fetch) rfl hf
        ((Lib.workerInt (ii := ii) (by rfl) p hs).trans ex)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
