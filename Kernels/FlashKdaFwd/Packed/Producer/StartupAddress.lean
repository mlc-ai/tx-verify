-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.InputLeader
import all Kernels.FlashKdaFwd.Packed.Producer.OffsetRegisters
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Proof

private def coord (reg : Nat) (d : Dim) := Producer.move (.int .u 32) reg (.sreg ⟨.ctaid,some d⟩)

set_option maxRecDepth 60000 in
private theorem coordinates : Transfers.slice 111 2 = some [coord 309 .x,coord 310 .y] := by
  kernel_rfl

private theorem zero_coord (base : Nat → Nat → Nat) (L : Launch) (t : TState) (d : Dim) (r : Nat)
    (zero : (L.ctaidOf (129 / L.block)).get d = 0) :
    execLocalA (Prologue.assumptions base) L 129 t (coord r d).op =
      .ok (next (setReg t r (b32 0))) := by
  change execMove L 129 t (coord r d).op = _
  simp [coord,Producer.move,execMove,readValue,readBits,sregValue,SReg.width,zero,DType.width,
    Value.bytes,b32,truncBits,bind,Except.bind,pure,Except.pure]

private def addressInputs (t : TState) :=
  setReg (setReg {t with pc := 113,fault := none} 309 (b32 0)) 2247 (b64 65536)

private def addressFields (t : TState) :=
  (t.pc,t.regs 2264,t.regs 309,t.regs 307,t.regs 88,t.sub,t.acc,t.fault)

set_option maxRecDepth 60000 in
private theorem address_math (base : Nat → Nat → Nat) (L : Launch) (t : TState) :
    (localWindow base L 113 2 2 (addressInputs t)).map addressFields =
      some (115,some (b64 65536),some (b32 0),t.regs 307,t.regs 88,t.sub,t.acc,none) := by
  kernel_rfl

theorem find_offsets (base : Nat → Nat → Nat) (L : Launch) (t : TState) (pc : t.pc = 111)
    (origin : L.ctaidOf (129/L.block) = ⟨0,0,0⟩) (state : LoaderState t) :
    ∃ u, Relation.ReflTransGen (Tau kernel (Prologue.assumptions base) L 129) t u ∧
      u.pc = 115 ∧ u.regs 2264 = some (b64 65536) ∧ u.regs 309 = some (b32 0) ∧
      u.regs 307 = some (b32 129) ∧ u.regs 88 = some (.pred false) ∧
      u.sub = 0 ∧ u.acc = [] ∧ u.fault = none := by
  let x := next (setReg t 309 (b32 0))
  let y := next (setReg x 310 (b32 0))
  have siteX : kernel.code[t.pc]? = some (coord 309 .x) := by
    rw [pc]; exact fetch (pc := 111) (i := 0) (by decide) (by decide) coordinates
  have siteY : kernel.code[x.pc]? = some (coord 310 .y) := by
    rw [show x.pc = 112 by simp [x,next,setReg,pc]]
    exact fetch (pc := 111) (i := 1) (by decide) (by decide) coordinates
  have a : Tau kernel (Prologue.assumptions base) L 129 t x :=
    out_tau state.clear siteX (by rfl) (by rfl) (zero_coord base L t .x 309 (by rw [origin]; rfl))
  have b : Tau kernel (Prologue.assumptions base) L 129 x y :=
    out_tau state.clear siteY (by rfl) (by rfl) (zero_coord base L x .y 310 (by rw [origin]; rfl))
  have fix {r : Nat} {v : Value} (h : y.regs r = some v) : setReg y r v = y := by
    simp [setReg,← h,Function.update_eq_self]
  have pos : y.pc = 113 := by simp [y,x,next,setReg,pc]
  have clear : y.fault = none := state.clear
  have original : addressInputs y = y := by
    unfold addressInputs
    rw [← pos,← clear,fix (r := 309) (by simp [y,x,next,setReg]),
      fix (r := 2247) (by simpa [y,x,next,setReg] using state.offsets)]
  have h := address_math base L y
  rw [original] at h
  obtain ⟨u,steps,fields⟩ := Option.map_eq_some_iff.mp h
  simp only [addressFields,Prod.mk.injEq] at fields
  refine ⟨u,.head a (.head b (run_rtg (localWindow_sound (by decide) steps))),?_⟩
  simpa [y,x,next,setReg,state.thread,state.leader,state.scalar,state.fresh] using fields

end FlashKda.Packed.ProducerControl
