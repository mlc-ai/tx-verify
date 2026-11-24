-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Pointer
public import Kernels.FlashKdaFwd.Packed.Bfloat
public import Lemmas.Flow.Run
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Election
open PTX

def stop : Instr := ⟨none, .unmodeled ⟨.brkpt, [], []⟩⟩

def jump : Instr := ⟨some (2,false), .bra 1456 false⟩

def guardOp : Instr := ⟨none, .int ⟨.or, .pred, false, [some 2], [.reg 35, .reg 88]⟩⟩

def tid : Instr := ⟨none, .move {
  kind := .scalar, ty := .int .u 32, dsts := [some 667], srcs := [.sreg ⟨.tid, some .x⟩] }⟩

def laneId : Instr := ⟨none, .int {
  op := .and, ty := .int .b 32, dsts := [some 668], srcs := [.reg 667, .imm 31] }⟩

def zeroLane : Instr := ⟨none, .int {
  op := .setp .eq none, ty := .int .b 32, dsts := [some 35], srcs := [.reg 668, .imm 0] }⟩

def elect : Instr := ⟨none, .warp ⟨.elect, none, [some 3415, some 3416], [], some (.reg 331)⟩⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 60000 in
theorem sites :
    Transfers.slice 32 1 = some [elect] ∧
    Transfers.slice 1414 4 = some [tid, laneId, zeroLane, guardOp] ∧
    Transfers.slice 1454 2 = some [jump, stop] := ⟨rfl,rfl,rfl⟩

theorem nonzero_member : electMember 0xffffffff 1 := by decide

theorem mask_member {l : Nat} (h : l < 32) : electMember 0xffffffff l := by
  exact (show ∀ i : Fin 32, electMember 0xffffffff i.val by decide +kernel) ⟨l,h⟩

theorem choose (L : Launch) (g : Nat) (t : TState)
    (mask : t.regs 331 = some (Proof.b32 0xffffffff)) :
    electTmpl L g t (some 3415) 3416 (.reg 331) = .elect 0xffffffff (fun leader =>
      next (setReg (setReg t 3415 (Proof.b32 leader)) 3416 (.pred (laneOf L g == leader)))) := by
  rw [electTmpl, Proof.readBits_b32 mask (by decide)]
  change (if electMember 0xffffffff (laneOf L g) then _ else _) = _
  have yes : electMember 0xffffffff (laneOf L g) := mask_member (Nat.mod_lt _ (by decide))
  rw [ite_eq_left yes]
  rfl

noncomputable section
variable (b : Nat → Nat → Nat)
local notation "A" =>
  [Pointer.representation b, Bfloat.exactNarrow, Activation.arithmetic, Activation.approximate]

theorem guarded (L : Launch) (g : Nat) (t : TState) (zeroLane notLeader : Bool)
    (lane : t.regs 35 = some (.pred zeroLane)) (leader : t.regs 88 = some (.pred notLeader)) :
    execLocalA A L g t guardOp.op =
      .ok (next (setReg t 2 (.pred (zeroLane || notLeader)))) := by
  change execInt L g t ⟨.or, .pred, false, [some 2], [.reg 35, .reg 88]⟩ = _
  simp [execInt, DType.width, readPred, readReg, lane, leader, bind, Except.bind, pure, Except.pure]

theorem nonzero_guard (L : Launch) (g : Nat) (t : TState)
    (threadId : (L.tidOf g).x = 129) (elected : t.regs 88 = some (.pred false)) :
    ∃ u, [tid, laneId, zeroLane, guardOp].foldlM (m := Exec) (fun s i => execLocalA A L g s i.op)
      t = .ok u ∧ u.regs 2 = some (.pred false) := by
  let t1 := next (setReg t 667 (Proof.b32 129))
  let t2 := next (setReg t1 668 (Proof.b32 1))
  let t3 := next (setReg t2 35 (.pred false))
  have a : execLocalA A L g t tid.op = .ok t1 := by
    change execMove L g t tid.op = _
    simp [tid, execMove, readValue, readBits, sregValue, SReg.width, Dim3.get, threadId,
      DType.width, Value.bytes, t1, Proof.b32, truncBits, bind, Except.bind, pure, Except.pure]
  have c : execLocalA A L g t1 laneId.op = .ok t2 := by
    change execInt L g t1 ⟨.and, .int .b 32, false, [some 668], [.reg 667,.imm 31]⟩ = _
    simp [execInt, t2, t1, next, setReg, readBits, readReg, Proof.b32, DType.width, truncBits,
      bind, Except.bind, pure, Except.pure]
  have d : execLocalA A L g t2 zeroLane.op = .ok t3 := by
    change execInt L g t2 ⟨.setp .eq none, .int .b 32, false, [some 35], [.reg 668,.imm 0]⟩ = _
    simp [execInt, t3, t2, t1, next, setReg, readBits, readReg, Proof.b32, DType.width, truncBits,
      bind, Except.bind, pure, Except.pure]
    rfl
  have holds : t3.regs 88 = some (.pred false) := by
    simpa [t3, t2, t1, next, setReg] using elected
  have e := guarded b L g t3 false false (by simp [t3, next, setReg]) holds
  simp only [List.foldlM_cons, a, c, d, e, bind, Except.bind, List.foldlM_nil, pure, Except.pure]
  exact ⟨_, rfl, by simp [next, setReg]⟩

theorem stop_rule (L : Launch) (g : Nat) (t : TState) :
    execLocalA A L g t stop.op = .error .noRule := by rfl

theorem stop_path (K : Kernel) (L : Launch) (g : Nat) (t : TState)
    (j : K.code[1454]? = some jump) (s : K.code[1455]? = some stop)
    (pc : t.pc = 1454) (ok : t.fault = none) (condition : t.regs 2 = some (.pred false)) :
    Run K A L g t [⟨1455, .ub .noRule⟩] none := by
  have step : Tau K A L g t (skip t) := by
    simp [Tau, out, ok, pc, j, jump, guardHolds, readReg, condition, bind, Except.bind,
      pure, Except.pure]
  apply Run.last (Relation.ReflTransGen.single step)
  refine ⟨.ub .noRule, ?_, ?_⟩
  · have pos : (skip t).pc = 1455 := by simp [skip, pc]
    have clear : (skip t).fault = none := ok
    have act : stop.op.isLocal = true := rfl
    simp only [out, pos, clear, s, show guardHolds (skip t) stop.guard = .ok true from rfl,
      act, ↓reduceIte, stop_rule]
  · simp [Fires, skip, pc]

end
end FlashKda.Packed.Election
