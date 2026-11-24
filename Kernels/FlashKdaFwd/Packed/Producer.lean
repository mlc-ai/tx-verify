-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Election
public import Tactics.KernelRfl
import Mathlib.Tactic.FinCases
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Producer
open PTX

def move (ty : DType) (d : Nat) (x : Opnd) : Instr :=
  ⟨none,.move ⟨.scalar,ty,[some d],[x]⟩⟩

def integer (ty : IType) (op : IntOp) (d : Nat) (xs : List Opnd) : Instr :=
  ⟨none,.int ⟨op,.int ty 32,false,[some d],xs⟩⟩

def role : List Instr :=
  [move (.int .u 32) 307 (.sreg ⟨.tid,some .x⟩),
   integer .u .shr 308 [.reg 307,.imm 5], integer .u (.setp .lt none) 4 [.reg 307,.imm 128],
   integer .u (.setp .lt none) 5 [.reg 307,.imm 160], integer .b .selp 328 [.imm 1,.imm 2,.reg 5],
   integer .b .selp 327 [.imm 0,.reg 328,.reg 4], move .pred 84 (.imm 0), move .pred 83 (.imm (-1)),
   integer .b (.setp .eq none) 6 [.reg 327,.imm 0], ⟨some (6,false),.bra 42 false⟩,
   integer .b (.setp .ne none) 7 [.reg 327,.imm 1], move .pred 85 (.reg 83),
   move .pred 86 (.reg 84), move .pred 87 (.reg 83), move .pred 88 (.reg 83),
   ⟨some (7,false),.bra 48 false⟩, move (.int .b 32) 331 (.imm (-1)),
   move (.int .b 32) 329 (.imm 0), move (.int .b 32) 330 (.reg 329)]

set_option maxRecDepth 60000 in
theorem sites : Transfers.slice 13 19 = some role := by kernel_rfl

def selectedRole : List Instr :=
  [{move (.int .s 32) 330 (.imm 1) with guard := some (3416,false)},
   move (.int .s 32) 329 (.reg 3415), integer .b (.setp .eq none) 88 [.reg 330,.imm 0],
   move .pred 85 (.imm 0), move .pred 83 (.imm (-1)), move .pred 84 (.reg 83),
   move .pred 86 (.reg 85), move .pred 87 (.reg 85), ⟨none,.bra 48 true⟩]

set_option maxRecDepth 60000 in
theorem selected_sites : Transfers.slice 33 9 = some selectedRole := by kernel_rfl

noncomputable section
private def limited (K : Kernel) (A : List Assumption) (L : Launch) (g lo hi : Nat) :
    Nat → TState → Option TState
  | 0, t => some t
  | n+1, t => do
    guard (lo ≤ t.pc ∧ t.pc < hi)
    let u ← tauStep K A L g t
    limited K A L g lo hi n u

private theorem agrees {K src : Kernel} {A : List Assumption} {L : Launch} {g lo hi : Nat}
    (shared : ∀ pc, lo ≤ pc → pc < hi → K.code[pc]? = src.code[pc]?) {n : Nat} {t u : TState}
    (h : limited src A L g lo hi n t = some u) : run K A L g n t = some u := by
  induction n generalizing t with
  | zero => exact h
  | succ n ih =>
    by_cases live : lo ≤ t.pc ∧ t.pc < hi
    · have fetch := shared t.pc live.1 live.2
      have same : tauStep K A L g t = tauStep src A L g t := by simp only [tauStep, out, fetch]
      simp only [limited, guard, live] at h
      rw [run, same]
      cases next : tauStep src A L g t with
      | none => simp [next] at h
      | some v => exact ih (by simpa [next] using h)
    · simp [limited, guard, live] at h

private def model (pc : Nat) (code : List Instr) : Kernel :=
  {name := "", params := [], code := List.replicate pc Election.stop ++ code}
private def launch (l : Launch) : Launch := {l with block := 192, ntid := ⟨192,1,1⟩}
private def start (t : TState) : TState := {t with pc := 13, fault := none}
private def summary (t : TState) := (t.pc, t.fault, t.regs 331)
private def rules (base : Nat → Nat → Nat) :=
  [Pointer.representation base, Bfloat.exactNarrow, Activation.arithmetic, Activation.approximate]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem all_lanes (base : Nat → Nat → Nat) (L : Launch) (t : TState) (l : Fin 32) :
    (limited (model 13 role) (rules base) (launch L) (128+l.val) 13 32 19 (start t)).map summary =
      some (32,none,some (Proof.b32 0xffffffff)) := by
  fin_cases l <;> kernel_rfl

theorem before_election (base : Nat → Nat → Nat) (L : Launch) (K : Kernel) (t : TState)
    (l : Fin 32) (block : L.block = 192) (threads : L.ntid = ⟨192,1,1⟩) (pc : t.pc = 13)
    (clear : t.fault = none) (fetch : ∀ i < 19, K.code[13+i]? = role[i]?) :
    ∃ u, run K [Pointer.representation base, Bfloat.exactNarrow, Activation.arithmetic,
      Activation.approximate] L (128+l.val) 19 t = some u ∧
      u.pc = 32 ∧ u.fault = none ∧ u.regs 331 = some (Proof.b32 0xffffffff) := by
  have sameL : launch L = L := by unfold launch; rw [← threads, ← block]
  have sameT : start t = t := by unfold start; rw [← pc, ← clear]
  have f := all_lanes base L t l
  rw [sameL, sameT] at f
  obtain ⟨u,steps,endState⟩ := Option.map_eq_some_iff.mp f
  refine ⟨u, agrees (src := model 13 role) ?_ steps, ?_⟩
  · intro p low high
    obtain ⟨i,rfl⟩ : ∃ i, p = 13+i := ⟨p-13,by omega⟩
    rw [fetch i (by omega)]
    have enough : (List.replicate 13 Election.stop).length ≤ 13+i := by simp
    change role[i]? = (List.replicate 13 Election.stop ++ role)[13+i]?
    rw [List.getElem?_append_right enough, List.length_replicate, Nat.add_sub_cancel_left]
  · simpa [summary] using endState

def chosen (t : TState) (leader : Nat) :=
  next (setReg (setReg t 3415 (Proof.b32 leader)) 3416 (.pred true))

private def chosenFlags (t : TState) := (t.pc,t.fault,t.regs 88)

set_option maxRecDepth 10000 in
private theorem chosen_values (base : Nat → Nat → Nat) (L : Launch) (g n : Nat) (t : TState) :
    (limited (model 33 selectedRole) (rules base) L g 33 42 9
      (chosen {t with pc := 32, fault := none} n)).map chosenFlags =
      some (48,none,some (.pred false)) := by kernel_rfl

theorem after_election (base : Nat → Nat → Nat) (L : Launch) (K : Kernel) (t : TState)
    (g n : Nat) (pc : t.pc = 32) (clear : t.fault = none)
    (fetch : ∀ i < 9, K.code[33+i]? = selectedRole[i]?) :
    ∃ u, run K [Pointer.representation base, Bfloat.exactNarrow, Activation.arithmetic,
      Activation.approximate] L g 9 (chosen t n) = some u ∧
      u.pc = 48 ∧ u.fault = none ∧ u.regs 88 = some (.pred false) := by
  have h := chosen_values base L g n t
  have same : {t with pc := 32, fault := none} = t := by rw [← pc, ← clear]
  rw [same] at h
  obtain ⟨u,steps,endState⟩ := Option.map_eq_some_iff.mp h
  refine ⟨u, agrees (src := model 33 selectedRole) ?_ steps, ?_⟩
  · intro p low high
    obtain ⟨i,rfl⟩ : ∃ i, p = 33+i := ⟨p-33,by omega⟩
    rw [fetch i (by omega)]
    have enough : (List.replicate 33 Election.stop).length ≤ 33+i := by simp
    change selectedRole[i]? = (List.replicate 33 Election.stop ++ selectedRole)[33+i]?
    rw [List.getElem?_append_right enough, List.length_replicate, Nat.add_sub_cancel_left]
  · simpa [chosenFlags] using endState

end
end FlashKda.Packed.Producer
