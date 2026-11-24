-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Program
public import Lemmas.Register.EventRegFrame
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotRmw
public import Lemmas.Execution.NoBarArrive

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Proof PTX.EventFrame

def allowed (pc : Nat) : Prop :=
  48 ≤ pc ∧ (pc ≤ 1455 ∨ 1863 ≤ pc) ∧ (pc ≤ 1881 ∨ 2072 ≤ pc)

def tested (pc : Nat) : Prop := 1418 ≤ pc ∧ pc < 2072

instance (pc : Nat) : Decidable (allowed pc) := by unfold allowed; infer_instance
instance (pc : Nat) : Decidable (tested pc) := by unfold tested; infer_instance

def special (pc : Nat) : Prop :=
  (1414 ≤ pc ∧ pc ≤ 1417) ∨ pc = 1454 ∨ pc = 1455 ∨ pc = 1880 ∨ pc = 1881

instance (pc : Nat) : Decidable (special pc) := by unfold special; infer_instance

def edge (pc target : Nat) : Bool :=
  decide (allowed target ∧ (target ≤ 1414 ∨ 1418 ≤ target) ∧ (tested target → tested pc))

def branches (pc : Nat) : Op → Bool
  | .bra dst _ => edge pc dst
  | .brx .. => false
  | _ => true

def writes (op : Op) := if op.isLocal then writesRegs op else eventWrites op

def accepts (pc : Nat) (i : Instr) : Bool :=
  if allowed pc ∧ ¬ special pc then
    edge pc (pc+1) && branches pc i.op && !(writes i.op).contains 88 &&
      !(writes i.op).contains 2
  else true

def boundaries : List Nat := [85,110,115,116,379]

def staysOnSide (pc dst : Nat) : Bool :=
  boundaries.all fun cut => decide ((pc < cut → dst ≤ cut) ∧ (cut < pc → cut < dst))

def startupBranch (pc : Nat) : Op → Bool
  | .bra dst _ => staysOnSide pc dst
  | .brx .. => false
  | .exit | .ret => decide (379 < pc)
  | _ => true

def barrierSite (pc : Nat) (op : Op) : Bool :=
  !op.isBarArrive && (!Flow.barOp op || decide (pc = 85 ∨ pc = 110 ∨ 379 ≤ pc))

def memorySite (pc : Nat) (op : Op) : Bool :=
  !(Flow.bulkOp op || Flow.clcOp op || Flow.atomicOp op) &&
    (!Flow.writeOp op || decide (379 < pc)) && (startupBranch pc op && barrierSite pc op)

def check (base : Nat) (xs : List Instr) : Bool :=
  (xs.zipIdx base).all fun (i,pc) => accepts pc i && memorySite pc i.op

def window (base n : Nat) := (Transfers.slice base n).map (check base)

theorem at_window {base n pc : Nat} {i : Instr} (h : window base n = some true)
    (fit : base+n ≤ 3835) (lo : base ≤ pc) (hi : pc < base+n)
    (ins : kernel.code[pc]? = some i) :
    accepts pc i = true ∧ memorySite pc i.op = true := by
  unfold window at h
  rw [instructions fit] at h
  have all := List.all_eq_true.mp (Option.some.inj h)
  have m : ((kernel.code.drop base).take n)[pc-base]? = some i := by
    rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,show base+(pc-base)=pc by omega,ins]
  rw [← Bool.and_eq_true]
  apply all (i,pc)
  exact List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mpr ⟨lo, m⟩

end FlashKda.Packed.ProducerControl
