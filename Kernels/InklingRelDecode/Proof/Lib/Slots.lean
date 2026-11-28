-- SPDX-License-Identifier: Apache-2.0
module

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib.Slots

/-- The dense prologue schedule reaches its publishing barrier at 281. -/
def prologue := 100
def publish := 281
def enter := 285
def reuse := 289

def stride := 400
def frame (r : Nat) := 1000 + stride*r
def mma (r : Nat) := frame r + 100
def softmax (r : Nat) := frame r + 200
def finish := frame 8589934596

/-- The loader issues eight copies in four elected pairs in this band. -/
def emptyWait (r : Nat) := frame r
def readyArrival (r : Nat) := frame r + 2
def readyCopy (r p : Nat) (second : Bool) :=
  frame r + (6 + 4*p + p/2 + (if second then 1 else 0))
def readyWait (r : Nat) := mma r + 1
def scoreCommit (r : Nat) := mma r + 13
def scoreWait (r : Nat) := softmax r + 64
def probArrival (r : Nat) := softmax r + 90
/-- PV consumes block r during MMA iteration r+1. -/
def probWait (r : Nat) := mma (r+1) + 15
def emptyCommit (r : Nat) := mma (r+1) + 27
def doneCommit (i : Nat) := mma i + 28
def doneWait (i : Nat) := softmax i + 70
def finalCommit := finish - 92
def finalWait := finish

theorem kv_ready (r : Nat) (p : Fin 4) (b : Bool) :
    readyArrival r < readyWait r ∧ readyCopy r p b < readyWait r := by
  have := p.isLt
  cases b <;> simp [readyArrival,readyCopy,readyWait,mma] <;> omega

theorem kv_empty (r : Nat) : emptyCommit r < emptyWait (r+3) := by
  simp [emptyCommit,emptyWait,mma,frame,stride]; omega

theorem scores (r : Nat) : scoreCommit r < scoreWait r := by
  simp [scoreCommit,scoreWait,mma,softmax]

theorem probs (r : Nat) : probArrival r < probWait r := by
  simp [probArrival,probWait,softmax,mma,frame,stride]; omega

theorem done (i : Nat) : doneCommit i < doneWait i := by simp [doneCommit,doneWait,mma,softmax]

theorem final_order : finalCommit < finalWait := by decide

end PTX.Kernels.InklingRelDecode.Proof.Lib.Slots
