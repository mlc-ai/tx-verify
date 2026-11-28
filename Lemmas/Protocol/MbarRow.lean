-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotObject
public import Lemmas.Kernel.Safety.Classes

@[expose] public section
namespace PTX.MbarRow
open PTX.Flow

def Wait (e : Event) (l : Loc) (q : Nat) : Prop := ∃ ok, e.kind = .wait l q ok true .cta

def Arrive (e : Event) (l : Loc) (tx : Nat) : Prop := e.kind = .arrive l tx 1 true .cta

def Issue (e : Event) (l : Loc) (n : Nat) : Prop :=
  ∃ (a : Nat) (s : TensorCopy.Spec), e.kind = .tensorIssue a s ∧ s.mbar = l ∧
    TensorTransfer.bytes s.descriptor = n

def Commit (e : Event) (l : Loc) : Prop :=
  ∃ s : TcCommit.Spec, e.kind = .tc (.commit s) ∧ s.mbar = l ∧ s.group = .one

inductive Shape where
  | init (count : Opnd)
  | arrive (tx : Opnd)
  | wait (parity : Opnd)
  | commit
  | issue (mode : TensorMode)
  deriving DecidableEq, Repr

def Shape.ok : Shape → Op → Bool
  | .init c, .mbarInit _ _ c' => c == c'
  | .arrive tx, .mbarArrive _ _ t c cl rel sc st =>
    t == tx && c == .imm 1 && !cl && rel && sc == .cta && st.isNone
  | .wait p, .mbarWait _ _ _ p' acq sc => p == p' && acq && sc == .cta
  | .commit, .tcCommit g _ _ mk => g == .one && mk.isNone
  | .issue md, .cpTensor _ grp _ _ _ _ _ _ mc md' _ => !grp && mc.isNone && md' == md
  | _, _ => false

/-- Exact instruction guard and operand shape of a potential object use. -/
structure Site where
  pc : Nat
  guard : Option (Nat × Bool)
  shape : Shape
  deriving DecidableEq, Repr

/-- Every object instruction in the region is listed, including predicated instructions.
Each listed site decodes to its stated guard and shape. -/
def regionOk (code : List Instr) (lo hi : Nat) (sites : List Site) : Bool :=
  code.zipIdx.all (fun (i,pc) => !(lo ≤ pc && pc < hi && objectOp i.op) ||
    sites.any (fun s => s.pc == pc && s.guard == i.guard && s.shape.ok i.op)) &&
  sites.all (fun s => lo ≤ s.pc && s.pc < hi && (code[s.pc]?).any
    (fun i => objectOp i.op && s.guard == i.guard && s.shape.ok i.op))

theorem objectKind {e : Event} {l : Loc} (hm : Frame.MbarOf e l) : ObjectKind e.kind := by
  obtain ⟨pc,k⟩ := e
  cases k <;> try trivial
  case tc k => cases k <;> trivial

end PTX.MbarRow
