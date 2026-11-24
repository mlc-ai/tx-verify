-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.WarpUniform
public import Core.Source.Decode

/-!
# Control flow: `brx.idx`, `exit`, `ret` and `trap` (THREAD-BRANCH, THREAD-RUN)
-/

namespace PTX.Tests.ControlFlow
noncomputable section

private def launch : Launch := { grid := 1, block := 32, params := fun _ => none }

/-- A thread whose register 0 holds the 32-bit index `i`. -/
private def withIndex (i : Nat) : TState := setReg {} 0 (.bits 32 (BitVec.ofNat 64 i))

private def table : Op := .brx (.reg 0) [3, 5, 7] false

-- Decoding: the table is resolved to source positions; it must be declared before the branch.
private def env : Decode.Env :=
  { classes := [⟨"r".toList, 1, 32⟩], labels := [], params := [], tables := [("T", 0, [3, 5, 7])],
    pc := 2 }
example : Decode.op env "brx.idx" [.register "r0", .symbol "T"] = .ok table := rfl
example : Decode.op env "brx.idx.uni" [.register "r0", .symbol "T"] =
    .ok (.brx (.reg 0) [3, 5, 7] true) := rfl
example : (Decode.op { env with pc := 0, tables := [("T", 1, [3])] } "brx.idx"
    [.register "r0", .symbol "T"]).toOption = none := rfl
example : (Decode.op env "brx.idx" [.register "r0", .symbol "U"]).toOption = none := rfl

-- `brx.idx` continues at the entry of the list that the index selects.
example : table.rule = some .threadBranch := rfl
example : execLocal launch 0 (withIndex 0) table = .ok { withIndex 0 with pc := 3 } := rfl
example : execLocal launch 0 (withIndex 1) table = .ok { withIndex 1 with pc := 5 } := rfl
example : execLocal launch 0 (withIndex 2) table = .ok { withIndex 2 with pc := 7 } := rfl
-- An index at or beyond the length of the list is undefined.
example : execLocal launch 0 (withIndex 3) table = .error .badValue := rfl
example : execLocal launch 0 (withIndex 0xFFFFFFFF) table = .error .badValue := rfl
-- The index is the low 32 bits of the register.
example : execLocal launch 0 (setReg {} 0 (.bits 64 (BitVec.ofNat 64 (2 ^ 32 + 1)))) table =
    .ok { setReg {} 0 (.bits 64 (BitVec.ofNat 64 (2 ^ 32 + 1))) with pc := 5 } := rfl
-- An index register that was never written is undefined.
example : execLocal launch 0 {} table = .error .uninitialized := rfl
-- Trust boundary of kernel assumptions: for every list of assumptions in which none selects the
-- instruction at this state, the fault is the result.
example (A : List Assumption)
    (h : ∀ a ∈ A, a.localRule launch 0 (withIndex 3) table = none) :
    execLocalRule A launch 0 (withIndex 3) table = .error .badValue := by
  rw [execLocalRule_of_none h]
  rfl
-- An assumption that selects the instruction replaces the core's result, the fault included.
private def pickFirst : Assumption :=
  { name := "pick-first", statement := "brx.idx continues at the first entry",
    localRule := fun _ _ t op => match op with
      | .brx _ (pc :: _) _ => some (.ok { t with pc := pc })
      | _ => none }
example : execLocalRule [pickFirst] launch 0 (withIndex 3) table =
    .ok { withIndex 3 with pc := 3 } := rfl
example : execLocalRule [pickFirst] launch 0 (withIndex 1) table =
    .ok { withIndex 1 with pc := 3 } := rfl

-- `brx.idx.uni` has the rule of `brx.idx`; ERR-NONUNIFORM-GUARD compares the indices of the lanes.
example : (Op.brx (.reg 0) [3, 5, 7] true).rule = some .threadBranch := rfl
example : execLocal launch 0 (withIndex 1) (.brx (.reg 0) [3, 5, 7] true) =
    .ok { withIndex 1 with pc := 5 } := rfl
example : execLocal launch 0 (withIndex 3) (.brx (.reg 0) [3, 5, 7] true) = .error .badValue := rfl
-- The index a `brx.idx.uni` reads is recorded for the uniformity check; `brx.idx` records none.
example : uniIndex launch 0 (withIndex 2) (.brx (.reg 0) [3, 5, 7] true) = some 2 := rfl
example : uniIndex launch 0 (withIndex 2) table = none := rfl
example : uniIndex launch 0 {} (.brx (.reg 0) [3, 5, 7] true) = none := rfl
private def uniKernel : Kernel :=
  { name := "uni", params := [], code := [⟨none, .brx (.reg 0) [3, 5, 7] true⟩] }
example : (visit uniKernel launch 0 (withIndex 1) none).index = some 1 := rfl
-- Two lanes that read different indices disagree; the same index with no guard does not.
example : (visit uniKernel launch 0 (withIndex 1) none).Disagree
    (visit uniKernel launch 1 (withIndex 2) none) := Or.inr ⟨1, 2, rfl, rfl, by decide⟩
example : ¬ (visit uniKernel launch 0 (withIndex 1) none).Disagree
    (visit uniKernel launch 1 (withIndex 1) none) := by
  rintro (⟨b, b', h, -⟩ | ⟨x, y, hx, hy, hne⟩)
  · cases h
  · cases hx; cases hy; exact hne rfl

-- `griddepcontrol` in a launch of one grid has no effect (EXT-GRIDDEP-SINGLE).
example : Decode.op env "griddepcontrol.wait" [] = .ok (.misc (.gridDep true)) := rfl
example : Decode.op env "griddepcontrol.launch_dependents" [] = .ok (.misc (.gridDep false)) := rfl
example : (Op.misc (.gridDep true)).rule = some .threadNoEffect := rfl
example : (Op.misc (.gridDep true)).isLocal = true := rfl
example (t : TState) : execLocal launch 0 t (.misc (.gridDep true)) = .ok (next t) := rfl
example (t : TState) : execLocal launch 0 t (.misc (.gridDep false)) = .ok (next t) := rfl
example : (Decode.op env "griddepcontrol" []).toOption = none := rfl

-- `exit` and `ret` end the thread.
example : Op.exit.rule = some .threadRun := rfl
example (A : List Assumption) (t : TState) : eventTmpl A launch 0 t .exit = .exit := rfl
example (A : List Assumption) (t : TState) : eventTmpl A launch 0 t .ret = .exit := rfl
example : Decode.op env "exit" [] = .ok .exit := rfl

-- `trap` is undefined behaviour with its own reason, for every assumption list.
example : Op.trap.rule = some .threadRun := rfl
example : Op.trap.isLocal = false := rfl
example (A : List Assumption) (t : TState) : eventTmpl A launch 0 t .trap = .ub .trap := rfl
example : Decode.op env "trap" [] = .ok .trap := rfl

private def trapKernel : Kernel := { name := "trap", params := [], code := [⟨none, .trap⟩] }
example (A : List Assumption) : out trapKernel A launch 0 {} = .ev (.ub .trap) := rfl
example (pc : Nat) (e : Event) (o : Option TState) :
    Fires pc (.ub .trap) e o ↔ e = ⟨pc, .ub .trap⟩ ∧ o = none := Iff.rfl

end
end PTX.Tests.ControlFlow
