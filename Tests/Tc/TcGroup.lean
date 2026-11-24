-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcGroup

namespace PTX.Tests.TcGroup

private def kernel (code : List Instr) : Kernel := { name := "groups", params := [], code }

example : (kernel []).TcGroupUniform := rfl
example : (kernel [{ op := .tcAlloc .one 1 0 (.imm 32) },
    { op := .tcDealloc .one (.reg 4) (.imm 32) }]).TcGroupUniform := rfl
example : (kernel [{ op := .tcAlloc .two 1 0 (.imm 32) },
    { op := .tcDealloc .two (.reg 4) (.imm 32) },
    { op := .tcRelinquish .two }]).TcGroupUniform := rfl

-- Unqualified operations do not imply group 1.
example : (kernel [{ op := .tcAlloc .two 1 0 (.imm 32) },
    { op := .tcLd [1] 4 }, { op := .tcWaitLd },
    { op := .tcFenceBefore }, { op := .tcFenceAfter }]).TcGroupUniform := rfl

-- Predication does not turn a mixed-group source into a valid kernel.
example : ¬ (kernel [{ op := .tcAlloc .one 1 0 (.imm 32) },
    { guard := some (3, false), op := .tcAlloc .two 2 0 (.imm 32) }]).TcGroupUniform := by
  intro h; cases h

private def mixed : Kernel := kernel [
  { op := .tcAlloc .one 1 0 (.imm 32) },
  { op := .tcCommit .two 0 0 (some (.imm 3)) }]

-- Even a theorem about an empty launch or an unvisited branch must satisfy the rule.
example (A : List Assumption) (L : Launch) (mem0 : Mem0) (post : FinalMem → Prop)
    (hv : L.Valid mixed) : ¬ Correct mixed A L mem0 post := by
  intro h
  have hg := h.tcGroupUniform hv
  cases hg

end PTX.Tests.TcGroup
