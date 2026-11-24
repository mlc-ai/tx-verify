-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public meta import Core.Source.Decode
public import Kernels.InklingRelDecode.Ptx
public meta import Kernels.InklingRelDecode.Ptx

/-! Decoder coverage of the frozen Inkling 2 Small relative-attention decode PTX
(`_rel_verify_kernel`): every instruction is decoded on its own against the environment that
`Decode.prepare` builds from the kernel's declarations (shared layout, parameter objects, the
branch table of `brx.idx`), and the forms the model does not yet represent are reported by
opcode. Instructions that decode but have no Core rule are listed too. The full kernel is also
decoded, which checks the header (`.reqntid`) and the parameter objects. This is a work list, not
a correctness theorem. -/
open PTX PTX.Decode

#eval show IO Unit from do
  let m := Generated.InklingRelDecode.module
  match prepare m.globals m.functions.head! with
  | .error e => IO.println s!"Inkling decode setup: {e}"
  | .ok p =>
    let results := (p.instrs.zipIdx 0).map fun ((g, o, a), i) =>
      match guard p.env g, op { p.env with pc := i } o a with
      | .ok _, .ok x => (o, x.rule.isSome, "")
      | .error e, _ | _, .error e => (o, false, e)
    let failed := results.filter fun (_, _, e) => e != ""
    let noRule := results.filter fun (_, r, e) => e == "" && !r
    IO.println s!"Inkling decode: {p.instrs.length} instructions, {failed.length} not decoded, \
      {noRule.length} decoded without a rule"
    for o in (failed.map (·.1)).eraseDups do
      let n := (failed.filter (·.1 == o)).length
      let e := ((failed.find? (·.1 == o)).map (·.2.2)).getD ""
      IO.println s!"  not decoded: {n} {o}: {e}"
    for o in (noRule.map (·.1)).eraseDups do
      IO.println s!"  no rule: {(noRule.filter (·.1 == o)).length} {o}"
  match Decode.module Generated.InklingRelDecode.module
      Generated.InklingRelDecode.module.functions.head! with
  | .error e => IO.println s!"Inkling prepare: {e}"
  | .ok k =>
    IO.println s!"Inkling prepare OK: {k.code.length} instructions, sharedBytes {k.sharedBytes}, \
      maxThreads {k.maxThreads}, reqThreads {k.reqThreads}, paramObjects {k.paramObjects.length}"
