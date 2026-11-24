-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public meta import Core.Source.Decode
public import Kernels.FlashAttn4Fwd.Ptx
public meta import Kernels.FlashAttn4Fwd.Ptx

/-! Decoder coverage of the frozen FlashAttention-4 forward PTX: every instruction is decoded
on its own against the kernel's actual declarations, and the forms the model does not yet
represent are reported by opcode. This is a work list, not a correctness theorem. -/
open PTX PTX.Decode

def setup (globals : List (List String)) (f : Syntax.Function) :
    M (Env × List (List String) ×
      List (Option (String × Bool) × String × List Syntax.Operand)) := do
  let body ← if needsScopeResolution f.body then
      resolveScopes (scopeDepth f.body) f.body [] "" else pure f.body
  let (decls, labels, instrs) ← flatten body 0
  let (sharedDecls, regDecls) := decls.partition (fun d => d.head? = some ".shared")
  -- Declarations the model does not represent are reported, not fatal.
  let classes := regDecls.flatMap fun d => ((regClass d).toOption).getD []
  let unsupported := regDecls.filter fun d => (regClass d).toOption.isNone
  let sharedGlobals := globals.filter (fun d => d.head? != some ".global")
  let (shared, _) ← sharedLayout (sharedDecls ++ sharedGlobals) 0
  let (ps, _, paramObjects) ← parameterDecls f.header
  let params := ps ++ paramObjects.map (fun p => (p.name, p.bytes * 8))
  let env : Env := { classes, labels, params, shared, objects := paramObjects }
  pure (env,
    unsupported, instrs)

-- The generated name of the kernel function is longer than a line.
set_option linter.style.longLine false

#eval show IO Unit from do
  match setup Generated.FlashAttn4Fwd.module.globals
    Generated.FlashAttn4Fwd.kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_object_at__tensor0000o11101213_tensor0000o11101213_tensor0000o10111213_tensor0000o11101213_None_None_None_Non_0 with
  | .error e => IO.println s!"FA4 decode setup: {e}"
  | .ok (env, unsupported, instrs) =>
    IO.println s!"FA4 declarations: {unsupported.length} register declarations not represented"
    for d in unsupported.eraseDups.take 8 do IO.println s!"  {d}"
    let failed := instrs.filterMap fun (p, o, a) =>
      match guard env p, op env o a with
      | .ok _, .ok _ => none
      | .error e, _ | _, .error e => some (o, e)
    let opcodes := (failed.map (·.1)).eraseDups
    IO.println
      s!"FA4 decode: {instrs.length} instructions, {failed.length} not decoded, {opcodes.length} forms"
    for o in opcodes do
      let n := (failed.filter (·.1 == o)).length
      let e := ((failed.find? (·.1 == o)).map (·.2)).getD ""
      IO.println s!"  {n} {o}: {e}"
