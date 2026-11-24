-- SPDX-License-Identifier: Apache-2.0
module

@[expose] public section

/-!
PTX source syntax, as produced by the Python parser (`Tools/parse_ptx.py`).

This is deliberately untyped: opcode strings, operand spellings, and declaration
tokens are kept verbatim. All interpretation (modifiers, literal values, label
resolution, register widths) happens in Lean, in `PTX.Decode`.
-/

/-! ## PROG-SYNTAX — the parsed PTX source
Statement: The model starts from the syntax tree of the kernel's PTX file. The tree keeps opcode
  strings, operand spellings and declaration tokens exactly as written, and the decoder gives them
  their meaning.

Review: the exported trees are the files `Kernels/<K>/Ptx.lean`.

Defs: *

Source:
- §4 (syntax)
- §11 (directives)

Direction: representation

Effect: The model's source is the syntax tree the Python parser exports. That the tree is the `.ptx`
  file is external fact EXT-IMPORT.
-/

namespace PTX.Syntax

/-- An instruction operand as spelled in the source: a register, a symbol, a literal, the sink `_`,
an address, a vector, a base with a signed offset, a negation, or a pair. -/
inductive Operand where
  | register (name : String)
  | symbol (name : String)
  | literal (text : String)
  | sink
  | address (children : List Operand)
  | vector (children : List Operand)
  | offset (sign : String) (base offset : Operand)
  | negate (operand : Operand)
  | pair (children : List Operand)
  deriving Repr, Inhabited

/-- One statement of a function body: an instruction with its optional guard predicate, a label,
a declaration, a directive, or a nested scope. -/
inductive Statement where
  /-- `predicate = some (register, negated)`. -/
  | instruction (predicate : Option (String × Bool)) (opcode : String) (operands : List Operand)
  | label (name : String)
  | declaration (tokens : List String)
  | directive (tokens : List String)
  | scope (body : List Statement)
  deriving Repr, Inhabited

/-- A function of the module: its name, header tokens and body statements. -/
structure Function where
  name : String
  header : List String
  body : List Statement
  deriving Repr, Inhabited

/-- A parsed PTX module: its directives, global declarations and functions. -/
structure Module where
  sourceSha256 : String
  directives : List (List String)
  /-- Module-scope declarations other than functions, e.g. `.extern .shared` arrays. -/
  globals : List (List String) := []
  functions : List Function
  deriving Repr, Inhabited

end PTX.Syntax
