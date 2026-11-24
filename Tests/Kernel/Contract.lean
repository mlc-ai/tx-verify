-- SPDX-License-Identifier: Apache-2.0
module

public meta import Lean
public meta import ImportGraph.Lean.Environment
public import Core.Assembly.Correctness
public import Core.Assembly.WaitOrder
public import Core.Async.BulkGroup
public import Core.Async.BulkExecution
public import Core.Tmem.TmemPairRelease
public import Core.Tmem.TmemPairAccess
public import Core.Tc.TcMmaDescriptor
public import Core.Tc.TcSharedDescriptor
public import Core.Tc.TcMmaOperands
public import Core.Tc.TcSharedAddress
public import Core.Async.Tensor.TensorStore
public import Core.Async.Tensor.TensorCopy
public import Core.Async.Tensor.TensorTransfer
public import Core.Async.Tensor.TensorDescriptor
public import Core.Async.Tensor.TensorTile
public import Core.Async.Tensor.TensorAddress
public import Core.Async.Tensor.TensorSwizzle
public import Core.Clc.ClcEffects
public import Core.Clc.ClcOwnership
public import Core.Source.Decode
public import Assumption.NcReadOnly
public import Assumption.ApproxExact
public import Assumption.ClusterScopeMbar
public import Assumption.SegmentExact
public import Assumption.PairEven
public import Assumption.TcLdDataflow
public import Assumption.CommitOrder
public import Assumption.PollAgree
public import Assumption.SetMaxNRegSync

/-!
# The contract index is complete

Every reviewed definition belongs to a contract entry, and every entry is well formed. The
entries are the `## ID — title` module-doc sections of `Core/`, the assumption constructors in
`Assumption/` included, with `Defs:`, `Source:` and `Direction:` lines. Basic rules also
name applicability, premises and effects. External/open notes are `### EXT-` or
`### OPEN-` headings beside their rules in `Core/`. A standalone external rule also uses
the `### EXT-` heading inside its own module-doc opener. The check fails the build
when:

* two entries have the same ID, or an entry lacks a field or has an unknown direction;
* an entry has a `Guarantee:` field (its conclusion belongs in the Statement);
* an entry names a definition that does not exist in its file;
* a definition of `Core/` belongs to no entry of its file (an unlabelled rule), or to two;
* any file of the model or its guide refers to an ID that is not defined;
* Core imports anything outside Core and Mathlib.
-/

namespace PTX.ContractCheck

open Lean Elab Command

meta structure Entry where
  id : String
  file : String
  defs : List String
  direction : String

meta def directions : List String :=
  ["equal", "stricter", "scope", "reading", "not-conservative", "representation",
    "interface", "trust"]

/-- The rule-ID prefixes, which are `RULE_PREFIXES` of `Tools/contract_index.py` (compared by
tests/test_contract_fields.py), then `OPEN`, and the prefixes before the rename, so that a
reference to a renamed ID is reported as undefined. -/
meta def prefixes : List String :=
  ["PROG", "THREAD", "MEM", "OBJ", "DEP", "ERR", "CORRECT", "EXT", "ASM", "OPEN",
    "SOURCE", "INSTR", "VALUE", "TYPES", "EXEC", "FLOAT"]

meta partial def leanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← leanFiles e.path)
    else if e.path.extension == some "lean" then out := out.push e.path
  return out

/-- The lines after a field line that start with two spaces continue the field. -/
meta def continued : List String → String
  | l :: ls => if l.startsWith "  " then " " ++ l.trimAscii.copy ++ continued ls else ""
  | [] => ""

meta def field (key : String) (lines : List String) : Option String :=
  match lines.dropWhile (fun l => !(l.startsWith (key ++ ": ") || l == key ++ ":")) with
  | l :: ls => some ((l.drop (key.length + 2)).trimAscii.copy ++ continued ls)
  | [] => none

meta partial def parse (file : String) : List String → List Entry → Except String (List Entry)
  | [], acc => .ok acc.reverse
  | l :: ls, acc =>
    let heading := if l.startsWith "/-! ## " then some (l.drop 7)
      else if l.startsWith "/-! ### EXT-" then some (l.drop 8) else none
    if let some heading := heading then
      let id := (heading.copy.splitOn " — ").head!.trimAscii.copy
      let body := ls.takeWhile fun x => !(x.endsWith "-/")
      match field "Defs" body, field "Source" body, field "Direction" body with
      | some d, some _, some dir => do
        if (field "Guarantee" body).isSome then
          throw s!"{file}: {id} has a Guarantee field; state its conclusion in the Statement"
        if file.startsWith "Core/" &&
            !(file.startsWith "Core/Source/" || file.startsWith "Core/Data/" ||
              file == "Core/Assembly/Execution.lean" ||
              file == "Core/Assembly/Correctness.lean") then
          for key in ["Applies", "Premises", "Effect"] do
            if (field key body).getD "" == "" then
              throw s!"{file}: {id} needs a nonempty {key} line"
        let defs := ((d.splitOn ",").map (·.trimAscii.copy)).filter (· ≠ "")
        parse file ls ({ id, file, defs, direction := dir } :: acc)
      | _, _, _ => .error s!"{file}: {id} needs Defs, Source and Direction lines"
    else parse file ls acc

/-- The parser rejects a block with a `Guarantee:` field and accepts the same block without it. -/
meta def guaranteeBlock (withGuarantee : Bool) : List String :=
  ["/-! ## PROG-EXAMPLE — example", "Statement: s", "Defs: d", "Source: s", "Direction: equal",
    "Applies: a", "Premises: p"] ++ (if withGuarantee then ["Guarantee: g"] else []) ++
    ["Effect: e", "-/"]

#guard (parse "Core/Sync/Example.lean" (guaranteeBlock true) []) matches .error _
#guard (parse "Core/Sync/Example.lean" (guaranteeBlock false) []) matches .ok [_]

#guard (parse "Core/Memory/Example.lean"
  ("/-! ### EXT-EXAMPLE — example" :: (guaranteeBlock false).drop 1) [])
  matches .ok [⟨"EXT-EXAMPLE", _, ["d"], "equal"⟩]

/-- A `Source:` label with a list below it and blank lines between the fields is a field. -/
meta def listBlock : List String :=
  ["/-! ## PROG-EXAMPLE — example", "Statement: s", "", "Defs: d", "", "Source:",
    "- §1: \"q\"", "- EXT-X", "", "Direction: equal", "", "Applies: a", "", "Premises: p", "",
    "Effect: e", "-/"]

#guard (parse "Core/Sync/Example.lean" listBlock []) matches .ok [_]

meta def isIdChar (c : Char) : Bool := c.isUpper || c.isDigit || c == '-'

/-- Contract IDs mentioned in a text. -/
meta def refs (text : String) : List String :=
  ((text.splitToList fun c => !isIdChar c).map fun t => (t.dropEndWhile (· == '-')).copy).filter
    fun t => prefixes.any fun p => t.startsWith (p ++ "-") && t.length > p.length + 1

meta def moduleOf (file : String) : Name := ((file.dropEnd 5).copy.replace "/" ".").toName

/-- Constants that the compiler generates for a declaration: they belong to it. -/
meta def generated (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  n.isInternal || n.hasMacroScopes || isAuxRecursor env n || isNoConfusion env n ||
    Meta.isMatcherCore env n || env.isProjectionFn n || Meta.isInstanceCore env n ||
    (match ci with | .ctorInfo _ | .recInfo _ | .quotInfo _ => true | _ => false) ||
    match n with
    | .str p s =>
      s ∈ ["inj", "injEq", "sizeOf_spec", "eq_def", "ext", "ext_iff", "induct"] ||
        s.startsWith "eq_" || s.startsWith "proof_" || s.startsWith "match_" ||
        (s ∈ ["noConfusionType", "ctorIdx", "ctorElimType", "ofNat", "ofNat_ctorIdx", "below",
            "brecOn"] && (env.find? p matches some (.inductInfo _))) ||
        -- auxiliary definitions of a generated constant (`instRepr….repr`, `brecOn.go`)
        (match env.find? p with | some cp => generated env p cp | none => false)
    | _ => false

elab "#check_contract" : command => do
  let env ← getEnv
  let files := (← leanFiles "Core") ++ (← leanFiles "Assumption")
  let mut entries : List Entry := []
  let mut texts : List String := []
  let mut errs : Array String := #[]
  for f in files do
    let text ← IO.FS.readFile f
    texts := text :: texts
    -- Core imports only Core and Mathlib.
    for line in text.splitOn "\n" do
      let imp := if line.startsWith "public import " then some (line.drop 14).copy
        else if line.startsWith "import " then some (line.drop 7).copy else none
      if let some names := imp then
        for name in names.splitOn " " do
          let model := name.startsWith "Core." || name.startsWith "Mathlib."
          let constructor := f.toString.startsWith "Assumption/" && name.startsWith "Assumption."
          unless model || constructor do errs := errs.push s!"{f}: forbidden model import {name}"
    match parse f.toString (text.splitOn "\n") [] with
    | .ok es => entries := entries ++ es
    | .error e => errs := errs.push e
  -- External/open note headings are colocated with rules; the guides only refer to them.
  for f in ["README.md", "Core/README.md"] do
    texts := (← IO.FS.readFile f) :: texts
  let mut external : List String := []
  for text in texts do
    for l in text.splitOn "\n" do
      if l.startsWith "### EXT-" || l.startsWith "### OPEN-" then
        external := ((l.drop 4).copy.splitOn " ").head!.trimAscii.copy :: external
  let ids := entries.map (·.id) ++ external
  for i in ids.eraseDups do
    if ids.count i > 1 then errs := errs.push s!"duplicate ID {i}"
  for e in entries do
    unless e.direction ∈ directions do
      errs := errs.push s!"{e.id}: unknown direction '{e.direction}'"
  -- every named definition exists, in the file of its entry
  let mut claimed : NameMap String := {}
  for e in entries do
    for d in e.defs do
      if d == "*" then continue
      let cands := [(("PTX." ++ d).toName), d.toName]
      match cands.find? env.contains with
      | none => errs := errs.push s!"{e.id}: no definition {d}"
      | some n =>
        if env.getModuleFor? n != some (moduleOf e.file) then
          errs := errs.push s!"{e.id}: {d} is not defined in {e.file}"
        if let some other := claimed.find? n then
          errs := errs.push s!"{d} belongs to both {other} and {e.id}"
        claimed := claimed.insert n e.id
  -- every definition belongs to an entry of its file
  let whole := (entries.filter (·.defs.contains "*")).map (moduleOf ·.file)
  let mods := files.toList.map (moduleOf ·.toString)
  for (n, ci) in env.constants.map₁.toList do
    let some m := env.getModuleFor? n | continue
    unless m ∈ mods do continue
    if m ∈ whole || generated env n ci || claimed.contains n then continue
    errs := errs.push s!"{n} ({m}) belongs to no contract entry"
  -- every referenced ID is defined
  for t in texts do
    for r in (refs t).eraseDups do
      unless r ∈ ids do errs := errs.push s!"reference to undefined ID {r}"
  if errs.isEmpty then
    logInfo m!"contract: {entries.length} entries in Lean, {external.length} external or open"
  else
    throwError (String.intercalate "\n" errs.toList)

#check_contract

end PTX.ContractCheck
