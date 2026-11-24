# SPDX-License-Identifier: Apache-2.0
"""Check which named readings (`### EXT-` notes) each kernel theorem discloses.

Every EXT note has one sentence that says which kernels it applies to:

    Disclosed by every kernel: K1, K2.
    Disclosed by every kernel whose statement names `C1`, `C2 (field := v)` or `C3` and `C4`: K1.
    Disclosed by every kernel whose statement names `C1`: none.

The sentence may start inside a line of a field (usually the last sentence of `Effect:`), wrap
onto the following lines, and ends with the first period after the kernel list's `: `.
The backquoted items are Lean constants (resolved as written or under `PTX.`), optionally with
one argument condition: `Op.bra (uni := true)` is an `Op.bra` whose `uni` argument is `true`,
`Op.tcMmaTs (aOff ≠ 0)` one whose `aOff` argument is not the literal 0 (an argument that is not
a literal counts as different). Items joined by `and` form one alternative; the note applies when
one alternative holds. Without a `whose` clause the note applies to every kernel. The kernel
list is the names of the `Kernels/` directories, in that order, or `none`; `--write` regenerates
it.

A kernel can keep its disclosure register in `Kernels/<kernel>/READINGS.md`. The register has a
`# EXT disclosures` heading and one `- EXT-ID` line per reading. For a kernel with this file the
model sentences omit its name. The tool checks both destinations against the theorem comments
and checks the combined disclosure against the Lean declaration closure.

A kernel's statement names a constant when the constant occurs in the type of
`PTX.Kernels.<K>.correct` or, transitively, in a definition under `Kernels/` reached from it:
the program `kernel`, `Pre`, `Post`, the assumption list and the kernel's data. Proofs are not
followed, nor are the bodies of Core and Lemmas definitions: the shared library proofs mention
every rule of the model, so a closure through them names every reading for every kernel. The
statement closure therefore contains the instruction forms of the program (with their literal
arguments) and the assumption constructors it selects. A reading applies to a program that has
one of its instruction forms; a reading that depends on runtime data (a descriptor field, a
count compared with the CTA size) is attributed to every program that has the instruction.

Each kernel's `Theorem.lean` has a module comment `## Readings this result depends on` whose
bullets start with the IDs they explain (`- EXT-A, EXT-B: ...`, `- EXT-A and EXT-B (...)`).

With `--lean --write` the kernel lists are rewritten from the computation.

Checks:
  * every EXT note has one well-formed `Disclosed by` sentence, naming existing kernels;
  * the kernels a note lists are exactly the kernels whose `Theorem.lean` lists the note;
  * with `--lean` (needs a built project): every named constant and argument exists, and the
    kernels a note lists are exactly the kernels whose statement satisfies its condition.

Usage: python3 Tools/reading_uses.py [--lean [--write] [--show]]
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HEADING = re.compile(r"^### (EXT-[A-Z0-9-]+)\b")
BULLET = re.compile(r"^- (EXT-[A-Z0-9-]+(?:(?:, | and )EXT-[A-Z0-9-]+)*)")
ITEM = re.compile(r"^`([^`\s(]+)(?: \((\w+) (:=|≠) ([^`)]+)\))?`$")
READINGS = "## Readings this result depends on"


class Atom:
    """A constant, optionally with one argument condition."""

    def __init__(self, text):
        m = ITEM.match(text)
        if not m:
            raise ValueError(f"malformed item {text}")
        self.const, self.field, op, self.value = m.groups()
        self.equal = op == ":="
        self.text = text

    def key(self):
        return (self.const, self.field, self.equal, self.value)


class Note:
    """One EXT note: where it is, and its `Disclosed by` sentence."""

    def __init__(self, ident, path, span, alternatives, kernels):
        # span: (first line, column where the sentence starts, last line, column after its period)
        self.ident, self.path, self.span = ident, path, span
        self.line = span[0] + 1
        self.alternatives = alternatives  # None: every kernel; else a list of lists of Atom
        self.kernels = kernels


def kernel_names():
    return sorted(p.parent.name for p in (ROOT / "Kernels").glob("*/Theorem.lean"))


def model_files():
    files = sorted((ROOT / "Core").rglob("*.lean")) + [ROOT / "Core/README.md"]
    return [f for f in files if ".lake" not in f.parts]


def split_items(text):
    """Split `a`, `b` or `c` and `d` into alternatives of items."""
    alternatives = []
    for alt in re.split(r",? or |, ", text):
        parts = [p.strip() for p in alt.split(" and ")]
        alternatives.append([Atom(p) for p in parts])
    return alternatives


START = "Disclosed by every kernel"


def list_cut(rest):
    """The index of the first ': ' outside backquotes in `rest`, or None."""
    tick = False
    for i, ch in enumerate(rest):
        if ch == "`":
            tick = not tick
        elif ch == ":" and not tick and rest[i + 1 : i + 2] == " ":
            return i
    return None


def sentence_end(text):
    """The index just after the period that ends the sentence starting `text`, or None."""
    cut = list_cut(text)
    if cut is None:
        return None
    dot = text.find(".", cut)
    return None if dot < 0 else dot + 1


def parse_sentence(sentence):
    """Return (alternatives, kernels) of one `Disclosed by` sentence."""
    if not sentence.startswith(START) or not sentence.endswith("."):
        raise ValueError("expected 'Disclosed by every kernel[ whose statement names ...]: ....'")
    rest = sentence[len(START) :]
    cut = list_cut(rest)
    if cut is None:
        raise ValueError("no ': ' before the kernel list")
    cond, names = rest[:cut], rest[cut + 2 : -1]
    if cond == "":
        alternatives = None
    elif cond.startswith(" whose statement names "):
        alternatives = split_items(cond[len(" whose statement names ") :])
    else:
        raise ValueError(f"unknown condition '{cond}'")
    kernels = [] if names == "none" else [k.strip() for k in names.split(",")]
    return alternatives, kernels


def note_text(lines, first):
    """The body of the note whose heading is the line before `first`, joined into one string with
    single spaces, and for each joined line its (line index, column, offset in the string)."""
    text, chunks = "", []
    for j in range(first, len(lines)):
        line = lines[j]
        if line.startswith(("### ", "## ", "/-! ")):
            break
        col = len(line) - len(line.lstrip())
        if text:
            text += " "
        chunks.append((j, col, len(text)))
        text += line[col:].rstrip()
        if line.rstrip().endswith("-/"):
            break
    return text, chunks


def position(chunks, offset):
    """The (line index, column) of offset `offset` of a joined note body."""
    j, col, start = next(c for c in reversed(chunks) if c[2] <= offset)
    return j, col + offset - start


def notes():
    """All EXT notes of the model, with their parsed sentences; raise on a malformed one."""
    out, errors = [], []
    for path in model_files():
        lines = path.read_text().splitlines()
        for i, line in enumerate(lines):
            m = HEADING.match(line)
            if not m:
                continue
            ident = m.group(1)
            text, chunks = note_text(lines, i + 1)
            rel = path.relative_to(ROOT)
            if text.count(START) != 1:
                errors.append(f"{rel}:{i + 1}: {ident} needs one 'Disclosed by' sentence")
                continue
            at = text.index(START)
            j, col = position(chunks, at)
            end = sentence_end(text[at:])
            try:
                if end is None:
                    raise ValueError("the sentence has no period after its kernel list")
                alternatives, kernels = parse_sentence(text[at : at + end])
            except ValueError as exc:
                errors.append(f"{rel}:{j + 1}: {ident}: {exc}")
                continue
            k, after = position(chunks, at + end - 1)
            out.append(Note(ident, rel, (j, col, k, after + 1), alternatives, kernels))
    return out, errors


def theorem_lists():
    """kernel -> set of EXT IDs listed in its Theorem.lean readings comment."""
    out = {}
    for k in kernel_names():
        text = (ROOT / "Kernels" / k / "Theorem.lean").read_text()
        start = text.find(READINGS)
        if start < 0:
            raise SystemExit(f"Kernels/{k}/Theorem.lean: no '{READINGS}' comment")
        block = text[start : text.find("-/", start)]
        ids = set()
        for line in block.splitlines():
            m = BULLET.match(line)
            if m:
                ids.update(re.split(r", | and ", m.group(1)))
        out[k] = ids
    return out


REGISTRY_TITLE = "# EXT disclosures"
REGISTRY_ITEM = re.compile(r"^- (EXT-[A-Z0-9-]+)$")


def read_registry(path):
    """Read a kernel-local register, and report malformed lines and duplicate IDs."""
    readings, errors = set(), []
    lines = path.read_text().splitlines()
    if not lines or lines[0] != REGISTRY_TITLE:
        errors.append(f"{path}:1: expected '{REGISTRY_TITLE}'")
    for n, line in enumerate(lines[1:], 2):
        if not line:
            continue
        item = REGISTRY_ITEM.fullmatch(line)
        if not item:
            errors.append(f"{path}:{n}: expected one '- EXT-ID' entry")
            continue
        ident = item.group(1)
        if ident in readings:
            errors.append(f"{path}:{n}: duplicate {ident}")
        readings.add(ident)
    return readings, errors


def write_registry(path, readings):
    """Write the entries in deterministic EXT-ID order."""
    path.write_text(REGISTRY_TITLE + "\n\n" + "".join(f"- {r}\n" for r in sorted(readings)))


LEAN = r"""
open Lean

namespace ReadingUses

def modOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

def resolve (env : Environment) (s : String) (extra : List Name := []) : Option Name :=
  let n := s.toName
  ([n, `PTX ++ n] ++ extra.map (· ++ n)).find? env.contains

/-- Constants whose types list every constructor of an inductive type: they name no form. -/
def skipped (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  ci matches .recInfo _ || isAuxRecursor env n || isNoConfusion env n ||
    match n with
    | .str _ s => s.startsWith "_sparseCasesOn"
    | _ => false

/-- The statement closure: types of every reached constant, bodies of `Kernels` definitions. -/
def closure (env : Environment) (start : Name) : NameSet × Array Expr := Id.run do
  let mut seen : NameSet := {}
  let mut exprs : Array Expr := #[]
  let mut stack := [start]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if skipped env n ci then continue
    let mut es := #[ci.type]
    if (modOf env n).map (·.getRoot) == some `Kernels && !ci.isTheorem then
      if let some v := ci.value? (allowOpaque := true) then es := es.push v
    for e in es do
      exprs := exprs.push e
      for c in e.getUsedConstants do
        unless seen.contains c do stack := c :: stack
  return (seen, exprs)

def binderIndex (ty : Expr) (field : Name) : Option Nat :=
  let rec go : Expr → Nat → Option Nat
    | .forallE n _ b _, i => if n == field then some i else go b (i + 1)
    | _, _ => none
  go ty 0

def intLit? (e : Expr) : Option Int :=
  match e.int? with
  | some i => some i
  | none => (e.nat?.map Int.ofNat).orElse fun _ => e.rawNatLit?.map Int.ofNat

/-- The arguments a constructor is applied to, at each application in `e`. -/
partial def collect (c : Name) (e : Expr) (acc : Array (Array Expr)) : Array (Array Expr) :=
  match e with
  | .app f a =>
    let acc := if e.getAppFn.isConstOf c then acc.push e.getAppArgs else acc
    collect c a (collect c f acc)
  | .lam _ t b _ | .forallE _ t b _ => collect c b (collect c t acc)
  | .letE _ t v b _ => collect c b (collect c v (collect c t acc))
  | .mdata _ b | .proj _ _ b => collect c b acc
  | _ => acc

def applications (es : Array Expr) (c : Name) : Array (Array Expr) :=
  es.foldl (fun acc e => if e.getUsedConstants.contains c then collect c e acc else acc) #[]

end ReadingUses

open ReadingUses in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut errors : Array String := #[]
  let mut resolved : Array (Option (Name × Option (Nat × Bool × Sum Int Name))) := #[]
  for (c, cond) in atoms do
    match resolve env c with
    | none => errors := errors.push s!"unknown constant {c}"; resolved := resolved.push none
    | some n =>
      match cond with
      | none => resolved := resolved.push (some (n, none))
      | some (field, eq, v) =>
        let some ci := env.find? n | unreachable!
        match binderIndex ci.type field.toName with
        | none => errors := errors.push s!"{c} has no argument {field}"; resolved := resolved.push none
        | some i =>
          let val : Option (Sum Int Name) := match v.toInt? with
            | some k => some (.inl k)
            | none => (resolve env v [`Bool, `Option]).map .inr
          match val with
          | none => errors := errors.push s!"unknown value {v}"; resolved := resolved.push none
          | some val => resolved := resolved.push (some (n, some (i, eq, val)))
  let mut out : Array Json := #[]
  for k in kernels do
    let some thm := resolve env s!"Kernels.{k}.correct" | errors := errors.push s!"no {k}.correct"
    let (names, exprs) := closure env thm
    let mut hits : Array Bool := #[]
    for r in resolved do
      match r with
      | none => hits := hits.push false
      | some (n, none) => hits := hits.push (names.contains n)
      | some (n, some (i, eq, val)) =>
        let ok := (applications exprs n).any fun args =>
          match args[i]? with
          | none => false
          | some a =>
            let same := match val with
              | .inl k => intLit? a == some k
              | .inr c => a.getAppFn.isConstOf c
            let known := match val with
              | .inl _ => (intLit? a).isSome
              | .inr _ => a.getAppFn.isConst
            if eq then same else !same || !known
        hits := hits.push ok
    out := out.push (Json.mkObj [("kernel", toJson k), ("hits", toJson hits)])
  IO.println (Json.mkObj [("errors", toJson errors), ("kernels", Json.arr out)]).compress
"""


def lean_string(s):
    return json.dumps(s, ensure_ascii=False)


def lean_source(kernels, atoms):
    imports = "".join(f"import Kernels.{k}.Theorem\n" for k in kernels)
    ks = ", ".join(lean_string(k) for k in kernels)
    items = []
    for a in atoms:
        cond = (
            "none"
            if a.field is None
            else f"some ({lean_string(a.field)}, {str(a.equal).lower()}, {lean_string(a.value)})"
        )
        items.append(f"({lean_string(a.const)}, {cond})")
    data = (
        f"\ndef kernels : List String := [{ks}]\n"
        "def atoms : List (String × Option (String × Bool × String)) :=\n  ["
        + ",\n   ".join(items)
        + "]\n"
    )
    return imports + data + LEAN


def lean_hits(kernels, atoms):
    """Run Lean on the built project; return {kernel: {atom key: bool}}."""
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    run = subprocess.run(
        [lake, "env", "lean", "--stdin"],
        cwd=ROOT,
        input=lean_source(kernels, atoms),
        capture_output=True,
        text=True,
    )
    lines = [line for line in run.stdout.splitlines() if line.startswith("{")]
    if run.returncode != 0 or not lines:
        raise SystemExit("Lean failed:\n" + run.stdout + run.stderr)
    result = json.loads(lines[-1])
    if result["errors"]:
        raise SystemExit("unresolved items:\n" + "\n".join(result["errors"]))
    return {
        r["kernel"]: {a.key(): h for a, h in zip(atoms, r["hits"], strict=True)}
        for r in result["kernels"]
    }


def computed(note, kernels, hits):
    if note.alternatives is None:
        return set(kernels)
    return {
        k for k in kernels if any(all(hits[k][a.key()] for a in alt) for alt in note.alternatives)
    }


def sentence_text(note, kernels):
    """The `Disclosed by` sentence of a note with the given kernels, on one line."""
    if note.alternatives is None:
        cond = ""
    else:
        alts = [" and ".join(a.text for a in alt) for alt in note.alternatives]
        joined = alts[0] if len(alts) == 1 else ", ".join(alts[:-1]) + " or " + alts[-1]
        cond = " whose statement names " + joined
    return f"{START}{cond}: {', '.join(kernels) or 'none'}."


def wrap(text, first="", rest=""):
    """`text` wrapped at 100 columns, keeping each backquoted item on one line."""
    parts = re.split(r"(`[^`]*`)", text)
    text = "".join(p.replace(" ", "\0") if p.startswith("`") else p for p in parts)
    lines = textwrap.wrap(
        text,
        100,
        initial_indent=first,
        subsequent_indent=rest,
        break_long_words=False,
        break_on_hyphens=False,
    )
    return [line.replace("\0", " ") for line in lines]


def sentence(note, kernels):
    """The `Disclosed by` sentence of a note with the given kernels, wrapped at 100 columns."""
    return wrap(sentence_text(note, kernels))


def write(found, kernels, hits):
    """Rewrite each note's kernel list from the computed uses."""
    by_path = {}
    for n in found:
        by_path.setdefault(n.path, []).append(n)
    for path, ns in by_path.items():
        lines = (ROOT / path).read_text().split("\n")
        for n in sorted(ns, key=lambda n: n.span, reverse=True):
            uses = [k for k in kernels if k in computed(n, kernels, hits)]
            start, col, end, after = n.span
            head, tail = lines[start][:col], lines[end][after:]
            lead = head[: len(head) - len(head.lstrip())]
            # A sentence inside a field continues the field's two-space indentation.
            rest = "  " if lead or head.strip() else ""
            text = head.strip() + (" " if head.strip() else "") + sentence_text(n, uses) + tail
            lines[start : end + 1] = wrap(text.rstrip(), lead, rest)
        (ROOT / path).write_text("\n".join(lines))


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--lean", action="store_true", help="compute uses from the built project")
    parser.add_argument("--show", action="store_true", help="print each note's kernel list")
    parser.add_argument("--write", action="store_true", help="rewrite the 'Disclosed by' lists")
    args = parser.parse_args()
    kernels = kernel_names()
    registry_paths = {
        k: path for k in kernels if (path := ROOT / "Kernels" / k / "READINGS.md").is_file()
    }
    central = [k for k in kernels if k not in registry_paths]
    found, errors = notes()
    listed = theorem_lists()
    ids = {n.ident for n in found}
    hits = None
    if args.lean:
        unique = {a.key(): a for n in found for alt in n.alternatives or [] for a in alt}
        hits = lean_hits(kernels, list(unique.values()))
        if args.write:
            write(found, central, hits)
            for k, path in registry_paths.items():
                write_registry(path, {n.ident for n in found if k in computed(n, kernels, hits)})
            found, errors = notes()
    for k, readings in listed.items():
        for r in sorted(readings - ids):
            errors.append(f"Kernels/{k}/Theorem.lean lists {r}, which has no EXT note")
    registries = {}
    for k, path in registry_paths.items():
        readings, problems = read_registry(path)
        registries[k] = readings
        errors.extend(problems)
        rel = path.relative_to(ROOT)
        for ident in sorted(readings - ids):
            errors.append(f"{rel}: {ident} has no EXT note")
        if readings != listed[k]:
            errors.append(
                f"{rel}: entries differ from Theorem.lean "
                f"(missing {sorted(listed[k] - readings)}, extra {sorted(readings - listed[k])})"
            )
    for n in found:
        where = f"{n.path}:{n.line}: {n.ident}"
        disclosed = set(n.kernels)
        for k in sorted(disclosed - set(kernels)):
            errors.append(f"{where}: unknown kernel {k}")
        if len(n.kernels) != len(disclosed):
            errors.append(f"{where}: a kernel is listed twice")
        for k in sorted(disclosed & registry_paths.keys()):
            errors.append(f"{where}: {k} uses a kernel-local disclosure register")
        theorem = {k for k in central if n.ident in listed[k]}
        if theorem != disclosed:
            errors.append(
                f"{where}: 'Disclosed by' lists {sorted(disclosed)}, the Theorem.lean files "
                f"list it for {sorted(theorem)}"
            )
        if hits is not None:
            uses = computed(n, kernels, hits)
            recorded = disclosed | {k for k, readings in registries.items() if n.ident in readings}
            if uses != recorded:
                errors.append(
                    f"{where}: the statements name it for {sorted(uses)}, "
                    f"disclosures list {sorted(recorded)}"
                )
            if args.show:
                print(f"{n.ident}: {', '.join(sorted(uses)) or 'none'}")
    if args.show and hits is not None:
        for k in kernels:
            mine = sorted(n.ident for n in found if k in computed(n, kernels, hits))
            print(f"{k} ({len(mine)}): {', '.join(mine)}")
    if errors:
        print("\n".join(errors))
        sys.exit(1)
    print(f"{len(found)} EXT notes, {len(kernels)} kernels: disclosures consistent")


if __name__ == "__main__":
    os.environ.setdefault("LAKE_NO_UPDATE", "1")
    main()
