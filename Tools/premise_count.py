# SPDX-License-Identifier: Apache-2.0
"""Count the premises of each tree's top theorem (`Kernels/<K>/tree.json` "top").

A closed tree (`"closed": true`) proves its kernel correct for every launch that satisfies `Pre`.
A premise is any other hypothesis of the top theorem: a binder, a section variable other than the
launch's, an antecedent or a change of the conclusion, or a declaration of its file that could
stand for one (an axiom, a local definition). The count is zero and stays zero.

An open tree (`"closed": false`) states `correct (hp : Pre ...) (ho : Open ...)`; its premises are
the leaf fields of the structure `Open` in `top.open` (a field whose type is another structure of
the tree named `...Rest` or `...Open` counts as that structure's fields, recursively), plus any
binder of the top theorem beyond `Pre` and `Open`. The ledger (`premises` in tree.json) names
exactly these leaves. A name new since the merge base is registered as `split_of` a name the merge
base had, and that parent is no longer a leaf: so the number of leaves rises only by a registered
split, and no premise is added.

    python3 Tools/premise_count.py [--tree K]        # the premises and their number
    python3 Tools/premise_count.py --total           # the number only
    python3 Tools/premise_count.py --roadmap FILE    # fail unless FILE's first "N open premises" is N
    python3 Tools/premise_count.py --ledger          # fail unless the ledgers hold

Without `--roadmap`, the environment variable `TXVERIFY_TMLFA4_ROADMAP` names the roadmap for
the pytest (`tests/test_premise_count.py`).
"""

import argparse
import re
import sys
from pathlib import Path

import trees

ROOT = trees.ROOT
IDENT = r"[^\s()\[\]{}:,]+"
STRUCTURE = re.compile(
    rf"^(?:@\[[^\]]*\]\s*)?(?:(?:private|public|protected)\s+)*structure\s+({IDENT})"
)
FIELD = re.compile(r"^(\s+)([^\s()\[\]{}:]+)\s*((?:[({\[][^)}\]]*[)}\]]\s*)*):(.*)$")

DOC = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT = re.compile(r"--[^\n]*")
IMPORT = re.compile(r"^(?:public\s+)?import\s+(\S+)$")
COMMAND = re.compile(r"^(?=\S)", re.MULTILINE)
ROADMAP_COUNT = re.compile(r"(\d+) open premises")
OPENING, CLOSING = "([{\u2983", ")]}\u2984"


def strip_comments(text: str) -> str:
    """The source without block and line comments (doc comments included)."""
    return LINE_COMMENT.sub("", DOC.sub("", text))


def normal(text: str) -> str:
    """The text with every run of white space a single blank."""
    return " ".join(text.split())


def split_top(text: str, token: str) -> tuple[str, str] | None:
    """The text before and after the first `token` outside every bracket."""
    depth = 0
    for i, char in enumerate(text):
        if depth == 0 and text.startswith(token, i):
            return text[:i], text[i + len(token) :]
        depth += (char in OPENING) - (char in CLOSING)
    return None


def binders(text: str) -> list[str]:
    """The bracketed groups and the bare names of a binder list, in order."""
    out, depth, start = [], 0, None
    for i, char in enumerate(text):
        if start is None and not char.isspace():
            start = i
        depth += (char in OPENING) - (char in CLOSING)
        if start is not None and depth == 0 and (char in CLOSING or char.isspace()):
            out.append(normal(text[start : i + 1]))
            start = None
    if start is not None:
        out.append(normal(text[start:]))
    return out


class Top:
    """The top theorem of a tree (`tree.json` "top")."""

    def __init__(self, tree):
        top = tree.top
        self.tree = tree
        self.correct = tree.root / top.get("correct", "Top/Correct.lean")
        self.name = top.get("theorem", "correct")
        rel_dir = Path(top.get("correct", "Top/Correct.lean")).parent.parts
        self.namespace = top.get("namespace") or ".".join([tree.namespace, *rel_dir])
        self.variables = top.get("variables", [])
        self.hypothesis = top.get("hypothesis")
        self.conclusion = top.get("conclusion")
        self.open = tree.root / top["open"] if top.get("open") else None


def theorem_premises(command: str, top: Top) -> list[str]:
    """What the theorem's statement assumes or changes beyond `Pre` (and `Open` in an open tree)."""
    head = split_top(command, ":=")
    statement = head[0] if head else command
    parts = split_top(statement, ":")
    if parts is None:
        return [f"no statement: {normal(command)}"]
    name, _, rest = parts[0].partition(top.name)
    out = [] if normal(name) == "theorem" else [f"modifier: {normal(name)}"]
    given = binders(rest)
    if top.tree.closed:
        out += [f"hypothesis: {b}" for b in given if b != top.hypothesis]
        if top.hypothesis not in given:
            out.append(f"missing: {top.hypothesis}")
    else:
        out += [f"hypothesis: {b}" for b in given if not allowed_open(b)]
        for head_ in ("Pre", "Open"):
            if not any(binder_type(b).split()[:1] == [head_] for b in given):
                out.append(f"missing: a hypothesis `{head_} ...`")
    if top.conclusion is not None and normal(parts[1]) != top.conclusion:
        out.append(f"conclusion: {normal(parts[1])}")
    return out


def binder_type(binder: str) -> str:
    """The type of a bracketed binder `(h : T)` ("" for a bare name)."""
    if binder[:1] not in OPENING:
        return ""
    inner = binder[1:-1]
    parts = split_top(inner, ":")
    return normal(parts[1]) if parts else ""


def allowed_open(binder: str) -> bool:
    """An implicit parameter, or a hypothesis `Pre ...` or `Open ...` (open trees)."""
    if binder[:1] in "{\u2983":
        return True
    return binder[:1] == "(" and binder_type(binder).split()[:1] in (["Pre"], ["Open"])


def premises(text: str, top: Top) -> list[str]:
    """Every premise of the top theorem in the source of its file (beyond `Open`)."""
    out: list[str] = []
    found = 0
    closed = top.tree.closed
    for command in COMMAND.split(strip_comments(text)):
        command = command.strip()
        line = normal(command)
        if not line or line == "module" or IMPORT.match(line):
            continue
        if line in ("@[expose] public section", "section", "public section", "end", "open PTX"):
            continue
        if line in (f"namespace {top.namespace}", f"end {top.namespace}"):
            continue
        if line.startswith("variable "):
            given = binders(command[len("variable") :])
            if closed:
                out += [f"variable: {b}" for b in given if b not in top.variables]
            else:
                out += [f"variable: {b}" for b in given if not allowed_open(b)]
        elif re.search(rf"\btheorem {re.escape(top.name)}(?![\w.'])", line):
            found += 1
            out += theorem_premises(command, top)
        elif closed:
            out.append(f"declaration: {line}")
        elif line.startswith(("include ", "axiom ", "local ", "notation ", "instance ")):
            out.append(f"declaration: {line}")
    if found != 1:
        out.append(f"{found} theorems {top.name}")
    if re.search(r"\b(sorry|admit|axiom|native_decide)\b", strip_comments(text)):
        out.append("sorry, admit, axiom or native_decide")
    return out


class Struct:
    """A structure of the tree: its full name, command text, file, and the namespaces and `open`s
    in force where it is declared (to resolve the names in its fields)."""

    def __init__(self, full, command, path, namespace, opens):
        self.full, self.command, self.path = full, command, path
        self.namespace, self.opens = namespace, opens


NAMESPACE = re.compile(r"^namespace\s+(\S+)")
SECTION_START = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:public\s+)?(?:noncomputable\s+)?section\b")
END_BLOCK = re.compile(r"^end\b(?:\s+(\S+))?")
OPEN_LINE = re.compile(r"^open\s+(?:scoped\s+)?([^(\n]+)")


def structures(tree) -> dict[str, Struct]:
    """`{full name: Struct}` of the structures of a tree (comments stripped). A structure
    `structure A.B.Rest` inside `namespace N` is `N.A.B.Rest`; `_root_.X` is `X`."""
    out = {}
    for path in tree.files():
        stack = []  # (kind, namespace parts, opens) per open block
        ns, opens = [], []
        for command in COMMAND.split(strip_comments(path.read_text())):
            head = command.strip()
            if m := NAMESPACE.match(head):
                stack.append((list(ns), list(opens)))
                ns = ns + m[1].split(".")
            elif SECTION_START.match(head):
                stack.append((list(ns), list(opens)))
            elif END_BLOCK.match(head):
                if stack:
                    ns, opens = stack.pop()
            elif m := OPEN_LINE.match(head):
                opens += m[1].split()
            elif m := STRUCTURE.match(head):
                name = m[1]
                full = (
                    name[len("_root_.") :] if name.startswith("_root_.") else ".".join([*ns, name])
                )
                out.setdefault(full, Struct(full, head, path, ".".join(ns), list(opens)))
    return out


def resolve(name: str, struct: Struct, index: dict) -> str | None:
    """The full name of the structure that `name`, written in `struct`'s file, denotes: as Lean
    does, the innermost enclosing namespace first, then the root, then the `open` namespaces."""
    name = name.removeprefix("@")
    if name.startswith("_root_."):
        name = name[len("_root_.") :]
        return name if name in index else None
    parts = struct.namespace.split(".") if struct.namespace else []
    candidates = [".".join([*parts[:k], name]) for k in range(len(parts), -1, -1)]
    candidates += [f"{o}.{name}" for o in struct.opens]
    for opened in struct.opens:  # `open X` inside namespace N also opens N.X
        candidates += [".".join([*parts[:k], opened, name]) for k in range(len(parts), 0, -1)]
    return next((c for c in candidates if c in index), None)


def fields(command: str) -> list[tuple[str, str]]:
    """`[(name, type)]` of a structure command: its `extends` parents as `("extends", parent)`,
    then the fields at the first indentation after `where`."""
    out = []
    head, _, body = command.partition(" where")
    if " extends " in head:
        for parent in split_commas(head.split(" extends ", 1)[1].split(" : ")[0]):
            out.append(("extends", normal(parent)))
    indent = None
    current = None
    for line in body.splitlines():
        if not line.strip() or "::" in line:
            continue
        width = len(line) - len(line.lstrip())
        if indent is None:
            indent = width
        if width == indent and (m := FIELD.match(line)):
            current = [m[2], m[4]]
            out.append(current)
        elif width > indent and current is not None:
            current[1] += " " + line.strip()
    return [(n, normal(t)) for n, t in out]


def split_commas(text: str) -> list[str]:
    parts, depth, start = [], 0, 0
    for i, char in enumerate(text):
        depth += (char in OPENING) - (char in CLOSING)
        if char == "," and depth == 0:
            parts.append(text[start:i])
            start = i + 1
    parts.append(text[start:])
    return [p for p in parts if p.strip()]


def head_name(type_: str) -> str:
    """The head constant of a type, as written (`Safe.NoUb.Rest` of `Safe.NoUb.Rest P L m`); of a
    `∀ …, … → C args` the head of its conclusion `C`."""
    if type_.lstrip().startswith("∀") and "→" in type_:
        type_ = type_.rsplit("→", 1)[1]
    word = type_.split()[0] if type_.split() else ""
    return word.strip("()")


def open_leaves(tree, name: str = "Open", bundles: tuple = ()) -> list[str]:
    """The leaf fields of the structure `name` of the top's `open` file, named by their dotted
    path from it (`noUb.whole`; a direct field keeps its bare name). A field whose type is another
    structure of the tree named `...Rest` or `...Open` (resolved by its qualified name) counts as
    that structure's fields, under the field's name; a parent of `extends` counts as its fields
    without a prefix. With `bundles` (name suffixes, `tree.json` "bundles"), an input bundle (a
    structure of hypotheses that a proved class still takes) counts as its fields too: the honest
    count of what is unproved."""
    index = structures(tree)
    top = Top(tree)
    roots = [s for f, s in index.items() if f.rsplit(".", 1)[-1] == name and s.path == top.open]
    if not roots:
        roots = [s for f, s in index.items() if f.rsplit(".", 1)[-1] == name]
    if not roots:
        return [f"missing structure {name}"]

    def walk(struct, prefix, seen):
        out = []
        for field, type_ in fields(struct.command):
            target = resolve(head_name(type_), struct, index)
            short = (target or "").rsplit(".", 1)[-1]
            if target and short.endswith(("Rest", "Open") + bundles) and target not in seen:
                inner = prefix if field == "extends" else f"{prefix}{field}."
                out += walk(index[target], inner, seen | {target})
            elif field != "extends":
                out.append(prefix + field)
        return out

    return walk(roots[0], "", {roots[0].full})


def count(tree) -> list[str]:
    """The premises of the tree's top theorem: for an open tree the leaves of `Open` (as
    `open: name`) and the extra hypotheses; for a closed tree the hypotheses beyond `Pre`."""
    top = Top(tree)
    out = premises(top.correct.read_text(), top)
    if not tree.closed:
        out = [f"open: {leaf}" for leaf in open_leaves(tree)] + out
    return out


def leaf_names(tree) -> list[str]:
    return [p.removeprefix("open: ") for p in count(tree) if p.startswith("open: ")]


def ledger_problems(tree, base=None) -> list[str]:
    """The ledger of an open tree against `Open` and the merge base (`base`: its tree.json, None
    for no bound); a closed tree has no premise."""
    found = count(tree)
    if tree.closed:
        out = [f"{tree.kernel}: premise {p}" for p in found]
        if tree.premises:
            out.append(f"{tree.kernel}: closed tree with a premise ledger")
        return out
    out = [f"{tree.kernel}: {p}" for p in found if not p.startswith("open: ")]
    leaves = leaf_names(tree)
    if len(set(leaves)) != len(leaves):
        twice = sorted({n for n in leaves if leaves.count(n) > 1})
        out.append(f"{tree.kernel}: leaf names twice: {twice}")
    ledger = set(tree.premises)
    if set(leaves) != ledger:
        out.append(
            f"{tree.kernel}: Open but not in the ledger {sorted(set(leaves) - ledger)}, "
            f"in the ledger but not in Open {sorted(ledger - set(leaves))}"
        )
    if base is not None and not base.get("closed", False):
        old = base.get("premises", {})
        for name in sorted(ledger - set(old)):
            parent = (tree.premises.get(name) or {}).get("split_of")
            if parent not in old:
                out.append(f"{tree.kernel}: new premise {name} is not split_of one of the base")
            elif parent in ledger:
                out.append(f"{tree.kernel}: {name} is split_of {parent}, which is still open")
    elif base is not None and base.get("closed", False) and leaves:
        out.append(f"{tree.kernel}: the tree was closed at the merge base")
    return out


def roadmap_count(text: str) -> int | None:
    """The first "N open premises" of a roadmap."""
    match = ROADMAP_COUNT.search(text)
    return int(match.group(1)) if match else None


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    trees.add_tree_argument(parser)
    parser.add_argument("--total", action="store_true", help="print the total only")
    parser.add_argument("--roadmap", type=Path, help="roadmap whose count must agree")
    parser.add_argument("--ledger", action="store_true", help="check the premise ledgers")
    parser.add_argument(
        "--inputs", action="store_true", help="count input bundles (tree.json bundles) as fields"
    )
    args = parser.parse_args(argv)
    rc = 0
    for tree in trees.load(args.tree):
        found = count(tree)
        if args.inputs:
            name = Top(tree).open_name if hasattr(Top(tree), "open_name") else "Open"
            found = open_leaves(tree, name, tuple(tree.cfg.get("bundles", [])))
        if not args.total:
            for premise in found:
                print(f"{tree.kernel}: {premise}")
        print(len(found) if args.total else f"{len(found):3d}  total  {tree.kernel}")
        if args.ledger:
            for problem in ledger_problems(tree, tree.base_config()):
                print(problem, file=sys.stderr)
                rc = 1
        if args.roadmap is not None:
            written = roadmap_count(args.roadmap.read_text())
            if written != len(found):
                print(
                    f"{args.roadmap}: says {written} open premises, counted {len(found)}",
                    file=sys.stderr,
                )
                rc = 1
    return rc


if __name__ == "__main__":
    sys.exit(main())
