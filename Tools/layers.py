# SPDX-License-Identifier: Apache-2.0
"""The layering of each proof tree, as counters that fall to zero (`Kernels/<K>/tree.json`).

    Tools/layers.py [--tree K] [--list COUNTER] [--lower]

A role's directories are its own; a role reads another role only where `roles` allows it. The
layers above (`upper`) read a role's `Export/` modules only, and do not open a role: no `import
all`, no role invariant by name (`role_invariants`), no case split on the role (`role_match`).
The public statements above the role line (`Export/`, `upper`) name no state (`state_names`), the
tree imports no old tree (`old_roots`), and no role internal reaches an upper module or the common
`Export`/`Follow` through public imports, so editing a role's `Ref` rebuilds nothing above it.

`--lower` lowers the ceilings in `tree.json` to the counts; it never raises one.
"""

import argparse
import re
import sys

import trees
from modcost import Graph, parse_header

IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(all\s+)?(\S+)", re.M)
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(private|public|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|axiom)\b"
)
SECTION = re.compile(r"^(?:@\[[^\]]*\]\s*)?(public\s+)?(section|namespace)\b(?:\s+(\S+))?")
END = re.compile(r"^end\b(?:\s+(\S+))?")
COMMAND = re.compile(r"^(?=\S)", re.M)
OPENING, CLOSING = "([{⦃", ")]}⦄"

BOUNDARY = ("Export", "Follow")
COUNTERS = (
    "upper imports of role internals",
    "imports between roles",
    "upper import all",
    "upper names of role invariants",
    "upper case splits on the role",
    "imports of old roots",
    "state names in public statements",
    "role matches outside Common",
    "role internals rebuilding upper modules",
)


def split_top(text, tokens):
    """The text before the first of `tokens` outside every bracket (the whole text if none)."""
    depth = 0
    for i, char in enumerate(text):
        if depth == 0 and any(text.startswith(t, i) for t in tokens):
            return text[:i]
        depth += (char in OPENING) - (char in CLOSING)
    return text


def public_signatures(code, export):
    """`(line, signature)` of the declarations of `code` (comments stripped) that are statements
    above the role line: in an `Export/` file the public ones, elsewhere every non-private one. A
    signature is the command up to its `:=`, `where` or first `|` alternative; a structure, class
    or inductive is whole."""
    out, stack = [], []
    line = 1
    for command in COMMAND.split(code):
        start, line = line, line + command.count("\n")
        head = command.lstrip()
        if m := SECTION.match(head):
            stack.append(bool(m[1]) and m[2] == "section")
            continue
        if END.match(head):
            if stack:
                stack.pop()
            continue
        m = DECL.match(head)
        if not m:
            continue
        mods = re.findall(r"\b(private|public)\s", head[: m.start(2)])
        if "private" in mods:
            continue
        if export and "public" not in mods and not any(stack):
            continue
        if m[2] in ("structure", "class", "inductive"):
            sig = command
        else:
            sig = split_top(command, (":=", " where", "\n  |", "\n|"))
        out.append((start, sig))
    return out


def counters(tree, graph=None):
    """Counter name -> list of `file: item` for one tree."""
    out = {name: [] for name in COUNTERS}
    old = tuple(r.replace("/", ".") + "." for r in tree.old_roots)
    for path in tree.files():
        rel = path.relative_to(tree.root).as_posix()
        role = tree.role_of(path)
        kind, top = role
        upper = kind == "upper"
        code = trees.strip_comments(path.read_text(errors="replace"))
        for m in IMPORT.finditer(code):
            all_, name = m[1], m[2]
            if name.startswith(old):
                out["imports of old roots"].append(f"{rel}: {name}")
            if not name.startswith(tree.module_prefix):
                continue
            target = tree.module_role(name)
            if upper:
                if tree.is_role_internal(trees.module_path(name, tree.repo)):
                    out["upper imports of role internals"].append(f"{rel}: {name}")
                if all_:
                    out["upper import all"].append(f"{rel}: {name}")
            elif kind == "role" and target and target[0] == "role":
                if target[1] != top and target[1] not in tree.roles.get(top, []):
                    out["imports between roles"].append(f"{rel}: {name}")
        body = IMPORT.sub("", code)
        if upper:
            out["upper names of role invariants"] += [
                f"{rel}: {m[0]}" for rx in tree.role_invariants for m in rx.finditer(body)
            ]
            out["upper case splits on the role"] += [
                f"{rel}: {m[0]}" for rx in tree.role_match for m in rx.finditer(body)
            ]
        if kind != "common":
            out["role matches outside Common"] += [
                f"{rel}: {m[0]}" for rx in tree.role_match for m in rx.finditer(body)
            ]
        export = tree.is_export(path)
        if upper or export:
            for line, sig in public_signatures(code, export):
                out["state names in public statements"] += [
                    f"{rel}:{line}: {m[0]}" for rx in tree.state_names for m in rx.finditer(sig)
                ]
    out["role internals rebuilding upper modules"] = rebuild_leaks(tree, graph)
    return out


def tree_graph(tree):
    """The import graph of the tree's files and what they import (the rest is a leaf)."""
    headers = {}
    for path in tree.files(generated=True):
        text = path.read_text(errors="replace")
        headers[trees.module_name(path, tree.repo)] = parse_header(text.splitlines())
    for _, imports in list(headers.values()):
        for imp in imports:
            headers.setdefault(imp.module, (True, []))
    return Graph(headers)


def rebuild_leaks(tree, graph=None):
    """`upper file: role internal` (rule 3: editing a role's `Ref` rebuilds no upper file).

    An upper file counts every role internal it reads: each direct import, public or private, and
    that import's public closure. A boundary file of the common layer (`Common/Export.lean`,
    `Common/Export/*`, `Common/Follow.lean`, `Common/Follow/*`) reads role internals privately by design; it counts only the role internals
    in its own public import closure, which its importers would read again."""
    graph = graph or tree_graph(tree)
    internal = [
        m
        for m in graph.names
        if m.startswith(tree.module_prefix)
        and tree.is_role_internal(trees.module_path(m, tree.repo))
    ]
    mask = 0
    for m in internal:
        mask |= graph.bit[m]
    out = []
    for m in graph.names:
        path = trees.module_path(m, tree.repo)
        if not m.startswith(tree.module_prefix) or tree.is_generated(path):
            continue
        role = tree.role_of(path)
        parts = tree.parts(path)
        if role[0] == "upper":
            hit = graph.reads(m) & mask
        elif role[0] == "common" and len(parts) > 1 and parts[1].removesuffix(".lean") in BOUNDARY:
            hit = graph.pub(m) & mask
        else:
            continue
        if hit:
            rel = path.relative_to(tree.root).as_posix()
            out += [f"{rel}: {r}" for r in internal if hit & graph.bit[r]]
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    trees.add_tree_argument(ap)
    ap.add_argument("--list", metavar="COUNTER")
    ap.add_argument("--lower", action="store_true", help="lower the ceilings to the counts")
    args = ap.parse_args(argv)
    over = 0
    for tree in trees.load(args.tree):
        now = counters(tree)
        if args.list:
            print("\n".join(now[args.list]))
            continue
        print(tree.kernel)
        for name, items in now.items():
            files = len({i.split(":")[0] for i in items})
            top = tree.ceiling(name)
            mark = "  ABOVE ITS CEILING" if isinstance(top, int) and len(items) > top else ""
            over += bool(mark)
            print(f"{len(items):6}  {files:4} files  (ceiling {top:5})  {name}{mark}")
        if args.lower:
            for name, (a, b) in tree.lower_ceilings({k: len(v) for k, v in now.items()}).items():
                print(f"  lowered {name}: {a} -> {b}")
    return 1 if over else 0


if __name__ == "__main__":
    sys.exit(main())
