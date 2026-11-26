# SPDX-License-Identifier: Apache-2.0
"""The ledger of the cross-lane predicates of each tree (`<root>/Iface/`, tree.json "iface").

A Lean file under `<root>/Iface/` that defines a predicate used across lanes declares it in its
leading comment block (the `--` lines before `module`), one entry per predicate:

    -- iface: <Name> producer=<lane> status=<status> domain=<domain>

with <status> one of `stated`, `row-proved`, `proved` and <domain> one of `consistent`,
`complete`, `valid-rows`. An entry may continue on the following comment lines, which then hold
`key=value` words only, for a header longer than the line limit:

    -- iface: QTmaArrivedAtStage producer=B status=row-proved
    --        domain=consistent

An optional `ahead=1` (tree.json `"ahead": true`) marks a classification row that the coordinator
wrote ahead of its producer because it can be checked statically against the code (rule 9's
exception): its importers are not flagged while it is `stated`, and it is listed under its own
heading (`--ahead` lists only these). `--require-proved` fails while any predicate, ahead or not,
is below `proved`.

A line `-- domain: <domain>` of the leading block (the older form) gives the domain of the entries
of the file that do not name one. tree.json `iface` has the same entry. A vocabulary file without
an entry is fine. Reported: an entry malformed or missing a key; an entry and tree.json that
disagree; a file outside the producer lane's paths that imports an Iface module with a predicate
still `stated`; a domain the definition contradicts (`complete` without `Complete`, `valid-rows`
without a validity hypothesis); a word stated as `= .float` or `= Value.float` in a definition.

    Tools/iface.py [--tree K] [--ahead] [--require-proved]
"""

import argparse
import re
import sys

import trees

ENTRY = re.compile(r"^--\s*iface:\s*(.*)$")
CONTINUATION = re.compile(r"^--\s+(\w+=\S+(?:\s+\w+=\S+)*)\s*$")
OLD_DOMAIN = re.compile(r"^--\s*domain:\s*(\S+)\s*$")
VALUES = {
    "producer": None,
    "status": ("stated", "row-proved", "proved"),
    "domain": ("consistent", "complete", "valid-rows"),
    "ahead": ("0", "1"),
}
OPTIONAL = {"ahead"}
IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.M)
COMMAND = re.compile(r"^(?=\S)", re.M)
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|public|protected|noncomputable)\s+)*"
    r"(?:def|abbrev|structure|inductive|class|theorem|lemma)\s+(\S+)"
)
VALID = re.compile(r"[({⦃][^:(){}]*[Vv]alid[^:(){}]*:|:\s*[\w.]*Valid")
FLOAT = re.compile(r"=\s*(?:\.float|Value\.float)\b")


def leading_block(text):
    """The `--` lines before the first other non-blank line (normally `module`)."""
    out = []
    for line in text.splitlines():
        if line.startswith("--"):
            out.append(line.rstrip())
        elif line.strip():
            break
    return out


def parse_block(lines):
    """`(entries, problems)`: `[(name, producer, status, domain)]` of a leading block, and the
    malformed entries as strings."""
    entries, problems, current = [], [], None
    domain = None
    for line in lines:
        if m := ENTRY.match(line):
            words = m[1].split()
            current = {"name": words[0] if words else "", "words": words[1:], "line": line}
            entries.append(current)
        elif current is not None and (m := CONTINUATION.match(line)):
            current["words"] += m[1].split()
            current["line"] += " / " + line
        else:
            current = None
            if m := OLD_DOMAIN.match(line):
                domain = m[1]
    out = []
    for e in entries:
        keys = {}
        bad = not e["name"] or "=" in e["name"]
        for word in e["words"]:
            key, eq, value = word.partition("=")
            if not eq or key not in VALUES or key in keys:
                bad = True
            keys[key] = value
        if "domain" not in keys and domain is not None:
            keys["domain"] = domain
        for key, allowed in VALUES.items():
            if key not in keys and key in OPTIONAL:
                continue
            if key not in keys or (allowed and keys[key] not in allowed):
                bad = True
        if bad:
            problems.append(e["line"])
        else:
            ahead = keys.get("ahead") == "1"
            out.append((e["name"], keys["producer"], keys["status"], keys["domain"], ahead))
    return out, problems


def headers(tree):
    """`{module: [(name, producer, status, domain)]}` of the Iface files with entries, and the
    malformed entries as `[(file, line)]`."""
    out, bad = {}, []
    for path in sorted((tree.root / "Iface").rglob("*.lean")):
        rows, problems = parse_block(leading_block(path.read_text(errors="replace")))
        if rows:
            out[trees.module_name(path, tree.repo)] = rows
        bad += [(path, line) for line in problems]
    return out, bad


def definition(code, name):
    """The command of `code` (comments stripped) that defines `name`, or None."""
    for command in COMMAND.split(code):
        m = DECL.match(command)
        if m and (m[1] == name or m[1].endswith("." + name)):
            return command
    return None


def problems(tree):
    out = []
    found, bad = headers(tree)
    out += [f"{tree.kernel}: malformed iface header in {p.name}: {line}" for p, line in bad]
    named = {}
    for module, rows in found.items():
        path = trees.module_path(module, tree.repo)
        rel = path.relative_to(tree.repo).as_posix()
        code = trees.strip_comments(path.read_text(errors="replace"))
        for name, producer, status, domain, ahead in rows:
            named[name] = (module, producer, status)
            entry = tree.iface.get(name)
            if entry is None:
                out.append(f"{rel}: {name} is not in tree.json iface")
            else:
                for key, value in (("producer", producer), ("status", status), ("domain", domain)):
                    if entry.get(key) != value:
                        out.append(f"{rel}: {name} {key}={value}, tree.json says {entry.get(key)}")
                if ahead and not entry.get("ahead"):
                    out.append(f"{rel}: {name} ahead=1, tree.json does not say ahead")
            if producer not in tree.lanes:
                out.append(f"{rel}: {name}: producer {producer} is not a lane of tree.json")
            text = definition(code, name)
            if text is None:
                out.append(f"{rel}: {name} is not defined there")
                continue
            if domain == "complete" and "Complete" not in text:
                out.append(f"{rel}: {name} domain=complete without `Complete`")
            if domain == "valid-rows" and not VALID.search(text):
                out.append(f"{rel}: {name} domain=valid-rows without a validity hypothesis")
            if FLOAT.search(text):
                out.append(f"{rel}: {name} states a word as `= .float`")
    for name in tree.iface:
        if name not in named:
            out.append(f"{tree.kernel}: tree.json iface {name} has no header under Iface/")
    stated = {}
    for module, rows in found.items():
        for name, producer, status, _, _ in rows:
            if status == "stated" and not tree.iface.get(name, {}).get("ahead"):
                stated.setdefault(module, []).append((name, producer))
    for path in tree.files(generated=True):
        rel = path.relative_to(tree.repo).as_posix()
        code = trees.strip_comments(path.read_text(errors="replace"))
        for m in IMPORT.finditer(code):
            for name, producer in stated.get(m[1], []):
                if producer not in tree.lanes_of(rel):
                    out.append(f"{rel}: imports {m[1]} ({name} is only stated, by {producer})")
    return out


def ahead(tree):
    """`{name: status}` of the predicates written ahead by the coordinator (`"ahead": true`)."""
    return {n: e.get("status") for n, e in sorted(tree.iface.items()) if e.get("ahead")}


def unproved(tree):
    """`{name: status}` of the predicates (ahead or not) whose status is below `proved`, from
    tree.json and the headers."""
    out = {n: e.get("status") for n, e in tree.iface.items() if e.get("status") != "proved"}
    for rows in headers(tree)[0].values():
        out.update({row[0]: row[2] for row in rows if row[2] != "proved"})
    return dict(sorted(out.items()))


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    trees.add_tree_argument(ap)
    ap.add_argument("--ahead", action="store_true", help="list the predicates written ahead only")
    ap.add_argument(
        "--require-proved", action="store_true", help="fail while a predicate is below proved"
    )
    args = ap.parse_args(argv)
    rc = 0
    for tree in trees.load(args.tree):
        early = ahead(tree)
        if early:
            print(f"{tree.kernel}: written ahead by the coordinator (importable while stated):")
            for name, status in early.items():
                print(f"  {name}  status={status}")
        if args.ahead:
            continue
        for p in problems(tree):
            print(p)
            rc = 1
        if args.require_proved:
            for name, status in unproved(tree).items():
                print(f"{tree.kernel}: {name} is {status}, not proved")
                rc = 1
    return rc


if __name__ == "__main__":
    sys.exit(main())
