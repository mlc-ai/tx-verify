# SPDX-License-Identifier: Apache-2.0
"""Mechanical checks of the dependency rule (DEP-ORDER, Core/Assembly/Dependency.lean).

usage: check_witness.py --no-wildcard
       check_witness.py --kinds
       check_witness.py --rules
       check_witness.py --mutate WORKDIR

`--no-wildcard` fails when `Kind.resume`, `TcKind.resume` or `KindNeeds` has a match arm whose
kind pattern is a wildcard: Lean accepts a wildcard silently, so a new event kind would get no
classification or no needs without any error.

`--kinds` prints, for every constructor of `Kind` and `TcKind`, its resume class (`free`,
`blocking`, `observing`), and fails when a constructor is missing from `Kind.resume`,
`TcKind.resume` or `KindNeeds`.

`--rules` collects the definitions reachable from the fields of `Consistent`; for each one that
mentions another thread's events (`SameWarp`, `SameCta`, `SameCluster`, `SameGroup`, `laneOf`,
`MaskInstance`, `MaskK`) and matches an event kind (`⟨pc, .kind ..⟩`), it requires that kind to
be blocking or observing, or a memory access decided by the memory layer (`rd`, `nc`, `wr`,
`rmw`), or listed in RULE_EXEMPT with its reason. The scan is heuristic; the oracles and examples
of Tests/Progress/DependencyCoverage.lean are the binding check.

`--mutate WORKDIR` is the mutation run: for each family of `KindNeeds` it writes a mutant of
Core/Assembly/Dependency.lean that drops the family's first need or replaces its needs by
`[.cond False]`, compiles the mutant into a shadow of the build directory under WORKDIR, and
requires Tests/Progress/DependencyCoverage.lean to fail against it. It needs the built Core and the Lean
toolchain of the repository (`lake env`).
"""

import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEP = ROOT / "Core" / "Assembly" / "Dependency.lean"
TYPES = ROOT / "Core" / "Data" / "Types.lean"
EXECUTION = ROOT / "Core" / "Assembly" / "Execution.lean"
COVERAGE = ROOT / "Tests" / "Progress" / "DependencyCoverage.lean"

MEMORY_KINDS = {"rd", "nc", "wr", "rmw"}
# Kinds that a value rule reaches through another thread's events without being blocking, with
# the reason (each must be justified by a row of DEPENDENCY-CHECKLIST.md).
RULE_EXEMPT = {
    "activemask": "returns the active lanes without waiting (checklist A18, free)",
    "exit": "an exit is a witness of a need, not a waiting event",
    "tensorStore": "bulk-group bookkeeping of the issuing thread (checklist D11, D12)",
    "copy": "bulk-group bookkeeping of the issuing thread (checklist D1, D8)",
    "clcQuery": "the CLC safety rule compares the queries of one cluster; a query decodes a "
    "register and waits for nothing (checklist E9, design §4.4)",
}


def constructors(text, name):
    """The constructor names of `inductive <name> where`."""
    m = re.search(r"^inductive " + re.escape(name) + r" where\n(.*?)(?=^\S)", text, re.M | re.S)
    if not m:
        raise SystemExit(f"inductive {name} not found")
    return re.findall(r"^  \| (\w+)", m.group(1), re.M)


def definition(text, name):
    """The text of `def <name>` up to the next top-level declaration or comment."""
    m = re.search(
        r"^def " + re.escape(name) + r"\b.*?(?=^(?:def|theorem|structure|inductive|"
        r"open|/--|/-!|end)\b)",
        text,
        re.M | re.S,
    )
    if not m:
        raise SystemExit(f"def {name} not found")
    return m.group(0)


def arms(body):
    """The match arms of a definition, as lists of alternative patterns with their results."""
    out = []
    pending = ""
    for line in body.splitlines():
        s = line.strip()
        if s.startswith("| ") or (pending and not s.startswith("def ")):
            pending = (pending + " " + s).strip() if pending else s
            if "=>" in s:
                out.append(pending)
                pending = ""
    return out


def wildcard_arms(body, kind_index):
    """Arms whose kind pattern (position `kind_index` of a multi-pattern arm) is a wildcard."""
    bad = []
    for a in arms(body):
        for alt in re.split(r"\s\|\s", a[2:]):
            pats = alt.split("=>")[0]
            parts = [p.strip() for p in pats.split(",")]
            if kind_index < len(parts) and parts[kind_index] == "_":
                bad.append(a)
    return bad


def covered(body, ctors, prefix=""):
    """The constructors that an arm of `body` names."""
    found = set()
    for c in ctors:
        if re.search(r"\| [^=]*\." + prefix + re.escape(c) + r"\b", body) or re.search(
            r"(?:\|\s|,\s)\." + prefix + re.escape(c) + r"\b", body
        ):
            found.add(c)
    return found


def classes():
    """The resume class of every constructor of `Kind` and `TcKind`."""
    dep = DEP.read_text()
    types = TYPES.read_text()
    kinds = constructors(types, "Kind")
    tckinds = constructors(types, "TcKind")
    result = {}
    for name, ctors, prefix in (("Kind.resume", kinds, ""), ("TcKind.resume", tckinds, "")):
        body = definition(dep, name)
        for a in arms(body):
            rhs = a.split("=>")[-1].strip()
            cls = "blocking" if rhs.startswith(".blocking") else rhs.lstrip(".").split()[0]
            if name == "Kind.resume" and rhs == "k.resume":
                continue
            for c in ctors:
                if re.search(r"\." + re.escape(c) + r"\b", a.split("=>")[0]):
                    key = c if name == "Kind.resume" else "tc." + c
                    result[key] = cls
    return kinds, tckinds, result


def check_no_wildcard():
    dep = DEP.read_text()
    bad = []
    bad += wildcard_arms(definition(dep, "Kind.resume"), 0)
    bad += wildcard_arms(definition(dep, "TcKind.resume"), 0)
    bad += wildcard_arms(definition(dep, "KindNeeds"), 0)
    return bad


def check_kinds():
    kinds, tckinds, cls = classes()
    dep = DEP.read_text()
    needs = definition(dep, "KindNeeds")
    errors = []
    for c in kinds:
        if c != "tc" and c not in cls:
            errors.append(f"Kind.{c} has no line in Kind.resume")
        if c != "tc" and not re.search(r"\." + re.escape(c) + r"\b", needs):
            errors.append(f"Kind.{c} has no line in KindNeeds")
    for c in tckinds:
        if "tc." + c not in cls:
            errors.append(f"TcKind.{c} has no line in TcKind.resume")
        if not re.search(r"\.tc \(?\." + re.escape(c) + r"\b", needs):
            errors.append(f"TcKind.{c} has no line in KindNeeds")
    return cls, errors


def core_defs():
    """Every `def` of Core with its body text, by its last name component."""
    defs = {}
    for p in sorted((ROOT / "Core").rglob("*.lean")):
        text = p.read_text()
        for m in re.finditer(
            r"^def ([\w.']+)(.*?)(?=^(?:def|theorem|structure|inductive|"
            r"/--|/-!|end|instance|abbrev)\b)",
            text,
            re.M | re.S,
        ):
            defs.setdefault(m.group(1).split(".")[-1], []).append((m.group(1), m.group(2), p))
    return defs


MARKERS = ("SameWarp", "SameCta", "SameCluster", "SameGroup", "laneOf", "MaskInstance", "MaskK")


def check_rules():
    _, _, cls = classes()
    defs = core_defs()
    cons = EXECUTION.read_text()
    m = re.search(r"^structure Consistent.*?(?=^\S)", cons, re.M | re.S)
    frontier = set(re.findall(r"\b([A-Z][\w]*)\b", m.group(0)))
    seen = set()
    while frontier:
        n = frontier.pop()
        if n in seen or n not in defs:
            continue
        seen.add(n)
        for _, body, _ in defs[n]:
            frontier |= set(re.findall(r"\b([A-Za-z][\w]*)\b", body)) - seen
    errors = []
    for n in sorted(seen):
        for full, body, path in defs[n]:
            if full in ("KindNeeds", "maskNeeds", "tcNeeds") or "Needs" in full:
                continue
            if not any(k in body for k in MARKERS):
                continue
            for k in set(re.findall(r"⟨\w+, \.(\w+)", body)):
                if k == "tc":
                    continue
                c = cls.get(k)
                if c in ("blocking", "observing") or k in MEMORY_KINDS or k in RULE_EXEMPT:
                    continue
                if c is None:
                    continue
                errors.append(
                    f"{path.relative_to(ROOT)}: {full} reaches another thread's events "
                    f"of the {c} kind `{k}`"
                )
    return errors


FAMILIES = {
    "shfl": "maskNeeds L shflClass X e",
    "vote": "maskNeeds L voteClass X e",
    "redux": "maskNeeds L reduxClass X e",
    "match": "maskNeeds L matchClass X e",
    "cluster": "clusterNeeds L X e op",
    "bulkWait": "groupNeeds X e (.bulk mode)",
    "asyncWait": "groupNeeds X e .cpAsync",
}


def mutants(text):
    """(name, mutant text) pairs: each family's needs dropped by one, or made unsatisfiable."""
    out = []
    for fam, call in FAMILIES.items():
        if call not in text:
            raise SystemExit(f"KindNeeds call for {fam} not found: {call}")
        out.append((fam + "-drop", text.replace("=> " + call, "=> (" + call + ").drop 1", 1)))
        out.append((fam + "-false", text.replace("=> " + call, "=> [.cond False]", 1)))
    # The CTA barrier and allocation-management needs are mutated in their first part (the warp
    # lanes), which the Core lemmas about their history conditions do not name.
    for fam, part in (("bar", "ctaBarWarpNeeds L X e ++"), ("resource", "tcNeeds L X e ++")):
        head = part.removesuffix(" ++")
        if part not in text:
            raise SystemExit(f"needs part for {fam} not found: {part}")
        out.append((fam + "-drop", text.replace(part, "(" + head + ").drop 1 ++", 1)))
        out.append((fam + "-false", text.replace(part, "(.cond False :: " + head + ") ++", 1)))
    needs = definition(text, "KindNeeds")
    for fam, start in (
        ("elect", "| .elect mask inst _, e =>"),
        ("warpBar", "| .warpBar mask inst, e =>"),
        ("matrix", "| .matrix .., e =>"),
        ("setMaxReg", "| .setMaxReg .., e =>"),
    ):
        i = needs.index(start) + len(start)
        nxt = needs.index("\n  | ", i)
        body = needs[i:nxt]
        drop = needs[:i] + " (" + body.strip() + ").drop 1" + needs[nxt:]
        false = needs[:i] + " [.cond False]" + needs[nxt:]
        out.append((fam + "-drop", text.replace(needs, drop)))
        out.append((fam + "-false", text.replace(needs, false)))
    return out


def mutate(workdir):
    env = dict(os.environ)
    lean_path = subprocess.run(
        ["lake", "env", "printenv", "LEAN_PATH"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()
    lean = subprocess.run(
        ["elan", "which", "lean"], cwd=ROOT, capture_output=True, text=True, check=True
    ).stdout.strip()
    build = ROOT / ".lake" / "build" / "lib" / "lean"
    text = DEP.read_text()
    # A snapshot of the built Core, so that a concurrent build cannot remove an olean under a
    # mutant; each mutant links to it.
    snapshot = Path(workdir) / "snapshot"
    if snapshot.exists():
        shutil.rmtree(snapshot)
    shutil.copytree(build / "Core", snapshot / "Core")
    results = []
    for name, mtext in mutants(text):
        shadow = Path(workdir) / name
        if shadow.exists():
            shutil.rmtree(shadow)
        shutil.copytree(snapshot / "Core", shadow / "Core", copy_function=os.symlink)
        target = shadow / "Core" / "Assembly"
        for f in target.glob("Dependency.*"):
            f.unlink()
        (target / "Dependency.lean").write_text(mtext)
        env["LEAN_PATH"] = f"{shadow}:{lean_path}"
        comp = subprocess.run(
            [
                lean,
                "-s512000",
                f"--root={shadow}",
                str(target / "Dependency.lean"),
                "-o",
                str(target / "Dependency.olean"),
            ],
            cwd=ROOT,
            env=env,
            capture_output=True,
            text=True,
        )
        if comp.returncode != 0:
            results.append((name, "mutant does not compile", comp.stdout[-400:]))
            continue
        test = subprocess.run(
            [lean, "-s512000", str(COVERAGE)], cwd=ROOT, env=env, capture_output=True, text=True
        )
        results.append((name, "killed" if test.returncode != 0 else "SURVIVED", ""))
    return results


def main(argv):
    if not argv:
        print(__doc__)
        return 2
    if argv[0] == "--no-wildcard":
        bad = check_no_wildcard()
        for b in bad:
            print("wildcard arm:", b)
        return 1 if bad else 0
    if argv[0] == "--kinds":
        cls, errors = check_kinds()
        print(json.dumps(cls, indent=1, sort_keys=True))
        for e in errors:
            print(e)
        return 1 if errors else 0
    if argv[0] == "--rules":
        errors = check_rules()
        for e in errors:
            print(e)
        return 1 if errors else 0
    if argv[0] == "--mutate" and len(argv) == 2:
        res = mutate(argv[1])
        for name, status, detail in res:
            print(f"{name}: {status}{(' ' + detail) if detail else ''}")
        return 0 if all(s == "killed" for _, s, _ in res) else 1
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
