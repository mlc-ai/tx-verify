# SPDX-License-Identifier: Apache-2.0
"""What a modification costs: files, hunks, modules rebuilt, check time, critical path.

    Tools/modcost.py FILE.lean [FILE ...]      # the files as edited in the working tree
    Tools/modcost.py --commit REV              # the Lean files a commit changes
    Tools/modcost.py --counters                # the pattern counters of tml-fa4's Proof

The rebuild set is the set of modules whose Lake trace reads the public interface (`.olean`) of an
edited file. It is what an edit of that interface rebuilds, and an upper bound for any other edit:
an edit that leaves `.olean` as it was (a proof, a comment, a private theorem) rebuilds the edited
file alone (`Lemmas/DECISIONS.md`, "What decides a rebuild"). A module reads the interface of what
it imports, privately or publicly, and of everything reached from there by `public import`; a
private import is invisible to the module's own importers. `import all`, `meta import` and files
without a `module` header read more, as in Lake's `ModuleImportInfo.addImport`.

Check times are the minimum over the `Built <module> (<time>)` lines of the Lake logs, which
`--logs` names (default: `.lake/build-logs/*.log`); modules without a time are counted.
"""

import argparse
import collections
import glob
import re
import subprocess
import sys
from pathlib import Path

from build_budget import critical_path, module_times

ROOT = Path(__file__).resolve().parents[1]
TOPS = ("Core", "Assumption", "Lemmas", "Tactics", "Tests", "Kernels")
IMPORT = re.compile(r"^(public\s+)?(meta\s+)?import\s+(all\s+)?([^\s-]\S*)")
MODULE = re.compile(r"^module\s*$")

Import = collections.namedtuple("Import", "module public meta all")


def module_name(path):
    return ".".join(Path(path).with_suffix("").parts)


def parse_header(lines):
    """`(is a module, imports)` of a file, from its text or its header lines."""
    is_module, imports = False, []
    for line in lines:
        if MODULE.match(line):
            is_module = True
        elif m := IMPORT.match(line):
            imports.append(Import(m[4], bool(m[1]), bool(m[2]), bool(m[3])))
    return is_module, imports


def git(*args, root=ROOT):
    return subprocess.run(
        ["git", "-C", str(root), *args], capture_output=True, text=True, check=True
    ).stdout


class Graph:
    """The import graph, with the set of modules whose interface each module reads."""

    def __init__(self, headers):
        self.imports = {
            m: [i for i in imps if i.module in headers] for m, (_, imps) in headers.items()
        }
        self.is_module = {m: is_mod for m, (is_mod, _) in headers.items()}
        self.names = sorted(headers)
        self.bit = {m: 1 << k for k, m in enumerate(self.names)}
        self._pub, self._all, self._every, self._reads = {}, {}, {}, {}
        sys.setrecursionlimit(100000)
        self._rev = None

    @classmethod
    def from_tree(cls, root=ROOT):
        headers = {}
        for top in TOPS:
            for path in (root / top).rglob("*.lean"):
                text = path.read_text(errors="replace")
                headers[module_name(path.relative_to(root))] = parse_header(text.splitlines())
        return cls(headers)

    @classmethod
    def from_commit(cls, rev, root=ROOT):
        paths = git("ls-tree", "-r", "--name-only", rev, "--", *TOPS, root=root).splitlines()
        lines = {p: [] for p in paths if p.endswith(".lean")}
        pattern = r"^((public +)?(meta +)?import +|module *$)"
        out = git("grep", "-E", pattern, rev, "--", *TOPS, root=root)
        for line in out.splitlines():
            path, text = line[len(rev) + 1 :].split(":", 1)
            if path in lines:
                lines[path].append(text)
        return cls({module_name(p): parse_header(ls) for p, ls in lines.items()})

    def _mix(self, memo, name, step):
        if name not in memo:
            out = 0
            for imp in self.imports[name]:
                if (deps := step(imp)) is not None:
                    out |= self.bit[imp.module] | deps
            memo[name] = out
        return memo[name]

    # Lake's transitive traces of a module: public, all, and meta/legacy (every import).
    def pub(self, name):
        def step(imp):
            if not imp.public:
                return None
            return self.every(imp.module) if imp.meta else self.pub(imp.module)

        return self._mix(self._pub, name, step)

    def all(self, name):
        def step(imp):
            if imp.all:
                return self.all(imp.module)
            return self.every(imp.module) if imp.meta else self.pub(imp.module)

        return self._mix(self._all, name, step)

    def every(self, name):
        return self._mix(self._every, name, lambda imp: self.every(imp.module))

    def reads(self, name):
        def step(imp):
            if not self.is_module[name] or imp.meta:
                return self.every(imp.module)
            return self.all(imp.module) if imp.all else self.pub(imp.module)

        return self._mix(self._reads, name, step)

    def downstream(self, names):
        mask = 0
        for n in names:
            mask |= self.bit[n]
        return {m for m in self.names if self.reads(m) & mask} | set(names)

    def downstream_static(self, names):
        """Reverse reachability through imports of every kind: what comes after in the build."""
        if self._rev is None:
            self._rev = collections.defaultdict(list)
            for m, imps in self.imports.items():
                for i in imps:
                    self._rev[i.module].append(m)
        return closure(names, self._rev)

    def upstream(self, names):
        return closure(names, {m: [i.module for i in imps] for m, imps in self.imports.items()})


def closure(names, edges):
    seen, stack = set(names), list(names)
    while stack:
        for n in edges.get(stack.pop(), ()):
            if n not in seen:
                seen.add(n)
                stack.append(n)
    return seen


def group(name, kernels):
    """The report class of a module, for an edit in the given kernels."""
    parts = name.split(".")
    if parts[0] != "Kernels":
        return {"Tests": "tests"}.get(parts[0], "library")
    kernel, rest = parts[1], parts[2:]
    if kernels and kernel not in kernels:
        return f"other kernel {kernel}"
    if rest[:1] != ["Proof"]:
        return f"{kernel} other"
    if rest[1:2] == ["Top"]:
        return f"{kernel} Proof Top/" + (rest[2] if len(rest) > 3 else "")
    return f"{kernel} Proof"


def summarise(graph, modules, times):
    """Check time, critical path inside the set, and the number of modules without a time."""
    sub = {m: [i.module for i in graph.imports[m] if i.module in modules] for m in modules}
    crit, chain = critical_path(times, sub) if sub else (0.0, [])
    total = sum(times.get(m, 0.0) for m in modules)
    return total, crit, chain, sum(m not in times for m in modules)


def cost(graph, changed, times, target=None):
    """The rebuild set of `changed`, its size by group, its check time and critical path."""
    modules = graph.downstream(changed)
    if target:
        modules &= graph.upstream([target])
    kernels = {m.split(".")[1] for m in changed if m.startswith("Kernels.")}
    groups = collections.defaultdict(list)
    for m in modules:
        groups[group(m, kernels)].append(m)
    total, crit, chain, untimed = summarise(graph, modules, times)
    return {
        "modules": modules,
        "groups": dict(groups),
        "seconds": total,
        "critical": crit,
        "chain": chain,
        "untimed": untimed,
    }


def hunks(diff):
    """`{path: hunks}` of a `--unified=0` diff."""
    out, path = {}, None
    for line in diff.splitlines():
        if line.startswith("diff --git "):
            path = line.split(" b/", 1)[1]
            out[path] = 0
        elif line.startswith("@@ ") and path:
            out[path] += 1
    return out


# The patterns of the architecture plan that may not become more frequent: (name, directories
# under the kernel's Proof, pattern, whether occurrences or lines are counted).
COUNTERS = (
    ("hData hN hD hS call lines", ("",), r"hData hN hD hS", False),
    ("cases i with", ("Top", "Progress", "Bound"), r"cases i with", False),
    ("lane invariant unfolded", ("",), r"unfold JR|\bJR_eq\b", False),
    ("positional projections", ("",), r"(?:\.2){3}", True),
    ("all_goals simp_all", ("",), r"^\s*all_goals simp_all\s*$", False),
    ("code lookups per list element", ("",), r"\.all \(fun pc => .*code\[pc\]\?", False),
    ("role table re-entered", ("",), r"ev_of_ne_ub \(T := table", False),
)

# A block of this many proof lines (numbers normalised, at least BLOCK_CHARS characters) that occurs
# in two files is copied.
BLOCK, BLOCK_CHARS = 12, 250
SKIP_LINE = ("--", "import ", "public import ", "set_option ", "variable ", "open ")


def copied_lines(proof2):
    """`{file: line numbers}` of the proof lines that another file repeats."""
    seen = {}
    for path in sorted(proof2.rglob("*.lean")):
        if {"Gen", "ShapeSet"} & set(path.relative_to(proof2).parts):
            continue
        lines = []
        for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            text = re.sub(r"\b\d+\b", "N", " ".join(line.split()))
            if text and not text.startswith(SKIP_LINE):
                lines.append((i, text))
        for j in range(len(lines) - BLOCK + 1):
            block = lines[j : j + BLOCK]
            text = "\n".join(t for _, t in block)
            if len(text) > BLOCK_CHARS:
                seen.setdefault(text, []).append((path, [i for i, _ in block]))
    out = {}
    for places in seen.values():
        if len({path for path, _ in places}) > 1:
            for path, numbers in places:
                out.setdefault(path, set()).update(numbers)
    return out


def counters(proof2):
    out = {}
    for name, dirs, pattern, each in COUNTERS:
        rx, n = re.compile(pattern), 0
        for d in dirs:
            for path in sorted((proof2 / d).rglob("*.lean")):
                for line in path.read_text(encoding="utf-8").splitlines():
                    n += len(rx.findall(line)) if each else bool(rx.search(line))
        out[name] = n
    out["copied proof lines"] = sum(map(len, copied_lines(proof2).values()))
    return out


def main(argv=None):
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("files", nargs="*", type=Path)
    parser.add_argument("--commit", help="measure the Lean files this commit changes")
    parser.add_argument("--target", help="count only what this module's build needs")
    parser.add_argument("--logs", nargs="+", default=[str(ROOT / ".lake/build-logs/*.log")])
    parser.add_argument("--upstream", action="store_true", help="also the modules below the files")
    parser.add_argument("--list", action="store_true", help="name the rebuilt modules")
    parser.add_argument("--counters", action="store_true")
    args = parser.parse_args(argv)
    if args.counters:
        for name, n in counters(ROOT / "Kernels/TmlFa4Fwd/Proof").items():
            print(f"{n:6d}  {name}")
        return 0
    if bool(args.files) == bool(args.commit):
        parser.error("give files or --commit")
    if args.commit:
        rev = git("rev-parse", args.commit).strip()
        graph = Graph.from_commit(rev)
        diff = hunks(git("show", "-m", "--first-parent", "--format=", "--unified=0", rev))
    else:
        graph = Graph.from_tree()
        paths = [f.resolve().relative_to(ROOT) for f in args.files]
        diff = {str(p): 0 for p in paths}
        diff.update(hunks(git("diff", "--unified=0", "HEAD", "--", *map(str, paths))))
    changed = [m for m in (module_name(p) for p in diff if p.endswith(".lean")) if m in graph.bit]
    times = module_times([f for g in args.logs for f in sorted(glob.glob(g))])
    target = args.target
    if target and target not in graph.bit:
        parser.error(f"unknown module {target}")
    print(f"files {len(diff)}, hunks {sum(diff.values())}, Lean modules {len(changed)}")
    for path, n in diff.items():
        print(f"  {n:4d} hunks  {path}")
    if not changed:
        return 0
    result = cost(graph, changed, times, target)
    print(f"rebuild set of a public-interface edit: {len(result['modules'])} modules")
    for name, mods in sorted(result["groups"].items()):
        secs = sum(times.get(m, 0.0) for m in mods)
        print(f"  {len(mods):5d}  {secs:8.0f} s  {name}")
        if args.list:
            for m in sorted(mods):
                print(f"         {times.get(m, 0):8.1f} s  {m}")
    above = graph.downstream_static(changed)
    if target:
        above &= graph.upstream([target])
    print(f"for comparison, importers through imports of every kind: {len(above) - len(changed)}")
    note = f" ({result['untimed']} modules without a time)" if result["untimed"] else ""
    print(f"check time {result['seconds']:.0f} s{note}")
    print(f"critical path {result['critical']:.0f} s over {len(result['chain'])} modules")
    for m in sorted(result["chain"], key=lambda n: -times.get(n, 0))[:5]:
        print(f"  {times.get(m, 0):8.1f} s  {m}")
    if args.upstream:
        up = graph.upstream(changed) - set(changed)
        secs = sum(times.get(m, 0.0) for m in up)
        print(f"upstream: {len(up)} modules, {secs:.0f} s")
        kernels = {m.split(".")[1] for m in changed if m.startswith("Kernels.")}
        for name, n in sorted(collections.Counter(group(m, kernels) for m in up).items()):
            print(f"  {n:5d}  {name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
