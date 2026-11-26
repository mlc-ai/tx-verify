# SPDX-License-Identifier: Apache-2.0
"""What a modification costs: files, hunks, modules rebuilt, check time, critical path.

    Tools/modcost.py FILE.lean [FILE ...]      # the files as edited in the working tree
    Tools/modcost.py --commit REV              # the Lean files a commit changes
    Tools/modcost.py --counters [--tree K] [--lower] [--list-counter NAME]
                                               # the counters of the trees (tree.json)

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

import trees
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


# The counters of a tree (`--counters`, `Kernels/<K>/tree.json`): positional projections, copied
# proof lines in zone A (Common, upper and `Export/` files, where there are none) and zone B (the
# rest), `maxHeartbeats` raises, files over MAX_LINES lines, and the tree's own `patterns`
# (`[name, directories under the root, regex, count occurrences rather than lines]`).
PROJECTION = re.compile(r"(?:\.2){3}")
HEARTBEATS = re.compile(r"^\s*set_option\s+maxHeartbeats\s+(\d+)")
DEFAULT_HEARTBEATS = 200000


def raises_heartbeats(line):
    """A `set_option maxHeartbeats n` with n above Lean's default or 0 (no limit)."""
    m = HEARTBEATS.match(line)
    return bool(m) and (int(m[1]) == 0 or int(m[1]) > DEFAULT_HEARTBEATS)


MAX_LINES = 500

# A block of this many proof lines (numbers normalised, at least BLOCK_CHARS characters) that occurs
# in two files is copied.
BLOCK, BLOCK_CHARS = 12, 250
SKIP_LINE = ("--", "import ", "public import ", "set_option ", "variable ", "open ")


def copied_lines(paths):
    """`{file: line numbers}` of the proof lines that another of `paths` repeats."""
    seen = {}
    for path in paths:
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


def zone_a(tree, path):
    """Common, upper and `Export/` files: no copied proof block at all."""
    return tree.role_of(path)[0] in ("common", "upper") or tree.is_export(path)


SPLIT_DIRS = ("Protocol", "Top")
GENERATED_HEADER = re.compile(r"\bGenerated by\b")


def line_key(tree, path):
    """The directory a file's lines count against: its first directory below the root, and the
    second one under `Protocol/` and `Top/` ("." for files at the root, `Top/.` for files
    directly in `Top/`)."""
    parts = path.relative_to(tree.root).parts
    if len(parts) == 1:
        return "."
    if parts[0] in SPLIT_DIRS:
        return f"{parts[0]}/{parts[1] if len(parts) > 2 else '.'}"
    return parts[0]


def line_counters(tree, files):
    """`handwritten lines` (the whole tree) and `handwritten lines <dir>` (see `line_key`)."""
    out = {"handwritten lines": 0}
    for path in files:
        n = len(path.read_text(encoding="utf-8").splitlines())
        out["handwritten lines"] += n
        key = f"handwritten lines {line_key(tree, path)}"
        out[key] = out.get(key, 0) + n
    return out


def misplaced_generated(files):
    """Files outside the generated directories whose header says a generator wrote them."""
    out = []
    for path in files:
        head = path.read_text(encoding="utf-8").splitlines()[:6]
        if any(GENERATED_HEADER.search(line) for line in head):
            out.append(path)
    return out


def top_module(tree):
    return trees.module_name(tree.root / tree.top.get("correct", "Top/Correct.lean"), tree.repo)


def unreachable(tree, files, graph=None):
    """The tree's handwritten modules that the top module does not import (transitively)."""
    graph = graph or Graph.from_tree(tree.repo)
    seen = graph.upstream([top_module(tree)])
    return [p for p in files if trees.module_name(p, tree.repo) not in seen]


def common_internal_imports(tree, files):
    """`(file, imported module)` for every import of a role-internal module from `Common/`."""
    out = []
    for path in files:
        role = tree.role_of(path)
        if not role or role[0] != "common":
            continue
        for line in path.read_text(encoding="utf-8").splitlines():
            m = IMPORT.match(line)
            if m and tree.is_role_internal(trees.module_path(m.group(4), tree.repo)):
                out.append((path, m.group(4)))
    return out


def counters(tree):
    """`{counter: number}` of one tree (`trees.Tree`), without its generated files."""
    files = tree.files()
    out = {"positional projections": 0, "maxHeartbeats raises": 0, "files over 500 lines": 0}
    out.update(line_counters(tree, files))
    out["generated files outside Gen"] = len(misplaced_generated(files))
    out["modules unreachable from the top"] = len(unreachable(tree, files))
    out["common imports of role internals"] = len(common_internal_imports(tree, files))
    for path in files:
        lines = path.read_text(encoding="utf-8").splitlines()
        out["positional projections"] += sum(len(PROJECTION.findall(line)) for line in lines)
        out["maxHeartbeats raises"] += sum(map(raises_heartbeats, lines))
        out["files over 500 lines"] += len(lines) > MAX_LINES
    copied = copied_lines(files)
    out["copied proof lines zone A"] = sum(len(v) for p, v in copied.items() if zone_a(tree, p))
    out["copied proof lines zone B"] = sum(len(v) for p, v in copied.items() if not zone_a(tree, p))
    for name, dirs, pattern, each in tree.cfg.get("patterns", []):
        rx, n = re.compile(pattern), 0
        for path in files:
            rel = path.relative_to(tree.root).as_posix()
            if not any(not d or rel.startswith(d.rstrip("/") + "/") for d in dirs):
                continue
            for line in path.read_text(encoding="utf-8").splitlines():
                n += len(rx.findall(line)) if each else bool(rx.search(line))
        out[name] = n
    return out


def counter_items(tree, name):
    """The `file:line` places of a counter (for `--list`)."""
    out = []
    if name.startswith("copied proof lines"):
        want = name.endswith("zone A")
        for p, numbers in sorted(copied_lines(tree.files()).items()):
            if zone_a(tree, p) == want:
                out += [f"{p.relative_to(tree.root)}:{i}" for i in sorted(numbers)]
        return out
    rel = lambda p: p.relative_to(tree.root).as_posix()  # noqa: E731
    if name == "generated files outside Gen":
        return [rel(p) for p in misplaced_generated(tree.files())]
    if name == "modules unreachable from the top":
        return [rel(p) for p in unreachable(tree, tree.files())]
    if name == "common imports of role internals":
        return [f"{rel(p)}: {m}" for p, m in common_internal_imports(tree, tree.files())]
    if name.startswith("handwritten lines"):
        lines = line_counters(tree, tree.files())
        return [f"{n:7d}  {k}" for k, n in sorted(lines.items()) if k.startswith(name)]
    test = {"positional projections": PROJECTION.search, "maxHeartbeats raises": raises_heartbeats}
    match = test.get(name)
    for pname, _, pattern, _ in tree.cfg.get("patterns", []):
        if pname == name:
            match = re.compile(pattern).search
    for path in tree.files():
        lines = path.read_text(encoding="utf-8").splitlines()
        if name == "files over 500 lines":
            if len(lines) > MAX_LINES:
                out.append(f"{path.relative_to(tree.root)}: {len(lines)} lines")
            continue
        out += [f"{path.relative_to(tree.root)}:{i}" for i, t in enumerate(lines, 1) if match(t)]
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
    parser.add_argument("--counters", action="store_true", help="the counters of the trees")
    trees.add_tree_argument(parser)
    parser.add_argument("--lower", action="store_true", help="with --counters: lower the ceilings")
    parser.add_argument("--list-counter", metavar="COUNTER", help="with --counters: the places")
    args = parser.parse_args(argv)
    if args.counters:
        over = 0
        for tree in trees.load(args.tree):
            if args.list_counter:
                print("\n".join(counter_items(tree, args.list_counter)))
                continue
            now = counters(tree)
            print(tree.kernel)
            for name, n in now.items():
                top = tree.ceiling(name)
                mark = "  ABOVE ITS CEILING" if isinstance(top, int) and n > top else ""
                over += bool(mark)
                print(f"{n:6d}  (ceiling {top:6})  {name}{mark}")
            if args.lower:
                for name, (a, b) in tree.lower_ceilings(now).items():
                    print(f"  lowered {name}: {a} -> {b}")
        return 1 if over else 0
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
