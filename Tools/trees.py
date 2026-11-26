# SPDX-License-Identifier: Apache-2.0
"""The proof trees of the kernels, as `Kernels/<K>/tree.json` describes them.

    Tools/trees.py [--tree K ...]       # each tree: root, handwritten lines per directory
    Tools/trees.py --report [--json]    # per directory: lines, per instruction, Export/, budget,
                                        # generated lines; files over 60 s (newest build log)
                                        # and over 500 lines

A tree is the layered proof of one kernel (`root`). Its `tree.json` names the role directories
and what each may import, the common, lower, upper and generated directories, the names that are
state, the top theorem, the ceilings of every counter, the premise ledger, the cross-lane
predicates and the paths of each lane. The tools under `Tools/` read it through this module; every
tool takes `--tree K` (default: every tree).

The ceilings only fall. The merge base of `HEAD` with `origin/main` (`TXVERIFY_BASE` names another
ref) holds the older `tree.json` that the tests compare with; a tree absent there has no bound.
"""

import argparse
import functools
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE_REF = "origin/main"
REPO_PREFIXES = ("Lemmas/", "Tools/", "tests/", "Tests/", "Kernels/")
COMMENT = re.compile(r"/-.*?-/|--[^\n]*", re.S)

# Defaults of the optional keys (the ones the schema leaves out).
DEFAULT_ROLE_INVARIANTS = [r"\b(?:stateInv|roleInv|countInv)\b", r"\bRef[A-Z]\w*"]
DEFAULT_ROLE_MATCH = [r"\b(?:cases|rcases|match)\b[^\n]*\brole\b", r"\bRole\.(?:rec|casesOn)\b"]
DEFAULT_CHECK_LIMIT = 60.0
DIR_LINES = "handwritten lines "


def module_name(path, root=ROOT):
    """`Kernels/K/A/B.lean` (absolute or relative to the repository) -> `Kernels.K.A.B`."""
    path = Path(path)
    if path.is_absolute():
        path = path.relative_to(root)
    return ".".join(path.with_suffix("").parts)


def module_path(name, root=ROOT):
    """`Kernels.K.A.B` -> the absolute path of its file."""
    return root / (name.replace(".", "/") + ".lean")


def strip_comments(text):
    """The text without comments; a removed block comment leaves its line breaks."""
    return COMMENT.sub(lambda m: "\n" * m[0].count("\n"), text)


def git(*args, root=ROOT, check=True):
    out = subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=True)
    if check and out.returncode:
        raise RuntimeError(f"git {' '.join(args)}: {out.stderr.strip()}")
    return out.stdout if out.returncode == 0 else None


@functools.lru_cache(maxsize=None)
def merge_base(root=ROOT, ref=None):
    """The merge base of `HEAD` with `ref` (default `TXVERIFY_BASE` or `origin/main`), or None."""
    ref = ref or os.environ.get("TXVERIFY_BASE") or BASE_REF
    out = git("merge-base", "HEAD", ref, root=root, check=False)
    return out.strip() if out else None


def show_json(rev, path, root=ROOT):
    """The JSON file `path` (relative to the repository) at `rev`, or None if absent."""
    if rev is None:
        return None
    out = git("show", f"{rev}:{path}", root=root, check=False)
    return json.loads(out) if out is not None else None


class Tree:
    """One kernel's tree: its configuration and the questions the tools ask about its paths."""

    def __init__(self, config_path, repo=ROOT):
        self.repo = Path(repo)
        self.config_path = Path(config_path)
        self.cfg = json.loads(self.config_path.read_text())
        self.kernel = self.cfg["kernel"]
        self.kernel_dir = self.config_path.parent
        self.rel_root = self.cfg["root"].rstrip("/")
        self.root = self.repo / self.rel_root
        self.module_prefix = self.rel_root.replace("/", ".") + "."
        self.namespace = self.cfg.get("namespace", "")
        self.roles = self.cfg.get("roles", {})
        self.common = self.cfg.get("common", "Common")
        self.lower = list(self.cfg.get("lower", []))
        self.upper = list(self.cfg.get("upper", []))
        self.generated = list(self.cfg.get("generated", []))
        self.old_roots = [r.rstrip("/") for r in self.cfg.get("old_roots", [])]
        self.state_names = [re.compile(p) for p in self.cfg.get("state_names", [])]
        self.role_invariants = [
            re.compile(p) for p in self.cfg.get("role_invariants", DEFAULT_ROLE_INVARIANTS)
        ]
        self.role_match = [re.compile(p) for p in self.cfg.get("role_match", DEFAULT_ROLE_MATCH)]
        self.top = self.cfg.get("top", {})
        self.closed = bool(self.cfg.get("closed", False))
        self.lanes = self.cfg.get("lanes", {})
        self.iface = self.cfg.get("iface", {})
        self.premises = self.cfg.get("premises", {})
        self.ceilings = self.cfg.get("ceilings", {})
        self.check_limit = float(self.cfg.get("check_limit", DEFAULT_CHECK_LIMIT))

    def __repr__(self):
        return f"Tree({self.kernel})"

    @property
    def rel_config(self):
        return self.config_path.relative_to(self.repo).as_posix()

    # Paths.

    def parts(self, path):
        """The parts of `path` below the root, or None outside it."""
        path = Path(path)
        if not path.is_absolute():
            path = self.repo / path
        try:
            return path.relative_to(self.root).parts
        except ValueError:
            return None

    def is_generated(self, path):
        """Under a generated directory: a name of `generated` at any depth below the root or the
        kernel directory, or a path of it relative to the root."""
        path = Path(path)
        if not path.is_absolute():
            path = self.repo / path
        for base in (self.root, self.kernel_dir):
            try:
                rel = path.relative_to(base)
            except ValueError:
                continue
            for g in self.generated:
                if "/" in g.strip("/"):
                    if base == self.root and rel.as_posix().startswith(g.strip("/") + "/"):
                        return True
                elif g in rel.parts[:-1]:
                    return True
        return False

    def files(self, generated=False):
        """The Lean files of the tree, sorted; without the generated ones unless asked."""
        out = sorted(self.root.rglob("*.lean"))
        return out if generated else [p for p in out if not self.is_generated(p)]

    def role_of(self, path):
        """The place of a path in the layers: `("role", R)`, `("common", C)`, `("lower", D)`,
        `("upper", D)`, `("other", first part)`, or None outside the tree."""
        parts = self.parts(path)
        if not parts:
            return None
        top = parts[0].removesuffix(".lean") if len(parts) == 1 else parts[0]
        if len(parts) > 1 and top in self.roles:
            return ("role", top)
        if top == self.common and len(parts) > 1:
            return ("common", top)
        if top in self.lower:
            return ("lower", top)
        if top in self.upper:
            return ("upper", top)
        return ("other", top)

    def is_export(self, path):
        parts = self.parts(path) or ()
        return "Export" in parts[1:-1]

    def is_role_internal(self, path):
        """In a role directory and not under its `Export/`."""
        role = self.role_of(path)
        return bool(role) and role[0] == "role" and not self.is_export(path)

    def module_role(self, module):
        return self.role_of(module_path(module, self.repo))

    def lane_prefixes(self, lane):
        """The repository-relative path prefixes of a lane."""
        out = []
        for p in self.lanes.get(lane, []):
            out.append(p if p.startswith(REPO_PREFIXES) else f"{self.rel_root}/{p}")
        return out

    def lanes_of(self, rel_path):
        """The lanes whose paths contain `rel_path` (relative to the repository)."""
        rel_path = Path(rel_path).as_posix()
        return [
            lane
            for lane in self.lanes
            if any(in_prefix(rel_path, p) for p in self.lane_prefixes(lane))
        ]

    def handwritten_lines(self):
        """`{directory below the root: lines}` of the non-generated Lean files ("." for files at
        the root)."""
        out = {}
        for path in self.files():
            parts = path.relative_to(self.root).parts
            key = parts[0] if len(parts) > 1 else "."
            out[key] = out.get(key, 0) + len(path.read_text(errors="replace").splitlines())
        return dict(sorted(out.items()))

    def generated_lines(self):
        """`{directory: lines}` of the generated Lean files: below the root by their first
        directory (a role's `Gen/` counts for the role), and the kernel directory's generated
        directories outside the root as `kernel <name>`."""
        out = {}
        for path in self.files(generated=True):
            if not self.is_generated(path):
                continue
            parts = path.relative_to(self.root).parts
            key = parts[0] if len(parts) > 1 else "."
            out[key] = out.get(key, 0) + len(path.read_text(errors="replace").splitlines())
        for g in self.generated:
            base = self.kernel_dir / g.strip("/")
            if "/" in g.strip("/") or not base.is_dir() or base.is_relative_to(self.root):
                continue
            n = sum(len(p.read_text(errors="replace").splitlines()) for p in base.rglob("*.lean"))
            if n:
                out[f"kernel {g}"] = n
        return dict(sorted(out.items()))

    def lean_files_all(self):
        """Every Lean file of the tree, generated ones and the kernel's generated directories
        outside the root included."""
        out = set(self.files(generated=True))
        for g in self.generated:
            base = self.kernel_dir / g.strip("/")
            if "/" not in g.strip("/") and base.is_dir():
                out |= set(base.rglob("*.lean"))
        return sorted(out)

    # The older tree.json and the ceilings.

    def base_config(self):
        """The `tree.json` of this kernel at the merge base, or None."""
        return show_json(merge_base(self.repo), self.rel_config, self.repo)

    def ceiling(self, name):
        """The ceiling of a counter; a counter without one has ceiling 0."""
        return self.ceilings.get(name, 0)

    def ceiling_violations(self, measured):
        """Measured values above their ceilings, and ceilings above the merge base's."""
        out = [
            f"{self.kernel}: {name} = {n} above its ceiling {self.ceiling(name)}"
            for name, n in measured.items()
            if n > self.ceiling(name)
        ]
        base = self.base_config()
        old = (base or {}).get("ceilings", {})
        per_dir = lambda cs: {k: v for k, v in cs.items() if k.startswith(DIR_LINES)}  # noqa: E731
        # Directory line ceilings may be moved between directories: one may rise when the sum of
        # all directory line ceilings does not (and the total ceiling is checked as any other).
        moved = per_dir(old) and sum(per_dir(self.ceilings).values()) <= sum(per_dir(old).values())
        for name, c in self.ceilings.items():
            if name in old and c > old[name] and not (moved and name.startswith(DIR_LINES)):
                out.append(f"{self.kernel}: ceiling {name} raised from {old[name]} to {c}")
        if per_dir(old) and not moved:
            out.append(f"{self.kernel}: the directory line ceilings rose in sum")
        return out

    def lower_ceilings(self, measured):
        """Lower the ceilings in `tree.json` to the measured values; never raise one. Returns the
        `{name: (old, new)}` changed."""
        changed = {}
        for name, n in measured.items():
            if name in self.ceilings and n < self.ceilings[name]:
                changed[name] = (self.ceilings[name], n)
                self.ceilings[name] = n
        if changed:
            self.cfg["ceilings"] = self.ceilings
            self.config_path.write_text(json.dumps(self.cfg, indent=2, ensure_ascii=False) + "\n")
        return changed


def in_prefix(path, prefix):
    return path == prefix.rstrip("/") or path.startswith(prefix.rstrip("/") + "/")


def load(names=None, repo=ROOT):
    """The trees of `Kernels/*/tree.json`, sorted by kernel; only the named ones if `names`."""
    out = [Tree(p, repo) for p in sorted(Path(repo).glob("Kernels/*/tree.json"))]
    if names:
        wanted = set(names)
        found = [t for t in out if t.kernel in wanted or t.kernel_dir.name in wanted]
        missing = wanted - {t.kernel for t in found} - {t.kernel_dir.name for t in found}
        if missing:
            raise SystemExit(f"no tree.json for {', '.join(sorted(missing))}")
        out = found
    return out


def add_tree_argument(parser):
    parser.add_argument(
        "--tree",
        action="append",
        metavar="K",
        help="the kernel whose tree to measure (repeatable; default: every tree)",
    )


SITE_DECL = re.compile(r"^def (\w+) : RoleDecl :=\s*⟨\[([^\]]*)\]", re.M)
INTERVAL = re.compile(r"\((\d+),\s*(\d+)\)")


def role_instructions(tree):
    """`{role: instructions}`: tree.json `role_instructions`, else the regions of the role's
    declarations in `<root>/<common>/Sites.lean` (`def <name> : RoleDecl := ⟨[(a, b), …], …⟩`,
    a declaration belongs to the role whose name, lowercased, starts it)."""
    if "role_instructions" in tree.cfg:
        return dict(tree.cfg["role_instructions"])
    path = tree.root / tree.common / "Sites.lean"
    out = {}
    if not path.exists():
        return out
    for name, regions in SITE_DECL.findall(strip_comments(path.read_text())):
        role = next((r for r in tree.roles if name.lower().startswith(r.lower())), None)
        if role is None:
            continue
        n = sum(int(b) - int(a) for a, b in INTERVAL.findall(regions))
        out[role] = out.get(role, 0) + n
    return out


def newest_log(repo=ROOT):
    """The newest Lake log of `Tools/build.sh` (`.lake/build-logs/*.log`), or None."""
    logs = [p for p in (Path(repo) / ".lake/build-logs").glob("*.log") if not p.is_symlink()]
    return max(logs, key=lambda p: (p.stat().st_mtime, p.name)) if logs else None


def build_stats(tree, log):
    """`(files over the check limit in the log, files over 500 lines)` of the tree, every Lean
    file of it counted (generated ones too); the first is None without a log."""
    files = tree.lean_files_all()
    over_lines = sum(1 for p in files if len(p.read_text(errors="replace").splitlines()) > 500)
    if log is None:
        return None, over_lines
    import check_times

    mods = {module_name(p, tree.repo) for p in files}
    times = {m: t for m, t in check_times.built(log) if m in mods}
    return sum(1 for t in times.values() if t > tree.check_limit), over_lines


def report(tree, log=None):
    """One row per directory of the tree (`modcost.line_key`: the first directory, the second one
    under `Protocol/` and `Top/`): handwritten lines, lines per instruction (a role's own
    instructions; the kernel's for the others), the share of `Export/` (roles), the line ceiling
    (`handwritten lines <dir>` in `ceilings`), and the open premises."""
    import modcost
    import premise_count

    counts = modcost.line_counters(tree, tree.files())
    lines = {
        k.removeprefix("handwritten lines "): n
        for k, n in counts.items()
        if k != "handwritten lines"
    }
    gen = tree.generated_lines()
    export = {}
    for path in tree.files():
        parts = tree.parts(path)
        if len(parts) > 2 and parts[0] in tree.roles and "Export" in parts[1:-1]:
            n = len(path.read_text(errors="replace").splitlines())
            export[parts[0]] = export.get(parts[0], 0) + n
    instr = role_instructions(tree)
    total_instr = tree.cfg.get("instructions") or 0
    ceiled = {
        k.removeprefix("handwritten lines "): v
        for k, v in tree.ceilings.items()
        if k.startswith("handwritten lines ")
    }
    rows = []
    for d in sorted(set(lines) | set(tree.roles) | set(ceiled) | set(gen)):
        n = lines.get(d, 0)
        row = {"tree": tree.kernel, "dir": d, "lines": n, "generated": gen.get(d, 0)}
        k = instr.get(d) if d in tree.roles else (None if d.startswith("kernel ") else total_instr)
        row["instructions"] = k or None
        row["per_instruction"] = round(n / k, 2) if k else None
        if d in tree.roles:
            row["export_share"] = round(export.get(d, 0) / n, 3) if n else 0.0
        if d in ceiled:
            row["ceiling"] = ceiled[d]
        rows.append(row)
    premises = None if tree.closed else len(premise_count.leaf_names(tree))
    over_time, over_lines = build_stats(tree, log)
    rows.append(
        {
            "tree": tree.kernel,
            "dir": "TOTAL",
            "lines": counts["handwritten lines"],
            "generated": sum(gen.values()),
            "over_time": over_time,
            "over_lines": over_lines,
            "log": log.name if log else None,
            "instructions": total_instr or None,
            "per_instruction": round(counts["handwritten lines"] / total_instr, 2)
            if total_instr
            else None,
            "ceiling": tree.ceilings.get("handwritten lines"),
            "open_premises": premises,
        }
    )
    return rows


def report_line(row):
    cols = [f"{row['tree']:<26}", f"{row['dir']:<18}", f"{row['lines']:>7}"]
    cols.append(f"gen {row.get('generated', 0):>6}")
    if row.get("per_instruction") is not None:
        cols.append(f"{row['per_instruction']:>7.2f}/instr ({row['instructions']})")
    if "export_share" in row:
        cols.append(f"export {100 * row['export_share']:.0f}%")
    if row.get("ceiling") is not None:
        cols.append(f"ceiling {row['lines']}/{row['ceiling']}")
    if row.get("open_premises") is not None:
        cols.append(f"open premises {row['open_premises']}")
    if "over_lines" in row:
        t = "?" if row["over_time"] is None else row["over_time"]
        cols.append(f"files >60s {t} >500 lines {row['over_lines']} ({row['log'] or 'no log'})")
    return "  ".join(cols)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    add_tree_argument(parser)
    parser.add_argument("--report", action="store_true", help="one line per directory")
    parser.add_argument("--json", action="store_true", help="with --report: JSON rows")
    parser.add_argument("--log", type=Path, help="with --report: this build log, not the newest")
    args = parser.parse_args(argv)
    if args.report:
        log = args.log or newest_log()
        rows = [row for tree in load(args.tree) for row in report(tree, log)]
        if args.json:
            print(json.dumps(rows, indent=1))
        else:
            for row in rows:
                print(report_line(row))
        return 0
    for tree in load(args.tree):
        lines = tree.handwritten_lines()
        total = sum(lines.values())
        state = "closed" if tree.closed else "open"
        print(f"{tree.kernel}: {tree.rel_root} ({state}), {total} handwritten lines", end="")
        if tree.cfg.get("instructions"):
            print(f", {total / tree.cfg['instructions']:.1f} per instruction", end="")
        print()
        for d, n in lines.items():
            print(f"  {n:7d}  {d}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
