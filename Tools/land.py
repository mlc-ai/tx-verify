# SPDX-License-Identifier: Apache-2.0
"""Land one lane's commit on the current branch (run in the integration worktree).

    Tools/land.py <40-hex commit> [--tree K] --lane L [--no-build]

Refuses anything but a full 40-hex commit id. Then, one line per step:

1. the commit's changed paths against the merge base lie in the lane's paths (tree.json "lanes";
   without `--tree`, the lane's paths in any tree);
2. under `Lemmas/` the changes are additions only (rule 13);
3. `Core/`, any `Theorem.lean`, `Spec.lean`, `Assumptions*`, `lakefile.lean` are unchanged (rule 15);
4. no `sorry`, `native_decide` or `axiom` in the changed Lean files;
5. `git merge --no-ff --no-commit`, then the static tests (layers, modcost, unique names, premise
   count, iface); a failure aborts the merge.

Unless `--no-build`: every Lean module the commit adds or changes (`lean_modules`) and the tree's
top module (without `--tree`: every open tree's) are built through `Tools/build.sh`, `#print axioms`
of each built top theorem must print exactly `[propext, Classical.choice, Quot.sound]`, and the
whole pytest suite must pass. The merge is committed only if every step passed; otherwise it is aborted.
"""

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

import layers
import modcost
import trees

ROOT = trees.ROOT
HEX40 = re.compile(r"[0-9a-f]{40}")
FROZEN = re.compile(
    r"^(?:Core/.*|(?:.*/)?Theorem\.lean|(?:.*/)?Spec\.lean|(?:.*/)?Assumptions[^/]*(?:/.*)?"
    r"|lakefile\.lean)$"
)
FORBIDDEN = re.compile(
    r"(?<![\w.'])(sorry|native_decide)(?![\w'])"
    r"|^[ \t]*(?:@\[[^\]\n]*\][ \t]*)?(?:(?:private|public|protected|noncomputable|unsafe)\s+)*"
    r"(axiom)\s",
    re.M,
)
STATIC_TESTS = (
    "tests/test_layers.py",
    "tests/test_modcost.py",
    "tests/test_unique_names.py",
    "tests/test_premise_count.py",
    "tests/test_iface.py",
)
AXIOMS = "[propext, Classical.choice, Quot.sound]"


class Refused(Exception):
    pass


def run(args, root, check=False, **kw):
    return subprocess.run(args, cwd=root, capture_output=True, text=True, check=check, **kw)


def git(root, *args):
    out = run(["git", *args], root)
    if out.returncode:
        raise Refused(f"git {' '.join(args)}: {out.stderr.strip()}")
    return out.stdout


def check_id(commit):
    if not HEX40.fullmatch(commit or ""):
        raise Refused(f"not a full 40-hex commit id: {commit!r}")


def changes(root, commit):
    """`[(status, path)]` that merging the commit changes in HEAD (renames as D + A).

    It is the difference between HEAD and the merged tree, not the commit against one merge base:
    a lane that merged the integration branch has several merge bases with it, and a diff against
    one of them would show other lanes' landed files as the lane's own.
    """
    base = git(root, "merge-base", "HEAD", commit).strip()
    merged = run(["git", "merge-tree", "--write-tree", "HEAD", commit], root)
    if merged.returncode != 0:
        raise Refused(f"the merge has conflicts:\n{merged.stdout}")
    tree = merged.stdout.split()[0]
    out = []
    for line in git(root, "diff", "--name-status", "--no-renames", "HEAD", tree).splitlines():
        status, path = line.split("\t", 1)
        out.append((status[0], path))
    return base, out


def check_paths(ts, lane, changed):
    """Each changed path lies in the lane's paths of one of the trees `ts`."""
    if not any(lane in t.lanes for t in ts):
        where = ts[0].rel_config if len(ts) == 1 else "any tree.json"
        raise Refused(f"lane {lane} is not in {where}")
    outside = [p for _, p in changed if not any(lane in t.lanes_of(p) for t in ts)]
    if outside:
        raise Refused(f"outside lane {lane}'s paths: {', '.join(outside)}")


LEAN_ROOTS = ("Core/", "Lemmas/", "Tactics/", "Tests/", "Kernels/")


def lean_modules(changed, root=ROOT):
    """The Lean modules a commit adds or changes (not the deleted ones), sorted."""
    return sorted(
        trees.module_name(p, root)
        for s, p in changed
        if s != "D" and p.endswith(".lean") and p.startswith(LEAN_ROOTS)
    )


def build_targets(ts, changed, root=ROOT):
    """The changed modules and the top modules of the open trees among `ts`, and those trees."""
    tops = [t for t in ts if not t.closed]
    mods = lean_modules(changed, root)
    for t in tops:
        top = trees.module_name(t.root / t.top.get("correct", "Top/Correct.lean"), root)
        if top not in mods:
            mods.append(top)
        # every module of the tree, so a file outside Top.Correct's imports that a change
        # breaks is caught too (lake rebuilds only what the change affects)
        for p in sorted((root / t.root).rglob("*.lean")):
            name = trees.module_name(p.relative_to(root), root)
            if name not in mods:
                mods.append(name)
    return mods, tops


def on_main(path, root=ROOT):
    """Whether `path` exists on the main branch (`TXVERIFY_MAIN`, default `origin/main`)."""
    main = os.environ.get("TXVERIFY_MAIN", "origin/main")
    if run(["git", "rev-parse", "--verify", "--quiet", f"{main}^{{commit}}"], root).returncode:
        return True  # no main to compare with: every existing file counts as on main
    return run(["git", "cat-file", "-e", f"{main}:{path}"], root).returncode == 0


def check_lemmas(changed, root=ROOT):
    """Rule 13: a library file that is on main is not edited; files newer than main may change."""
    edited = [
        f"{s} {p}" for s, p in changed if p.startswith("Lemmas/") and s != "A" and on_main(p, root)
    ]
    if edited:
        raise Refused(f"Lemmas/ takes new files only (files on main): {', '.join(edited)}")


def check_frozen(changed):
    frozen = [p for _, p in changed if FROZEN.match(p)]
    if frozen:
        raise Refused(f"frozen files changed: {', '.join(frozen)}")


def check_forbidden(root, commit, changed):
    bad = []
    for status, path in changed:
        if status == "D" or not path.endswith(".lean"):
            continue
        text = git(root, "show", f"{commit}:{path}")
        for m in FORBIDDEN.finditer(code_only(text)):
            bad.append(f"{path}: {m[1] or m[2]}")
    if bad:
        raise Refused(f"forbidden: {', '.join(bad)}")


def code_only(text):
    """The Lean text with comments (nested, doc comments included) and string literals blanked;
    line breaks stay."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        two = text[i : i + 2]
        if depth:
            if two == "/-":
                depth, i = depth + 1, i + 2
            elif two == "-/":
                depth, i = depth - 1, i + 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif two == "/-":
            depth, i = 1, i + 2
        elif two == "--":
            while i < n and text[i] != "\n":
                i += 1
        elif text[i] == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
                out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def top_theorem(tree):
    """The full name of the top theorem: the namespace around it in the top file."""
    path = tree.root / tree.top.get("correct", "Top/Correct.lean")
    name = tree.top.get("theorem", "correct")
    ns = []
    for line in trees.strip_comments(path.read_text()).splitlines():
        if m := re.match(r"namespace (\S+)", line):
            ns.append(m[1])
        elif (m := re.match(r"end (\S+)", line)) and ns and ns[-1] == m[1]:
            ns.pop()
        elif re.match(rf"(?:\S+\s+)*theorem {re.escape(name)}\b", line):
            return ".".join([*ns, name])
    return ".".join([tree.namespace, name])


def step(name, ok, detail=""):
    print(f"land: {name}: {'ok' if ok else 'FAILED'}{' (' + detail + ')' if detail else ''}")
    return ok


def land(commit, kernel, lane, build=True, root=ROOT):
    """Returns the exit code; prints one line per step. `kernel` None: every tree."""
    try:
        check_id(commit)
        ts = trees.load([kernel] if kernel else None, root)
        git(root, "cat-file", "-e", f"{commit}^{{commit}}")
        base, changed = changes(root, commit)
        step("changed files", True, f"{len(changed)} against {base[:12]}")
        check_paths(ts, lane, changed)
        step(f"paths in lane {lane}", True)
        check_lemmas(changed, root)
        step("Lemmas/ additions only", True)
        check_frozen(changed)
        step("frozen files unchanged", True)
        check_forbidden(root, commit, changed)
        step("no sorry, native_decide, axiom", True)
    except Refused as e:
        print(f"land: refused: {e}")
        return 1
    if run(["git", "status", "--porcelain", "--untracked-files=no"], root).stdout.strip():
        print("land: refused: the worktree has uncommitted changes")
        return 1
    merge = run(["git", "merge", "--no-ff", "--no-commit", commit], root)
    if not step("merge", merge.returncode == 0):
        print(merge.stdout + merge.stderr)
        return abort(root)
    # The ceilings and the premise count may not rise above the branch's own tree.json.
    head = git(root, "rev-parse", "HEAD").strip()
    env = {**os.environ, "TXVERIFY_BASE": head}
    tests = run([sys.executable, "-m", "pytest", "-q", *STATIC_TESTS], root, env=env)
    if not step("static tests", tests.returncode == 0, last_line(tests.stdout)):
        print(tests.stdout[-4000:])
        return abort(root)
    lines_before = {t.kernel: line_table(root, t.kernel, "HEAD") for t in ts}
    if build:
        mods, tops = build_targets(ts, changed, root)
        b = run([str(root / "Tools/build.sh"), *mods], root)
        if not step(f"build {len(mods)} modules", b.returncode == 0, last_line(b.stdout)):
            print(b.stdout[-4000:] + b.stderr[-2000:])
            return abort(root)
        for t in tops:
            module = trees.module_name(t.root / t.top.get("correct", "Top/Correct.lean"), root)
            ok, printed = axioms(root, module, top_theorem(t))
            if not step(f"axioms {t.kernel}", ok, printed):
                return abort(root)
        suite = run([sys.executable, "-m", "pytest", "-q", "tests"], root, env=env)
        if not step("pytest", suite.returncode == 0, last_line(suite.stdout)):
            print(suite.stdout[-4000:])
            return abort(root)
    for t in ts:
        lower_ceilings(root, t)
        report_lines(t, lines_before[t.kernel], line_table(root, t.kernel))
    if kernel:
        message = f"chore(kernel): land {ts[0].kernel} lane {lane} {commit}"
    else:
        message = f"chore(infra): land lane {lane} {commit}"
    done = run(["git", "commit", "-m", message], root)
    if not step("commit", done.returncode == 0, last_line(done.stdout)):
        print(done.stdout + done.stderr)
        return abort(root)
    return 0


def line_table(root, kernel, rev=None):
    """`{handwritten-lines counter: n}` of a tree in the worktree, or at `rev` (a scratch
    worktree is not needed: the counts are read from `git show` of the tree's files)."""
    if rev is None:
        t = trees.load([kernel], root)[0]
        return {k: v for k, v in modcost.line_counters(t, t.files()).items()}
    t = trees.load([kernel], root)[0]
    out = {"handwritten lines": 0}
    rel = t.rel_root
    listing = git(root, "ls-tree", "-r", "--name-only", rev, "--", rel).splitlines()
    for path in listing:
        if not path.endswith(".lean") or t.is_generated(root / path):
            continue
        text = git(root, "show", f"{rev}:{path}")
        n = len(text.splitlines())
        key = f"handwritten lines {modcost.line_key(t, root / path)}"
        out["handwritten lines"] += n
        out[key] = out.get(key, 0) + n
    return out


def lower_ceilings(root, tree):
    """Lower the tree's ceilings to the merged counts (they never rise) and stage tree.json. A tree
    with `"lower_lines": false` keeps its line ceilings (budgets of a tree that still grows)."""
    t = trees.load([tree.kernel], root)[0]
    now = modcost.counters(t)
    if not t.cfg.get("lower_lines", True):
        # a tree that still grows keeps its line budgets; only the other counters fall
        now = {k: v for k, v in now.items() if not k.startswith("handwritten lines")}
    t.lower_ceilings(now)
    t = trees.load([tree.kernel], root)[0]
    t.lower_ceilings({k: len(v) for k, v in layers.counters(t).items()})
    git(root, "add", t.rel_config)


def report_lines(tree, before, after):
    """One line per directory whose handwritten lines changed, and the total."""
    t = trees.load([tree.kernel], tree.repo)[0]
    keys = sorted(set(before) | set(after), key=lambda k: (k != "handwritten lines", k))
    for k in keys:
        a, b = before.get(k, 0), after.get(k, 0)
        if a != b or k == "handwritten lines":
            name = k.removeprefix("handwritten lines").strip() or "total"
            print(f"land: lines {t.kernel} {name}: {a} -> {b} ({b - a:+d}; ceiling {t.ceiling(k)})")


def axioms(root, module, theorem):
    """Whether `#print axioms theorem` prints exactly the three standard axioms, and its text."""
    scratch = root / ".lake/own"
    scratch.mkdir(parents=True, exist_ok=True)
    path = scratch / "LandAxioms.lean"
    path.write_text(f"import {module}\n\n#print axioms {theorem}\n")
    env_path = str(Path.home() / ".elan/bin")
    env = {**os.environ, "PATH": env_path + os.pathsep + os.environ.get("PATH", "")}
    out = run(["lake", "env", "lean", str(path)], root, env=env)
    text = " ".join((out.stdout + out.stderr).split())
    expected = f"'{theorem}' depends on axioms: {AXIOMS}"
    return out.returncode == 0 and text == expected, text[:300]


def last_line(text):
    lines = [x for x in text.strip().splitlines() if x.strip()]
    return lines[-1][:200] if lines else ""


def abort(root):
    run(["git", "merge", "--abort"], root)
    print("land: merge aborted")
    return 1


def main(argv=None):
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("commit")
    ap.add_argument("--tree", metavar="K", help="the kernel's tree (default: every tree)")
    ap.add_argument("--lane", required=True, metavar="L")
    ap.add_argument("--no-build", action="store_true")
    args = ap.parse_args(argv)
    return land(args.commit, args.tree, args.lane, not args.no_build)


if __name__ == "__main__":
    # one landing at a time in a worktree: a second call waits for the first
    import fcntl

    (ROOT / ".lake").mkdir(exist_ok=True)
    with open(ROOT / ".lake" / "land.lock", "a") as _lk:
        fcntl.flock(_lk, fcntl.LOCK_EX)
        sys.exit(main())
