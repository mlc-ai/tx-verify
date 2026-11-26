#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Check that no Lean file of a proof tree is slower than its ceiling.

A file of a tree takes at most the tree's `check_limit` seconds (`tree.json`, default 60) unless
`Kernels/<K>/check_times.json` lists it with a larger ceiling; generated files are not checked.
The times come from the Lake logs that `Tools/build.sh` writes (`.lake/build-logs/*.log`). A log
counts for a file only if it built the file's current text: `build.sh` records the SHA-1 of each
source before and after the build and the machine's load (`<log>.hashes.json`); a log without
hashes counts if it is newer than the file.

A time taken on a loaded machine says nothing. A log is evidence only if it is quiet: it records
its load, and the larger of the 1-minute load averages at its start and end is at most
`TXVERIFY_QUIET_LOAD` (default QUIET times the number of cores). A file FAILS when it is over
SLACK times its ceiling in the newest quiet log of its current text. A file over it in loaded logs
only is `deferred`: listed, exit code 0. `--confirm` measures the deferred files again, alone (their
`.trace` removed, rebuilt through `Tools/build.sh`), if the machine is quiet now, and refuses
otherwise. `--require-quiet` (before a PR) fails unless every file has a quiet measurement of its
current text. The ceilings only go down: `--lower` lowers them to the newest times and drops the
files that are within the limit.

    Tools/check_times.py [--tree K]                   # failed and deferred files
    Tools/check_times.py [--tree K] --deferred        # the deferred files only
    Tools/check_times.py [--tree K] --confirm         # re-measure the deferred ones, if quiet
    Tools/check_times.py [--tree K] --require-quiet   # every file measured quietly, none over
    Tools/check_times.py [--tree K] --lower           # lower the ceilings to the newest times
    Tools/check_times.py --record-start LOG           # build.sh: hashes and load before a build
    Tools/check_times.py --record LOG                 # build.sh: hashes and load after it
"""

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

import trees

ROOT = trees.ROOT
LOGS = ROOT / ".lake/build-logs"
SLACK = 1.5
QUIET = 0.15
BUILT = re.compile(r"Built (\S+) \(([0-9.]+)(ms|s|m)\)")
UNIT = {"ms": 0.001, "s": 1.0, "m": 60.0}
HASHED = ("Core", "Lemmas", "Tactics", "Tests", "Kernels")


def load_now():
    return {"load": os.getloadavg()[0], "cores": os.cpu_count() or 1}


def quiet_limit(cores):
    env = os.environ.get("TXVERIFY_QUIET_LOAD")
    return float(env) if env else QUIET * cores


def is_quiet(load):
    """Whether a log's load record (`{"start", "end", "cores"}`) is quiet; no record is not."""
    if not load or not {"start", "end", "cores"} <= set(load):
        return False
    return max(load["start"], load["end"]) <= quiet_limit(load["cores"])


def table_path(tree):
    return tree.kernel_dir / "check_times.json"


def ceilings(tree):
    path = table_path(tree)
    return json.loads(path.read_text()) if path.exists() else {}


def sha1(path):
    return hashlib.sha1(path.read_bytes()).hexdigest()


def built(log):
    """`[(module, seconds)]` of a Lake log."""
    text = Path(log).read_text(errors="ignore")
    return [(m, float(v) * UNIT[u]) for m, v, u in BUILT.findall(text)]


def hashes_path(log):
    return Path(str(log) + ".hashes.json")


def record_start(log, root=ROOT):
    """Write the SHA-1 of every Lean source and the load before a build (`<log>.pre.json`)."""
    out = {}
    for top in HASHED:
        for path in (root / top).rglob("*.lean"):
            out[trees.module_name(path, root)] = sha1(path)
    start = load_now()
    pre = {"hashes": out, "load": {"start": start["load"], "cores": start["cores"]}}
    Path(str(log) + ".pre.json").write_text(json.dumps(pre))


def record(log, root=ROOT):
    """Write `{"load": {start, end, cores}, "hashes": {module: SHA-1}}` (`<log>.hashes.json`):
    the hash of each module the log built whose source did not change during the build."""
    pre_path = Path(str(log) + ".pre.json")
    pre = json.loads(pre_path.read_text()) if pre_path.exists() else {}
    before = pre.get("hashes", {})
    out = {}
    for module, _ in built(log):
        path = trees.module_path(module, root)
        if path.exists() and (h := sha1(path)) == before.get(module, h):
            out[module] = h
    end = load_now()
    load = {**pre.get("load", {}), "end": end["load"], "cores": end["cores"]}
    data = {"load": load if "start" in load else None, "hashes": out}
    hashes_path(log).write_text(json.dumps(data, indent=0, sort_keys=True))
    if pre_path.exists():
        pre_path.unlink()


def read_record(log):
    """`(hashes or None, load or None)` of a log's record; an old record is hashes only."""
    path = hashes_path(log)
    if not path.exists():
        return None, None
    data = json.loads(path.read_text())
    if "hashes" in data and isinstance(data["hashes"], dict):
        return data["hashes"], data.get("load")
    return data, None


def current_times(logs, modules=None, root=ROOT):
    """`{module: [(seconds, quiet), ...]}`, newest log first, of the logs that built the module's
    current text (only `modules` if given)."""
    logs = sorted((Path(p) for p in logs), key=lambda p: p.stat().st_mtime, reverse=True)
    out, digest = {}, {}
    for log in logs:
        when = log.stat().st_mtime
        recorded, load = read_record(log)
        quiet = is_quiet(load)
        for module, t in built(log):
            if modules is not None and module not in modules:
                continue
            path = trees.module_path(module, root)
            if not path.exists():
                continue
            if recorded is not None:
                if module not in recorded:
                    continue
                if module not in digest:
                    digest[module] = sha1(path)
                if recorded[module] != digest[module]:
                    continue
            elif path.stat().st_mtime >= when:
                continue
            out.setdefault(module, []).append((t, quiet))
    return out


def log_files(logs=LOGS):
    """The Lake logs, without the `latest.log` link."""
    return [p for p in Path(logs).glob("*.log") if not p.is_symlink()]


def limit(tree, table, module):
    return max(tree.check_limit, table.get(module, 0.0))


def checked(tree, module):
    path = trees.module_path(module, tree.repo)
    return module.startswith(tree.module_prefix) and not tree.is_generated(path)


def verdict(tree, times, table, slack=SLACK):
    """`(failed, deferred)`: `{module: (seconds, ceiling)}` over SLACK times the ceiling in the
    newest quiet log of its current text, and the ones without a quiet log that are over it in a
    loaded one."""
    failed, deferred = {}, {}
    for module, ts in times.items():
        if not checked(tree, module):
            continue
        ceiling = limit(tree, table, module)
        quiet = [t for t, q in ts if q]
        if quiet:
            if quiet[0] > slack * ceiling:
                failed[module] = (quiet[0], ceiling)
        elif any(t > slack * ceiling for t, _ in ts):
            deferred[module] = (max(t for t, _ in ts), ceiling)
    return failed, deferred


def unmeasured(tree, times):
    """The checked modules of the tree without a quiet measurement of their current text."""
    out = []
    for path in tree.files():
        module = trees.module_name(path, tree.repo)
        if not any(q for _, q in times.get(module, [])):
            out.append(module)
    return out


def lowered(tree, times, table):
    """The ceilings lowered to the newest times; a file within the limit is dropped."""
    new = {m: min(c, times[m][0][0] if times.get(m) else c) for m, c in table.items()}
    return {m: round(c, 1) for m, c in sorted(new.items()) if c > tree.check_limit}


def trace_path(module, root=ROOT):
    return root / ".lake/build/lib/lean" / (module.replace(".", "/") + ".trace")


def confirm(modules, root=ROOT):
    """Rebuild `modules` alone through `Tools/build.sh` (their traces removed); the new log is
    recorded with its load. None, without building, if the machine is not quiet now."""
    now = load_now()
    if now["load"] > quiet_limit(now["cores"]):
        return None
    for m in modules:
        trace = trace_path(m, root)
        if trace.exists():
            trace.unlink()
    log = LOGS / f"confirm-{'-'.join(sorted(m.rsplit('.', 1)[-1] for m in modules))[:80]}.log"
    env = {**os.environ, "TXVERIFY_BUILD_LOG": str(log)}
    subprocess.run([str(root / "Tools/build.sh"), *sorted(modules)], env=env, cwd=root)
    return log


def main(argv=None):
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    trees.add_tree_argument(parser)
    parser.add_argument("--lower", "--write", action="store_true", dest="lower")
    parser.add_argument("--confirm", action="store_true", help="re-measure the deferred, if quiet")
    parser.add_argument("--deferred", action="store_true", help="list the deferred files only")
    parser.add_argument("--require-quiet", action="store_true", help="every file measured quietly")
    parser.add_argument("--record-start", metavar="LOG")
    parser.add_argument("--record", metavar="LOG")
    parser.add_argument("--slack", type=float, default=SLACK)
    args = parser.parse_args(argv)
    if args.record_start:
        record_start(args.record_start)
        return 0
    if args.record:
        record(args.record)
        return 0
    rc = 0
    for tree in trees.load(args.tree):
        table = ceilings(tree)
        times = current_times(log_files())
        if args.lower:
            table_path(tree).write_text(json.dumps(lowered(tree, times, table), indent=1) + "\n")
            continue
        failed, deferred = verdict(tree, times, table, args.slack)
        if args.confirm and deferred:
            if confirm(set(deferred)) is None:
                now = load_now()
                print(
                    f"{tree.kernel}: not measuring: load {now['load']:.1f} is above "
                    f"{quiet_limit(now['cores']):.1f} ({now['cores']} cores)"
                )
            else:
                times = current_times(log_files())
                failed, deferred = verdict(tree, times, table, args.slack)
        for module, (t, c) in sorted(deferred.items()):
            print(f"{tree.kernel}: deferred {module}: {t:.0f} s loaded only, ceiling {c:.0f} s")
        if args.deferred:
            continue
        for module, (t, c) in sorted(failed.items(), key=lambda x: -x[1][0]):
            print(
                f"{tree.kernel}: FAIL {module}: {t:.0f} s quiet, ceiling {c:.0f} s", file=sys.stderr
            )
        rc |= bool(failed)
        if args.require_quiet:
            missing = unmeasured(tree, times)
            for module in missing:
                print(f"{tree.kernel}: no quiet measurement of {module}", file=sys.stderr)
            if missing:
                print(f"{tree.kernel}: {len(missing)} files without a quiet measurement")
            rc |= bool(missing)
    return rc


if __name__ == "__main__":
    sys.exit(main())
