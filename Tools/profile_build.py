# SPDX-License-Identifier: Apache-2.0
"""Measure a coherent project-only cold Lake build, preserving package artifacts."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def processes():
    result = {}
    for folder in Path("/proc").iterdir():
        if not folder.name.isdigit():
            continue
        try:
            fields = (folder / "stat").read_text().rsplit(") ", 1)[1].split()
            parent = int(fields[1])
            rss = int(fields[21]) * os.sysconf("SC_PAGE_SIZE")
            result[int(folder.name)] = (parent, rss, folder)
        except (OSError, ValueError, IndexError):
            continue
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--clean", action="store_true")
    args = parser.parse_args()
    if args.clean:
        shutil.rmtree(ROOT / ".lake/build", ignore_errors=True)
    sources = {}
    for folder in ["Core", "Lemmas", "Tactics", "Tests", "Kernels"]:
        for path in sorted((ROOT / folder).rglob("*.lean")):
            sources[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
    source_digest = hashlib.sha256(json.dumps(sources, sort_keys=True).encode()).hexdigest()
    started = time.monotonic()
    seen = {}
    peak_tree = 0
    with args.log.open("w") as log:
        process = subprocess.Popen(["lake", "--wfail", "build"], cwd=ROOT, stdout=log, stderr=log)
        while process.poll() is None:
            now = time.monotonic()
            ps = processes()
            descendants = {process.pid}
            while True:
                added = {pid for pid, (parent, _, _) in ps.items() if parent in descendants}
                new = descendants | added
                if new == descendants:
                    break
                descendants = new
            peak_tree = max(peak_tree, sum(ps[pid][1] for pid in descendants if pid in ps))
            for pid in descendants:
                if pid not in ps:
                    continue
                _, rss, folder = ps[pid]
                if pid not in seen:
                    try:
                        cmd = (folder / "cmdline").read_bytes().decode().split("\0")
                    except OSError:
                        continue
                    source = next((a for a in cmd if a.endswith(".lean")), None)
                    seen[pid] = {
                        "source": source,
                        "first_seen_s": now - started,
                        "last_seen_s": now - started,
                        "peak_rss_bytes": rss,
                    }
                else:
                    seen[pid]["last_seen_s"] = now - started
                    seen[pid]["peak_rss_bytes"] = max(rss, seen[pid]["peak_rss_bytes"])
            time.sleep(0.2)
    modules = []
    for row in seen.values():
        if row["source"]:
            row["elapsed_s"] = row["last_seen_s"] - row["first_seen_s"]
            modules.append(row)
    report = {
        "command": ["lake", "--wfail", "build"],
        "project_artifacts_cleaned": args.clean,
        "dependency_artifacts_preserved": True,
        "returncode": process.returncode,
        "wall_s": time.monotonic() - started,
        "peak_process_tree_rss_bytes": peak_tree,
        "sampling_interval_s": 0.2,
        "source_manifest_sha256": source_digest,
        "modules": sorted(modules, key=lambda r: r["elapsed_s"], reverse=True),
    }
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "modules"}, indent=2))
    raise SystemExit(process.returncode)


if __name__ == "__main__":
    main()
