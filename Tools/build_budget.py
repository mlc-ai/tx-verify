# SPDX-License-Identifier: Apache-2.0
"""Per-module build time budget from Lake logs.

Reads ``Built <Module> (<time>)`` lines from one or more Lake logs (the minimum
observed time per module is used, so a log from a contended machine can be
combined with a clean one), computes the longest import chain weighted by build
time, and fails when one module exceeds the per-file budget.
"""

import argparse
import collections
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TIME = re.compile(r"Built (\S+) \(([\d.]+)(ms|s|m)\)")
IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(\S+)", re.M)


def module_times(logs):
    seen = collections.defaultdict(list)
    for log in logs:
        for name, value, unit in TIME.findall(Path(log).read_text(errors="replace")):
            scale = {"ms": 0.001, "s": 1.0, "m": 60.0}[unit]
            seen[name].append(float(value) * scale)
    return {name: min(values) for name, values in seen.items()}


def module_imports():
    graph = {}
    for top in ("Core", "Lemmas", "Tactics", "Tests", "Kernels"):
        for path in (ROOT / top).rglob("*.lean"):
            name = ".".join(path.relative_to(ROOT).with_suffix("").parts)
            graph[name] = IMPORT.findall(path.read_text(errors="replace"))
    return graph


def critical_path(times, graph):
    sys.setrecursionlimit(100000)
    memo, prev = {}, {}

    def cost(name):
        if name in memo:
            return memo[name]
        best, arg = 0.0, None
        for dep in graph.get(name, []):
            if dep in graph and cost(dep) > best:
                best, arg = cost(dep), dep
        memo[name] = best + times.get(name, 0.0)
        prev[name] = arg
        return memo[name]

    top = max(graph, key=cost)
    chain = []
    while top:
        chain.append(top)
        top = prev[top]
    return memo[chain[0]], chain


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("logs", nargs="+", type=Path)
    parser.add_argument("--max-file", type=float, default=60.0, help="per-module budget in seconds")
    parser.add_argument("--top", type=int, default=10)
    args = parser.parse_args()
    times = module_times(args.logs)
    if not times:
        print("no timings found")
        return 0
    graph = module_imports()
    total, chain = critical_path(times, graph)
    print(f"modules timed: {len(times)}; sum {sum(times.values()) / 60:.1f} cpu-min")
    print(f"critical path: {total / 60:.1f} min over {len(chain)} modules, ending at {chain[0]}")
    for name in sorted(chain, key=lambda n: -times.get(n, 0))[: args.top]:
        print(f"  chain {times.get(name, 0):7.1f}s  {name}")
    slow = sorted(times.items(), key=lambda kv: -kv[1])
    for name, value in slow[: args.top]:
        print(f"  file  {value:7.1f}s  {name}")
    over = [(n, v) for n, v in slow if v > args.max_file]
    if over:
        print(f"FAIL: {len(over)} module(s) over {args.max_file:.0f}s budget")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
