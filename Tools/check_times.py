#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Check that no Lean file of tml-fa4's Proof is slower than its ceiling.

A file takes at most LIMIT seconds unless `Tools/check_times.json` lists it with a larger ceiling.
The time of a file is the one of the newest Lake log that built it (`.lake/build-logs/*.log`, what
`Tools/build.sh` writes). A file over SLACK times its ceiling fails, so a loaded machine does not.
The ceilings only go down: `--write` lowers them and drops the files that are within LIMIT.

    Tools/check_times.py            # the files over their ceilings
    Tools/check_times.py --write    # lower the ceilings to the newest times
"""

import argparse
import json
import re
import statistics
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TABLE = ROOT / "Tools/check_times.json"
PREFIX = "Kernels.TmlFa4Fwd.Proof."
LIMIT, SLACK = 15.0, 2.0
BUILT = re.compile(r"Built (\S+) \(([0-9.]+)(ms|s)\)")


def newest_times(logs, root=ROOT):
    """`{module: seconds}` from the logs, the newest log of a module deciding. A log older than the
    module's file timed another text of it and does not count."""
    out = {}
    for log in sorted(logs, key=lambda p: p.stat().st_mtime):
        when = log.stat().st_mtime
        for module, value, unit in BUILT.findall(log.read_text(errors="ignore")):
            path = root / (module.replace(".", "/") + ".lean")
            if path.exists() and path.stat().st_mtime < when:
                out[module] = float(value) / (1000 if unit == "ms" else 1)
    return out


def load_factor(times, ceilings):
    """How much slower than its ceiling the median listed file was: the load of the machine."""
    ratios = [times[m] / c for m, c in ceilings.items() if m in times]
    return max(1.0, statistics.median(ratios)) if len(ratios) >= 20 else 1.0


def over(times, ceilings):
    """`{module: (seconds, ceiling)}` of the Proof files that are too slow, without the load."""
    out, load = {}, load_factor(times, ceilings)
    for module, t in times.items():
        if module.startswith(PREFIX) and ".Gen." not in module:
            ceiling = max(LIMIT, ceilings.get(module, 0))
            if t > SLACK * load * ceiling:
                out[module] = (t, ceiling)
    return out


def lowered(times, ceilings):
    """The ceilings, lowered to the times; a file within LIMIT is dropped."""
    new = {m: min(c, times.get(m, c)) for m, c in ceilings.items()}
    return {m: round(c, 1) for m, c in sorted(new.items()) if c > LIMIT}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    times = newest_times((ROOT / ".lake/build-logs").glob("*.log"))
    ceilings = json.loads(TABLE.read_text())
    if args.write:
        TABLE.write_text(json.dumps(lowered(times, ceilings), indent=1) + "\n")
        return 0
    slow = over(times, ceilings)
    for module, (t, ceiling) in sorted(slow.items(), key=lambda x: -x[1][0]):
        print(f"{module}: {t:.0f} s, ceiling {ceiling:.0f} s", file=sys.stderr)
    return 1 if slow else 0


if __name__ == "__main__":
    sys.exit(main())
