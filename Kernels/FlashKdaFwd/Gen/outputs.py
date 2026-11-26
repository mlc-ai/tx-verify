# SPDX-License-Identifier: Apache-2.0
"""Write the files a generator made, or check that the files on disk are those.

Every generator of this directory computes its outputs as texts and hands them to
`write_or_check`, so that all of them have the same two commands:

    python3 Kernels/FlashKdaFwd/Gen/<generator>.py            # write the outputs
    python3 Kernels/FlashKdaFwd/Gen/<generator>.py --check    # write nothing; fail if one is stale

`Kernels/FlashKdaFwd/regenerate.py` runs all of them in dependency order.
"""

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]


def write_or_check(files, check, previous=()):
    """Bring the files on disk to `files` (path -> text).

    `previous` lists generated files that are on disk now; one that `files` does not name is
    left over from an earlier run and is removed. With `check` nothing is written or removed:
    the paths that would be are printed as stale and the process exits with status 1.
    """
    wanted = {path: text.encode("utf-8") for path, text in files.items()}
    stale = [p for p, data in wanted.items() if not p.is_file() or p.read_bytes() != data]
    left = sorted(set(previous) - wanted.keys())
    if check:
        if stale or left:
            sys.exit("\n".join(f"stale: {p.relative_to(ROOT)}" for p in sorted([*stale, *left])))
        return
    for path in stale:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(wanted[path])
        print(f"wrote {path.relative_to(ROOT)}")
    for path in left:
        path.unlink()
        print(f"removed {path.relative_to(ROOT)}")
