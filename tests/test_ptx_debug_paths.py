# SPDX-License-Identifier: Apache-2.0
"""The frozen PTX of the Inkling kernel carries no machine-local path.

`ptxas` writes the compile-unit directory and file names into the debug sections as `.b8` bytes,
where a plain-text path check does not see them. A build is valid only through
`Kernels/InklingRelDecode/ptx-build/ns_run.sh`, which makes the sources appear under
`/tmp/inkling-decode-source`; every absolute path in the debug bytes must start with it.
"""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PTX = ROOT / "Kernels" / "InklingRelDecode" / "rel_verify_sm100a.ptx"
ALLOWED_ROOT = "/tmp/inkling-decode-source"


def _debug_strings(text):
    """Runs of at least four printable bytes written as consecutive `.b8 N` lines."""
    out, cur = [], []
    for line in text.split("\n"):
        m = re.match(r"^\.b8\s+(\d+)\b", line)
        if m and 32 <= int(m.group(1)) < 127:
            cur.append(int(m.group(1)))
            continue
        if len(cur) >= 4:
            out.append(bytes(cur).decode())
        cur = []
    return out


def test_inkling_ptx_has_no_local_path():
    text = PTX.read_text()
    paths = [s for s in _debug_strings(text) if s.startswith("/")]
    assert paths, "the debug sections of the build should name its source directory"
    bad = [p for p in paths if not p.startswith(ALLOWED_ROOT)]
    assert not bad, f"debug path outside {ALLOWED_ROOT}: {bad}"
    for root in ("home", "raid"):
        assert "/" + root + "/" not in text
