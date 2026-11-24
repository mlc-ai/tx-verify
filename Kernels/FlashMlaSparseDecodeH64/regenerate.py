#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Regenerate the Lean files and flow table from the frozen FlashMLA PTX."""

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

KERNEL = Path(__file__).resolve().parent
ROOT = KERNEL.parents[1]
TOOLS = ROOT / "Tools"
MODULE = f"Kernels.{KERNEL.name}"
NAMESPACE = f"PTX.{MODULE}"
GENERATED = f"PTX.Generated.{KERNEL.name}"
PTX = KERNEL / "v41_h64_no_split_plain.ptx"

sys.path.insert(0, str(TOOLS))
from code_table import generate as generate_code  # noqa: E402
from decode_chunks import SOURCE_PARTS, Layout  # noqa: E402
from export_lean import export  # noqa: E402
from flow_gen import generate as generate_flow  # noqa: E402
from parse_ptx import parse  # noqa: E402


def emit(files, check, previous=()):
    stale = []
    for path, text in files.items():
        expected = text.encode("utf-8")
        if path.is_file() and path.read_bytes() == expected:
            continue
        if check:
            stale.append(path)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(expected)
    for path in set(previous) - files.keys():
        if check:
            stale.append(path)
        else:
            path.unlink()
    if stale:
        sys.exit("\n".join(f"stale: {path.relative_to(ROOT)}" for path in sorted(stale)))


def decode_ptx(function):
    with tempfile.TemporaryDirectory(dir=ROOT / ".lake") as temporary:
        output = Path(temporary) / "Decoded.lean"
        subprocess.run(
            [
                sys.executable,
                str(TOOLS / "export_decoded.py"),
                "--ptx-module",
                f"{MODULE}.Ptx",
                "--function",
                f"{GENERATED}.{function}",
                "--globals",
                f"{GENERATED}.module.globals",
                "--namespace",
                f"{NAMESPACE}.Decoded",
                "-o",
                str(output),
            ],
            cwd=ROOT,
            env={**os.environ, "TMPDIR": temporary},
            check=True,
        )
        return output.read_text(encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare without rewriting sources")
    args = parser.parse_args()

    subprocess.run([sys.executable, str(KERNEL / "gen_ptx.py"), "--check"], check=True)
    source = PTX.read_text(encoding="utf-8")
    (function,) = parse(source).functions
    emit({KERNEL / "Ptx.lean": export(source, GENERATED)}, args.check)

    # The decoder reads the freshly built PTX module and Core decoder.
    subprocess.run(
        [str(TOOLS / "build.sh"), "Core.Source.Decode", f"{MODULE}.Ptx"], cwd=ROOT, check=True
    )
    decoded = KERNEL / "Data" / "Decoded.lean"
    emit({decoded: decode_ptx(function.name)}, args.check)

    audit = Layout(KERNEL.name, 256, SOURCE_PARTS, 0, header_literal=True)
    previous_audit = [
        path
        for path in audit.out.glob("Decode*.lean")
        if re.fullmatch(r"Decode(Prep|Header|Source\d+|Code\d+)?\.lean", path.name)
    ]
    emit(
        {audit.out / name: text for name, text in audit.render().items()},
        args.check,
        previous_audit,
    )

    flow = KERNEL / "Flow"
    flow_json = flow / "flow.json"
    sites, paths = generate_flow(PTX, f"{NAMESPACE}.Flow")
    emit(
        {flow_json: paths, **{flow / name: text for name, text in sites.items()}},
        args.check,
        (flow / "Sites").glob("Part[0-9]*.lean"),
    )
    code = generate_code(
        decoded,
        flow_json,
        f"{NAMESPACE}.Flow",
        f"{NAMESPACE}.kernel",
        f"{MODULE}.Spec",
        flow / "Code.lean",
    )
    previous_code = list((flow / "Code").glob("Part[0-9]*.lean"))
    previous_code.extend(flow.glob("CvtRuns.lean"))
    emit(code, args.check, previous_code)


if __name__ == "__main__":
    main()
