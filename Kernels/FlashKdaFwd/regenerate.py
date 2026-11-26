#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Regenerate the generated files of the FlashKDA packed-recurrence kernel, or check them.

Everything is made from the frozen PTX (`packed_fp32_sm100a.ptx`), in two parts:

1. The repository's shared tools (`Tools/`) write `Ptx.lean`, `Data/Decoded.lean`,
   `Audit/Decode*.lean` and `Flow/` (the flow table `flow.json`, `Sites*.lean`, `Code*.lean`).
   The decoder is a Lean program, so this part builds Lean (`Tools/build.sh`).
2. The generators of `Gen/` (`GENERATORS` below) write the run declarations
   `Gen/Out/runs_*.json`, the tables `Gen/Tables/*.json` and the generated Lean files under
   `Math/` and `Proof/`. They read the PTX, the flow table of part 1 and each other's outputs,
   and build no Lean.

    python3 Kernels/FlashKdaFwd/regenerate.py                # write every generated file
    python3 Kernels/FlashKdaFwd/regenerate.py --check        # write nothing; fail if one is stale
    python3 Kernels/FlashKdaFwd/regenerate.py --only-gen     # part 2 alone (also with --check)
"""

import argparse
import hashlib
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
PTX = KERNEL / "packed_fp32_sm100a.ptx"
SHA256 = "19629983dc136cc19e18811d12ce4d423b775e7dc8d5ec29f7423b450c546108"

sys.path.insert(0, str(TOOLS))
from code_table import generate as generate_code  # noqa: E402
from decode_chunks import SOURCE_PARTS, Layout  # noqa: E402
from export_lean import export  # noqa: E402
from flow_gen import generate as generate_flow  # noqa: E402
from parse_ptx import parse  # noqa: E402

# The generators of `Gen/`, each after the ones whose outputs it reads (named in the comment).
# Each writes its outputs when run without arguments; with `--check` it writes nothing and
# fails if an output is stale. The five `ref_*` generators that have closed forms of their
# phase (carry, producer, compute, store, epilogue) also compare them with the control-flow
# simulator `Gen/simulate.py` in a check, which takes about a minute and a half in all.
GENERATORS = [
    "thread",  # reads `Flow/flow.json` of part 1
    "matrix_table",
    "values_ends",  # matrix_table
    "values",  # thread, matrix_table
    "ref_machine",
    "ref_startup_trace",
    "ref_carry",  # matrix_table, values_ends
    "ref_producer",
    "ref_compute",  # thread, matrix_table
    "ref_compute_protocol",  # ref_compute
    "ref_store",
    "ref_epilogue",
]


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


def from_ptx(check):
    """Part 1: the files the shared tools make from the PTX. This builds Lean."""
    source = PTX.read_text(encoding="utf-8")
    (function,) = parse(source).functions
    emit({KERNEL / "Ptx.lean": export(source, GENERATED)}, check)

    # The decoder reads the freshly built PTX module and Core decoder.
    subprocess.run(
        [str(TOOLS / "build.sh"), "Core.Source.Decode", f"{MODULE}.Ptx"], cwd=ROOT, check=True
    )
    decoded = KERNEL / "Data" / "Decoded.lean"
    emit({decoded: decode_ptx(function.name)}, check)

    # The mangled CuTe parameter names are 1,425 characters long, and the kernel cannot afford to
    # spell one during scope resolution (minutes and tens of gigabytes each). The scope pass is
    # therefore checked on its own, with the 20 instructions that name a parameter proved without
    # evaluating the name (`DecodeScopeNames`).
    audit = Layout(
        KERNEL.name,
        256,
        SOURCE_PARTS,
        0,
        header_literal=True,
        scope_ptx=PTX.name,
        long_symbol=256,
    )
    previous_audit = [
        path
        for path in audit.out.glob("Decode*.lean")
        if re.fullmatch(
            r"Decode(Prep|Header|Source\d+|Code\d+|Scope(Setup|Names|\d+)|Resolved)?\.lean",
            path.name,
        )
    ]
    emit(
        {audit.out / name: text for name, text in audit.render().items()},
        check,
        previous_audit,
    )

    flow = KERNEL / "Flow"
    flow_json = flow / "flow.json"
    sites, paths = generate_flow(PTX, f"{NAMESPACE}.Flow", core_events=True)
    emit(
        {flow_json: paths, **{flow / name: text for name, text in sites.items()}},
        check,
        (flow / "Sites").glob("Part[0-9]*.lean"),
    )
    code = generate_code(
        decoded,
        flow_json,
        f"{NAMESPACE}.Flow",
        # The lookups are stated over the decoder cache, so `Spec.lean` (whose `kernel` is an
        # abbreviation of it) can change without rebuilding the tables.
        f"{NAMESPACE}.Decoded.kernel",
        f"{MODULE}.Data.Decoded",
        flow / "Code.lean",
    )
    previous_code = list((flow / "Code").glob("Part[0-9]*.lean"))
    previous_code.extend(flow.glob("CvtRuns.lean"))
    emit(code, check, previous_code)


def run_generators(check):
    """Part 2: run every generator of `Gen/`, to write its outputs or, with `check`, to check
    them. A check runs them all and then fails if one of them failed. A write stops at the
    first failure, because the later generators read what the earlier ones write."""
    failed = []
    for name in GENERATORS:
        command = [sys.executable, str(KERNEL / "Gen" / f"{name}.py")]
        if check:
            command.append("--check")
        print(f"== Gen/{name}.py{' --check' if check else ''}", flush=True)
        if subprocess.run(command, cwd=ROOT).returncode:
            if not check:
                sys.exit(f"Gen/{name}.py failed")
            failed.append(name)
    if failed:
        sys.exit("stale or failing: " + ", ".join(f"Gen/{name}.py" for name in failed))


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--check", action="store_true", help="compare without rewriting sources")
    parser.add_argument(
        "--only-gen",
        action="store_true",
        help="run only the generators of Gen/ (part 2), which build no Lean",
    )
    args = parser.parse_args()

    if hashlib.sha256(PTX.read_bytes()).hexdigest() != SHA256:
        sys.exit(f"{PTX.name}: SHA256 differs from the pinned build product")
    if not args.only_gen:
        from_ptx(args.check)
    run_generators(args.check)


if __name__ == "__main__":
    main()
