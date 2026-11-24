# SPDX-License-Identifier: Apache-2.0
"""Make nvcc's source-file records independent of the FlashKDA and CUDA install paths."""

import argparse
import re
from pathlib import Path

FILE_RECORD = re.compile(r'(\s*\.file\s+\d+\s+)"([^"]+)"(.*)')


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("input", type=Path, help="PTX retained by nvcc")
    cli.add_argument("output", type=Path)
    cli.add_argument("--flashkda", type=Path, required=True, help="upstream source checkout")
    cli.add_argument("--cuda", type=Path, required=True, help="CUDA toolkit directory")
    args = cli.parse_args()
    roots = {args.flashkda.resolve(): "FlashKDA", args.cuda.resolve(): "CUDA"}
    lines = []
    for line in args.input.read_text().splitlines():
        record = FILE_RECORD.fullmatch(line)
        if record:
            path = Path(record[2])
            if path.is_absolute():
                for parent in path.parents:
                    if label := roots.get(parent.resolve()):
                        path = Path(label) / path.relative_to(parent)
                        break
                else:
                    cli.error(f"unrecognized source root for {path}")
            line = f'{record[1]}"{path}"{record[3]}'
        lines.append(line.rstrip())
    args.output.write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
