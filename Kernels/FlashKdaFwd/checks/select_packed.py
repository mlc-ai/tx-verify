import argparse
import hashlib
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "Tools"))

SYMBOL_SHA256 = "90c7b6ce9ed03f9abd6bf8c5cf58fff0f3898cc966ace698d074e047863f0e17"


def select(source: str) -> str:
    from parse_ptx import parse

    code = re.sub(
        r'"(?:\\.|[^"\\])*"|/\*[\s\S]*?\*/|//[^\n]*',
        lambda m: m[0] if m[0].startswith('"') else " " + "\n" * m[0].count("\n"),
        source,
    )
    if re.search(r"^\s*\.(?:loc\s|file\s|section\s+\.debug)", code, re.M):
        raise ValueError("Rebuild without -lineinfo or device debug information")
    sections = re.split(r"(?=^\.visible \.entry )", code, flags=re.M)
    header = [
        line.rstrip()
        for line in sections[0].splitlines()
        if line.startswith((".version ", ".target ", ".address_size ", ".extern .shared "))
    ]
    selected = []
    for section in sections[1:]:
        name = section.split("(", 1)[0].removeprefix(".visible .entry ")
        if hashlib.sha256(name.encode()).hexdigest() == SYMBOL_SHA256:
            selected.append((name, section))
    if len(selected) != 1:
        raise ValueError(f"Expected one packed FP32 state entry, found {len(selected)}")
    name, clean = selected[0]
    text = "\n".join(header + [line.rstrip() for line in clean.splitlines() if line.strip()]) + "\n"
    original = parse(source)
    result = parse(text)
    if result.functions != [f for f in original.functions if f.name == name]:
        raise ValueError("The selected entry differs from the compiler output")
    if result.directives != original.directives:
        raise ValueError("Module directives changed during selection")
    if result.globals != [g for g in original.globals if ".shared" in g]:
        raise ValueError("Shared memory declarations changed during selection")
    return text


def main():
    cli = argparse.ArgumentParser()
    cli.add_argument("input", type=Path)
    cli.add_argument("output", type=Path)
    args = cli.parse_args()
    args.output.write_text(select(args.input.read_text()))


if __name__ == "__main__":
    main()
