# SPDX-License-Identifier: Apache-2.0
"""Check and rewrite the layout of the contract blocks of Core.

usage: contract_format.py --check [FILE ...]
       contract_format.py --apply FILE ...
       contract_format.py --worksheet PATH [FILE ...]

A contract block is a module comment `/-! ## ID — title` or an external/open note
`### EXT-...` / `### OPEN-...`. Its layout rules:

* fields are separated by exactly one blank line;
* a field label (`Statement:`, `Source:`, ...) starts at column 0, and the continuation lines
  of a field are indented by two spaces;
* `Source:` is a list with one item per line; an item is `- §x.y.z: "verbatim quote"` (a long
  quote wraps onto lines indented by two spaces) or a reference without a quote (`- EXT-FOO`);
* a `Content:` field is not used; its text belongs in the Statement;
* every paragraph belongs to a labeled field.

`--check` prints one line per violation (`file:line: ID: rule: detail`) and a count of the blocks
that violate each rule, and exits 1 when there is a violation. With no files it reads every
`.lean` file under `Core/`.

`--apply` rewrites the blocks of the given files mechanically: blank lines between fields,
two-space continuation indentation, and the split of an inline `Source:` into list items (one per
reference and quote). It never changes the words of a comment, so the result still passes the
quote check. Text that needs a human decision (a `Content:` field, an unlabeled paragraph, a
Source item that mixes a quote with other text) stays as it is. Applying twice changes nothing.

`--worksheet` writes a markdown file with one section for every block that needs such a decision:
the current text and a proposed rewrite.
"""

import argparse
import re
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WIDTH = 100
LABELS = (
    "Statement",
    "Source",
    "Content",
    "Why it is not spec text",
    "Direction",
    "Defs",
    "Applies",
    "Premises",
    "Effect",
    "Review",
    "Evidence",
    "Guarantee",
)
LABEL = re.compile("(" + "|".join(LABELS) + r"):(?: (.*))?$")
RULES = (
    "field-spacing",
    "continuation-indent",
    "source-not-list",
    "source-item-shape",
    "content-field",
    "unlabeled-paragraph",
)
QUOTE = re.compile(r'"([^"]+)"')
SPLIT_AHEAD = re.compile(r"\s*(§|EXT-|OPEN-|[A-Z][A-Z0-9]+-[A-Z])")


class Seg:
    """A field (label, lines) or an unlabeled paragraph (label None)."""

    def __init__(self, label, lines, line_no):
        self.label = label
        self.lines = lines
        self.line_no = line_no  # 1-based line of the first line
        self.unindented = False
        self.glued = False  # no blank line before it


class Block:
    def __init__(self, lines, start):
        self.start = start
        self.heading = lines[start]
        self.ident = lines[start].lstrip("/-! #").split(" — ")[0].strip()
        i = start + 1
        # A long note heading continues on lines that start with two spaces.
        while (
            lines[start].startswith("### ")
            and i < len(lines)
            and lines[i].startswith("  ")
            and not lines[i].endswith("-/")
        ):
            i += 1
        self.head_end = i
        self.terminator = None
        j = i
        while j < len(lines):
            line = lines[j]
            if line.startswith("### ") or line.startswith("/-! "):
                break
            if line.endswith("-/"):
                self.terminator = "alone" if line.strip() == "-/" else "attached"
                break
            j += 1
        if self.terminator == "attached":
            self.body_end = j + 1
            self.end = j + 1
        elif self.terminator == "alone":
            self.body_end = j
            self.end = j + 1
        else:
            self.body_end = self.end = j
        body = lines[self.head_end : self.body_end]
        if self.terminator == "attached":
            body[-1] = body[-1][: -len("-/")].rstrip()
            if not body[-1].strip():
                body.pop()
        self.body = body
        self.parse()

    def parse(self):
        segs, blanks_before, extra_blank = [], 0, False
        self.lead_blank = False
        self.trail_blanks = 0
        previous_blank = True  # the heading counts as separated
        first = True
        for k, line in enumerate(self.body):
            no = self.head_end + k + 1
            if not line.strip():
                blanks_before += 1
                previous_blank = True
                if blanks_before > 1 and segs:
                    extra_blank = True
                continue
            if first and blanks_before:
                self.lead_blank = True
            first = False
            m = LABEL.match(line)
            cur = segs[-1] if segs else None
            joined = not previous_blank
            if m:
                seg = Seg(m.group(1), [line], no)
                seg.glued = joined and cur is not None
                segs.append(seg)
            elif joined and cur is not None and cur.label is None:
                cur.lines.append(line)
            elif joined and cur is not None and self.continues(cur, line):
                if not line.startswith("  ") and not (cur.label == "Source" and line[:2] == "- "):
                    cur.unindented = True
                cur.lines.append(line)
            else:
                seg = Seg(None, [line], no)
                seg.glued = joined and cur is not None
                segs.append(seg)
            blanks_before = 0
            previous_blank = False
        self.trail_blanks = blanks_before if segs else 0
        self.segs = segs
        self.extra_blank = extra_blank

    @staticmethod
    def continues(seg, line):
        """Whether a line directly after a field line continues the field."""
        if seg.label is None:
            return True
        if seg.label == "Direction":
            return line.startswith("  ")
        return True

    def fields(self, label):
        return [s for s in self.segs if s.label == label]


def blocks_of(lines):
    out, i = [], 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("/-! ## ") or line.startswith(("### EXT-", "### OPEN-")):
            block = Block(lines, i)
            out.append(block)
            i = max(block.end, i + 1)
        else:
            i += 1
    return out


def source_items(seg):
    """The list items of a Source field: a list of (line_no, text), or None when the field is
    not in list form."""
    first = seg.lines[0]
    value = first[len("Source:") :].strip()
    if value:
        return None
    items = []
    for k, line in enumerate(seg.lines[1:], 1):
        if line.startswith("- "):
            items.append([seg.line_no + k, line[2:].strip()])
        elif line.startswith("  ") and items:
            items[-1][1] += " " + line.strip()
        else:
            return None
    return [tuple(x) for x in items]


def violations(block):
    """Yield (line_no, rule, detail) for a block."""
    for seg in block.segs:
        if seg.glued:
            yield seg.line_no, "field-spacing", "no blank line before " + (seg.label or "paragraph")
        if seg.unindented:
            yield seg.line_no, "continuation-indent", f"{seg.label} continuation is not indented"
        if seg.label is None:
            yield seg.line_no, "unlabeled-paragraph", seg.lines[0].strip()[:60]
        if seg.label == "Content":
            yield seg.line_no, "content-field", "Content text belongs in the Statement"
        if seg.label == "Source":
            items = source_items(seg)
            if items is None:
                yield seg.line_no, "source-not-list", "Source is not a list of `- ` items"
                continue
            for no, text in items:
                if '"' in text and not re.fullmatch(r'[^"]+?: "[^"]+"', text):
                    yield no, "source-item-shape", f'item is not `ref: "quote"`: {text[:50]}'
    if block.extra_blank:
        yield block.start + 1, "field-spacing", "more than one blank line"


def split_top(text):
    """Split a Source value at the `,` or `;` outside parentheses and quotes that is followed by
    a section reference or an ID."""
    parts, depth, quoted, last = [], 0, False, 0
    for i, c in enumerate(text):
        if c == '"':
            quoted = not quoted
        elif quoted:
            continue
        elif c == "(":
            depth += 1
        elif c == ")":
            depth = max(depth - 1, 0)
        elif c in ",;" and depth == 0 and SPLIT_AHEAD.match(text, i + 1):
            parts.append(text[last:i])
            last = i + 1
    parts.append(text[last:])
    return [p.strip() for p in parts if p.strip()]


def item_lines(item):
    """List items for one reference of an inline Source; (lines, needs_human)."""
    item = item.rstrip(".").strip()
    quotes = list(QUOTE.finditer(item))
    if not quotes:
        return [item], False
    ref = item[: quotes[0].start()].rstrip(" (:").strip()
    rest = QUOTE.sub("", item[len(item[: quotes[0].start()]) :])
    rest = re.sub(r"[\s(),;]|\band\b", "", rest)
    if rest or not ref:
        return [item], True
    return [f'{ref}: "{q.group(1)}"' for q in quotes], False


def wrap_item(text):
    return textwrap.wrap(
        text,
        WIDTH,
        initial_indent="- ",
        subsequent_indent="  ",
        break_long_words=False,
        break_on_hyphens=False,
    )


def listify(seg):
    """Lines of the list form of an inline Source field."""
    text = " ".join([seg.lines[0][len("Source:") :].strip()] + [x.strip() for x in seg.lines[1:]])
    text = re.sub(r"^PTX ISA \d+\.\d+ ", "", text.strip())
    out = ["Source:"]
    for part in split_top(text):
        lines, _ = item_lines(part)
        for one in lines:
            out += wrap_item(one)
    return out


def human_source_items(block):
    """Source items that mix a quote with other text, in inline or list form."""
    out = []
    for seg in block.fields("Source"):
        items = source_items(seg)
        if items is None:
            text = " ".join(
                [seg.lines[0][len("Source:") :].strip()] + [x.strip() for x in seg.lines[1:]]
            )
            text = re.sub(r"^PTX ISA \d+\.\d+ ", "", text.strip())
            for part in split_top(text):
                if item_lines(part)[1]:
                    out.append(part)
        else:
            out += [t for _, t in items if '"' in t and not re.fullmatch(r'[^"]+?: "[^"]+"', t)]
    return out


def render_block(block):
    """The lines of the rewritten body (without heading and terminator)."""
    out = [""] if block.lead_blank else []
    for k, seg in enumerate(block.segs):
        if k:
            out.append("")
        lines = seg.lines
        if seg.label == "Source" and source_items(seg) is None:
            lines = listify(seg)
        elif seg.label is not None:
            lines = [lines[0]] + [
                x
                if x.startswith("  ") or (seg.label == "Source" and x.startswith("- "))
                else "  " + x
                for x in lines[1:]
            ]
            if max(len(x) for x in lines) > WIDTH and any(
                not x.startswith("  ") for x in seg.lines[1:]
            ):
                lines = textwrap.wrap(
                    " ".join(x.strip() for x in seg.lines),
                    WIDTH,
                    subsequent_indent="  ",
                    break_long_words=False,
                    break_on_hyphens=False,
                )
        out += lines
    out += [""] * min(block.trail_blanks, 1)
    return out


def rewrite(text):
    lines = text.split("\n")
    for block in reversed(blocks_of(lines)):
        new = render_block(block)
        if block.terminator == "attached":
            new[-1] = new[-1] + "-/"
        lines[block.head_end : block.body_end] = new
    return "\n".join(lines)


def core_files():
    return sorted((ROOT / "Core").rglob("*.lean"))


def rel(path):
    try:
        return str(Path(path).resolve().relative_to(ROOT))
    except ValueError:
        return str(path)


def check_text(text):
    """Yield (line_no, ident, rule, detail) for a source text."""
    for block in blocks_of(text.split("\n")):
        for no, rule, detail in violations(block):
            yield no, block.ident, rule, detail


def check_files(files):
    """Return (messages, {rule: blocks violating it}, number of blocks)."""
    messages, counts, total = [], {r: 0 for r in RULES}, 0
    for path in files:
        text = Path(path).read_text()
        total += len(blocks_of(text.split("\n")))
        for block in blocks_of(text.split("\n")):
            rules = set()
            for no, rule, detail in violations(block):
                messages.append(f"{rel(path)}:{no}: {block.ident}: {rule}: {detail}")
                rules.add(rule)
            for rule in rules:
                counts[rule] += 1
    return messages, counts, total


def sentences(text):
    return [s.strip() for s in re.split(r"(?<=[.;])\s+", text) if s.strip()]


def words(text):
    return set(re.findall(r"[a-z0-9_:.`]+", text.lower()))


def seg_text(seg):
    first = seg.lines[0]
    if seg.label:
        first = first[len(seg.label) + 1 :]
    return " ".join([first.strip()] + [x.strip() for x in seg.lines[1:]]).strip()


def worksheet(files):
    out = [
        "# Contract block worksheet",
        "",
        "Generated by `Tools/contract_format.py --worksheet`. One section per block whose text needs",
        "a decision: a `Content:` field to merge into the Statement or drop, unlabeled paragraphs to",
        "assign to a field, and Source items that mix a quote with other text.",
        "",
    ]
    count = 0
    for path in files:
        lines = Path(path).read_text().split("\n")
        for block in blocks_of(lines):
            content = block.fields("Content")
            paras = [s for s in block.segs if s.label is None]
            human = human_source_items(block)
            if not (content or paras or human):
                continue
            count += 1
            out += [f"## {block.ident}", "", f"File: {rel(path)}:{block.start + 1}", ""]
            statement = " ".join(seg_text(s) for s in block.fields("Statement"))
            out += ["Current Statement:", "", textwrap.indent(statement, "> "), ""]
            keep = []
            for seg in content:
                body = seg_text(seg)
                out += ["Current Content:", "", textwrap.indent(body, "> "), ""]
                base = words(statement)
                for sent in sentences(body):
                    w = words(sent)
                    share = len(w & base) / len(w) if w else 1
                    if share < 0.8:
                        keep.append(sent)
            if content:
                if keep:
                    out += ["Proposed: merge into the Statement, or keep as a short Content:", ""]
                    out += [textwrap.indent(s, "> ") for s in keep] + [""]
                else:
                    out += ["Proposed: drop Content; the Statement covers it.", ""]
            for seg in paras:
                body = " ".join(x.strip() for x in seg.lines)
                out += [
                    f"Unlabeled paragraph (line {seg.line_no}):",
                    "",
                    textwrap.indent(body, "> "),
                    "",
                    "Proposed: assign to Effect, Review, Evidence or Why it is not spec text,",
                    "or merge into the Statement.",
                    "",
                ]
            for item in human:
                out += [
                    "Source item with a quote and other text:",
                    "",
                    textwrap.indent(item, "> "),
                    "",
                    'Proposed: one `- §ref: "quote"` item per quote, and the other text in the',
                    "Statement or in `Why it is not spec text`.",
                    "",
                ]
    out.insert(2, f"{count} blocks need a decision.")
    return "\n".join(out).rstrip() + "\n"


def main(argv=None):
    cli = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawTextHelpFormatter
    )
    mode = cli.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true", help="report format violations")
    mode.add_argument("--apply", action="store_true", help="rewrite the blocks of FILE ...")
    mode.add_argument("--worksheet", metavar="PATH", help="write the rewrite worksheet")
    cli.add_argument("files", nargs="*")
    args = cli.parse_args(argv)
    files = [Path(f) for f in args.files] or core_files()
    if args.apply:
        if not args.files:
            cli.error("--apply needs explicit files")
        for path in files:
            old = path.read_text()
            new = rewrite(old)
            if new != old:
                path.write_text(new)
        return 0
    if args.worksheet:
        Path(args.worksheet).write_text(worksheet(files))
        return 0
    messages, counts, total = check_files(files)
    print("\n".join(messages))
    print(f"blocks: {total}", file=sys.stderr)
    for rule in RULES:
        print(f"{rule}: {counts[rule]} blocks", file=sys.stderr)
    return 1 if messages else 0


if __name__ == "__main__":
    sys.exit(main())
