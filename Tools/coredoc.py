# SPDX-License-Identifier: Apache-2.0
"""Generate the reader document of Core (docs/core/) from the comments of Core/*.lean.

usage: coredoc.py [--check] [--report]

The document has two kinds of entries, both taken from comments in Core/*.lean:

* concepts: a def, abbrev, structure, inductive or class with its `/-- ... -/` doc comment;
* rules: the contract blocks `/-! ## ID — title` and their `### EXT-...` notes.

Each chapter is specified by `docs/core/chapters/<name>.json`: the rule blocks in reader order,
in groups, and a curated list of concepts. A rule shows its Statement, Source, Direction and
links to its Lean definitions; Applies, Premises, Effect and the remaining prose go into a
collapsed "Details for reviewers" block, and the `Review:` field is not shown. Every
entry links to its Lean source by a repo-relative path and line range, resolved by name when
the document is generated.

A chapter spec may also name sections of Core/README.md (`readme_sections`: a title and the
marker of a `<!-- BEGIN marker -->` ... `<!-- END marker -->` pair). Such a section is copied
after the rules. In it, a code span of a Core file followed by a colon and code spans of names
(`` `Core/Memory/Order.lean`: `po`, `baseCausality` ``) links each name to its declaration in
that file, and every rule ID links to its block.

The generator fails when a contract block or EXT note of Core is in no chapter or in two, when
a block has no Statement, when a `Defs` name does not resolve, when a chapter concept has no
doc comment, or when a README section is missing or names a definition or rule ID that does not
exist. With `--check` it regenerates in memory and also fails when a file in docs/core/
differs. `--report` prints comment lines that read as reviewer notes and prose glued to a field
line. The block parsing follows Tools/contract_index.py.
"""

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "Tools" / "isa"))
sys.path.insert(0, str(ROOT / "Tools"))
import doc_table  # noqa: E402
from contract_index import RULE_ID, RULE_PREFIXES  # noqa: E402

DOCS = "docs/core"
# Reading order of the chapters.
CHAPTERS = (
    "program",
    "instructions",
    "threads",
    "memory",
    "barriers",
    "mbarrier",
    "async",
    "tcgen05",
    "tmem",
    "clc",
    "assumptions",
    "correctness",
)
FIELDS = (
    "Statement",
    "Defs",
    "Source",
    "Direction",
    "Applies",
    "Premises",
    "Effect",
    "Review",
)
HIDDEN_FIELDS = ("Review", "Disclosed by every kernel", "Defs")
NOTE_FIELDS = (
    "Content",
    "Why it is not spec text",
    "Evidence",
    "Disclosed by every kernel",
    "Wider than the text by the reading only",
    "Wider than the text",
)
ALL_KEYS = FIELDS + NOTE_FIELDS
KINDS = (
    "def",
    "abbrev",
    "structure",
    "inductive",
    "class",
    "theorem",
    "lemma",
    "instance",
    "opaque",
    "axiom",
)
CONCEPT_KINDS = ("def", "abbrev", "structure", "inductive", "class")
MODIFIERS = r"(?:(?:private|protected|noncomputable|partial|unsafe|public|nonrec|meta)\s+)*"
DECL = re.compile(MODIFIERS + "(" + "|".join(KINDS) + r")\s+([^\s:({\[]+)")
COMMANDS = KINDS + (
    "namespace",
    "end",
    "section",
    "open",
    "variable",
    "universe",
    "attribute",
    "set_option",
    "macro",
    "syntax",
    "notation",
    "local",
    "scoped",
    "noncomputable",
    "private",
    "protected",
    "partial",
    "unsafe",
    "@[",
    "/--",
    "/-!",
    "/-",
    "public",
    "import",
    "module",
    "export",
    "deriving",
    "initialize",
    "elab",
    "declare_syntax_cat",
    "example",
    "#",
    "mutual",
    "meta",
)
# A Core file followed by the names of its declarations, in a README section.
FILE_DEFS = re.compile(r"`(Core/[\w/]+\.lean)`: (`[^`]+`(?:, `[^`]+`)*)")
# A rule ID or note ID in prose: not part of a word, a code span or a path.
RULE_REF = re.compile(
    r"(?<![\w`/#-])((?:PROG|THREAD|MEM|OBJ|DEP|ERR|EXT|ASM|OPEN)(?:-[A-Z0-9]+)+"
    r"|CORRECT(?:-[A-Z0-9]+)*)(?![\w`-])"
)
INTRO = (
    "This document describes the TxVerify model of PTX execution (`Core/`) for a reader. It has "
    "two kinds of entries. A concept is a Lean definition that the rules are stated over, shown "
    "with its doc comment. A rule is a contract block of the model: its statement says in plain "
    "words what it requires of programs or executions, its source cites the PTX ISA 9.5 text it "
    "rests on, and its direction says how it relates to that text. Interpretations, marked EXT, "
    "are readings of the PTX text that the model adopts beyond what the text states. Every entry "
    "is generated from the comments of the Lean source by `Tools/coredoc.py` and links to the "
    "lines it was generated from. The review guide and the index of all contract blocks are in "
    "[Core/README.md](../../Core/README.md)."
)


# ---------------------------------------------------------------- parsing


class Comment:
    """One `## ID — title` block or `### ID — title` note: a line range and its body lines."""

    def __init__(self, level, ident, title, file, start, end, body, nums):
        self.level, self.ident, self.title = level, ident, title
        self.file, self.start, self.end = file, start, end
        self.body, self.nums = body, nums  # body lines and their file line numbers
        self.segments = []  # ordered (key or None, text)
        self.adjacent = []  # (line number, text): unindented line right after a field
        self.fields = {}  # key -> text (first occurrence)
        self.line_keys = []  # segment key of each body line (None for prose)


def split_comments(rel, text):
    """The `## ` blocks and `### ` notes of every `/-! ... -/` module comment."""
    lines = text.splitlines()
    out = []
    i = 0
    while i < len(lines):
        if not lines[i].startswith("/-!"):
            i += 1
            continue
        j = i
        while not lines[j].rstrip().endswith("-/") or (j == i and lines[j].strip() == "/-!"):
            j += 1
        region = [(i + 1, lines[i][3:].lstrip())] + [(k + 1, lines[k]) for k in range(i + 1, j + 1)]
        last_text = region[-1][1].rstrip()
        region[-1] = (region[-1][0], last_text[:-2].rstrip())
        heads = [k for k, (_, ln) in enumerate(region) if re.match(r"#{2,3} ", ln)]
        for n, k in enumerate(heads):
            stop = heads[n + 1] if n + 1 < len(heads) else len(region)
            head = region[k][1]
            level = 2 if head.startswith("## ") else 3
            head = head[level + 1 :]
            m = k + 1
            while (
                level == 3 and m < stop and region[m][1].startswith("  ") and region[m][1].strip()
            ):
                head += " " + region[m][1].strip()
                m += 1
            ident, _, title = head.partition(" — ")
            last = stop - 1
            while last > k and not region[last][1].strip():
                last -= 1
            body = [ln for _, ln in region[m:stop]]
            nums = [x for x, _ in region[m:stop]]
            out.append(
                Comment(
                    level,
                    ident.strip(),
                    title.strip(),
                    rel,
                    region[k][0],
                    region[last][0],
                    body,
                    nums,
                )
            )
        i = j + 1
    return out


def parse_segments(c):
    """Split the body into labelled fields and unlabelled prose paragraphs."""
    note = c.level == 3 or not any(ln.startswith("Defs: ") for ln in c.body)
    segs = []  # [key, [lines]]
    cur = None
    c.line_keys = [None] * len(c.body)
    for idx, line in enumerate(c.body):
        m = re.match(r"([A-Z][A-Za-z ]+?)(?:,[a-z ]+)?: ?(.*)$", line)
        key = m.group(1) if m and m.group(1) in ALL_KEYS else None
        if line.startswith("Disclosed by every kernel"):
            key, m = "Disclosed by every kernel", re.match(r"()(.*)$", line)
        if key:
            cur = [key, [m.group(2)]]
            segs.append(cur)
        elif cur is None or not line.strip():
            if cur is not None and cur[0] is not None:
                cur = None
            if line.strip():
                cur = [None, [line]]
                segs.append(cur)
            elif segs and segs[-1][0] is None:
                segs[-1][1].append("")  # paragraph break inside prose
        else:
            indented = line.startswith("  ")
            if cur[0] is None:
                cur[1].append(line)
            elif cur[0] == "Direction" and not indented:
                cur = [None, [line]]
                segs.append(cur)
            elif cur[0] in NOTE_FIELDS or indented or (note and cur[0] == "Source"):
                cur[1].append(line)
            else:
                if not note:
                    c.adjacent.append((c.nums[idx], line.strip()))
                cur = [None, [line]]
                segs.append(cur)
        c.line_keys[idx] = segs[-1][0] if segs and line.strip() else None
    for key, ls in segs:
        text = "\n".join(ln.strip() if key else ln for ln in ls).strip("\n")
        c.segments.append((key, text))
        if key and key not in c.fields:
            c.fields[key] = text
    return c


class Decl:
    def __init__(self, kind, name, file, start, end, doc, members):
        self.kind, self.name, self.file = kind, name, file
        self.start, self.end, self.doc, self.members = start, end, doc, members


def is_command(line):
    return bool(line) and not line[0].isspace() and line.startswith(COMMANDS)


def strip_attributes(lines, i):
    """Skip `@[...]` attributes before a declaration, on their own lines or on its line."""
    line = lines[i] if i < len(lines) else ""
    while line.startswith("@["):
        depth, k = 0, 0
        for k, ch in enumerate(line):
            depth += ch == "["
            depth -= ch == "]"
            if depth == 0 and ch == "]":
                break
        line = line[k + 1 :].lstrip()
        if not line:
            i += 1
            line = lines[i] if i < len(lines) else ""
    return i, line


def doc_text(raw):
    return re.sub(r"\s?-/\s*$", "", re.sub(r"^\s*/--\s?", "", raw)).strip()


def parse_decls(rel, text):
    lines = text.splitlines()
    decls = []
    scopes = []  # stack of namespace names ("" for a section)
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        m = re.match(r"namespace ([\w.']+)", line)
        if m:
            scopes.append(m.group(1))
            i += 1
            continue
        if re.match(MODIFIERS + r"section\b", line):
            scopes.append("")
            i += 1
            continue
        if re.match(r"end\b", line):
            if scopes:
                scopes.pop()
            i += 1
            continue
        start = i
        doc = None
        if line.startswith("/--"):
            j = i
            while "-/" not in lines[j]:
                j += 1
            doc = doc_text("\n".join(lines[i : j + 1]))
            i = j + 1
        i, line = strip_attributes(lines, i)
        m = DECL.match(line)
        if not m:
            i = max(i, start + 1)
            continue
        kind, short = m.group(1), m.group(2)
        j = i + 1
        while j < n and not is_command(lines[j]):
            j += 1
        end = j
        while end > i + 1 and not lines[end - 1].strip():
            end -= 1
        prefix = ".".join(s for s in scopes if s)
        full = (prefix + "." if prefix else "") + short
        if short.startswith("_root_."):
            full = short.removeprefix("_root_.")
        decls.append(Decl(kind, full, rel, start + 1, end, doc, parse_members(kind, lines, i, end)))
        decls += where_helpers(kind, full, rel, lines, i, end)
        i = end
    return decls


def where_helpers(kind, full, rel, lines, i, end):
    """The auxiliary definitions of a `where` clause of a def or theorem, named `full.helper`."""
    if kind in ("structure", "inductive", "class"):
        return []
    at = next((k for k in range(i, end) if re.search(r"(^|\s)where\s*$", lines[k])), None)
    if at is None:
        return []
    heads = []
    pending = None
    k = at + 1
    while k < end:
        ln = lines[k]
        if re.match(r"  /--", ln):
            j = k
            while "-/" not in lines[j]:
                j += 1
            pending = (k, doc_text("\n".join(x.strip() for x in lines[k : j + 1])))
            k = j + 1
            continue
        hm = re.match(r"  (?:@\[[^\]]*\]\s*)*" + MODIFIERS + r"([A-Za-z_][\w']*)\b", ln)
        if hm and not ln.startswith("   "):
            first = pending[0] if pending else k
            heads.append((hm.group(1), first, pending[1] if pending else None))
        pending = None
        k += 1
    out = []
    for x, (name, first, doc) in enumerate(heads):
        stop = heads[x + 1][1] if x + 1 < len(heads) else end
        while stop > first + 1 and not lines[stop - 1].strip():
            stop -= 1
        out.append(Decl("def", f"{full}.{name}", rel, first + 1, stop, doc, []))
    return out


def parse_members(kind, lines, i, end):
    """Fields of a structure and constructors of an inductive, with their doc comments."""
    out = []
    if kind not in ("structure", "inductive", "class"):
        return out
    pending = None
    k = i + 1
    while k < end:
        ln = lines[k]
        if re.match(r"  /--", ln):
            j = k
            while "-/" not in lines[j]:
                j += 1
            pending = doc_text("\n".join(x.strip() for x in lines[k : j + 1]))
            k = j + 1
            continue
        if kind == "inductive" and re.match(r"  \|", ln):
            names = re.findall(r"\|\s*([A-Za-z_][\w']*)", ln)
            for x, nm in enumerate(names):
                out.append((nm, pending if x == 0 else None))
            pending = None
        elif kind != "inductive":
            m = re.match(r"  ([A-Za-z_][\w']*)\s*(?::|\(|\{|\[)", ln)
            if m and m.group(1) not in ("deriving", "mk", "extends"):
                out.append((m.group(1), pending))
                pending = None
        k += 1
    return out


class Repo:
    def __init__(self, root):
        self.root = Path(root)
        self.comments = {}  # id -> Comment
        self.decls = {}  # full name -> Decl
        self.files = {}  # file -> list of Decl
        for p in sorted((self.root / "Core").rglob("*.lean")):
            rel = p.relative_to(self.root).as_posix()
            text = p.read_text()
            for c in split_comments(rel, text):
                parse_segments(c)
                if c.ident in self.comments:
                    raise SystemExit(f"duplicate comment id {c.ident}")
                self.comments[c.ident] = c
            self.files[rel] = parse_decls(rel, text)
            for d in self.files[rel]:
                self.decls.setdefault(d.name, d)
        self.directions = {}
        readme = (self.root / "Core/README.md").read_text()
        self.readme = readme
        for m in re.finditer(r"^\| `([a-z-]+)` \| (.*?) \|$", readme, re.M):
            self.directions[m.group(1)] = m.group(2)

    def resolve(self, name):
        """A declaration by its `Defs` name, which Lean reads as `PTX.name` or `name`
        (Tests/Kernel/Contract.lean); also a field or constructor `Parent.member`."""
        name = name.strip()
        for cand in ("PTX." + name, name):
            if cand in self.decls:
                return self.decls[cand]
        parent, _, mem = name.rpartition(".")
        if parent:
            d = self.resolve(parent)
            if d and any(m[0] == mem for m in d.members):
                return d
        return None


# ---------------------------------------------------------------- rendering


def slug(s):
    return re.sub(r"[^a-z0-9 -]", "", s.lower()).strip().replace(" ", "-")


def split_defs(text):
    return [x.strip() for x in re.split(r",\s*", text.replace("\n", " ")) if x.strip()]


def split_source(text):
    """Split a Source field into citations at '; ' or '), ' before a section sign. Trailing
    `; EXT-...` references are returned separately as the readings relied on."""
    text = " ".join(text.split())
    readings = []
    m = re.search(r";\s*((?:EXT|OPEN)-[A-Z0-9-]+(?:,\s*(?:EXT|OPEN)-[A-Z0-9-]+)*)\s*$", text)
    if m:
        readings = [x.strip() for x in m.group(1).split(",")]
        text = text[: m.start()]
    return re.split(r"(?<=\)),\s+(?=§)|;\s+(?=§)", text), readings


def item_id(it):
    return it if isinstance(it, str) else it["id"]


def spec_concepts(spec):
    return [nm for g in spec["concept_groups"] for nm in g["items"]]


def spec_items(spec):
    return [(g["name"], item_id(it)) for g in spec["groups"] for it in g["items"]]


class Book:
    """All chapters: their specs, the home chapter of each block and concept anchors."""

    def __init__(self, repo, specs):
        self.repo, self.specs = repo, specs
        self.errors = []
        self.home = {}  # block id -> chapter
        homes = {}
        for name, spec in specs.items():
            for _, ident in spec_items(spec):
                homes.setdefault(ident, []).append(name)
                if ident not in repo.comments:
                    self.errors.append(f"{name}: no such contract block or note {ident}")
        for ident in repo.comments:
            where = homes.get(ident, [])
            if len(where) != 1:
                place = ", ".join(where) or "no chapter"
                self.errors.append(f"{ident} is in {place}; it must be in exactly one chapter")
            if where:
                self.home[ident] = where[0]
        self.anchor = {}  # (chapter, concept) -> anchor
        self.concept_home = {}  # concept -> first chapter that lists it
        for name, spec in specs.items():
            names = spec_concepts(spec)
            lower = [slug(nm.replace(".", "-")) for nm in names]
            for nm, low in zip(names, lower):
                a = "c-" + low
                if lower.count(low) > 1:  # names that differ only in case
                    a += "-" + hashlib.sha1(nm.encode()).hexdigest()[:6]
                self.anchor[(name, nm)] = a
                self.concept_home.setdefault(nm, name)

    def concept_link(self, chapter, nm):
        if (chapter, nm) in self.anchor:
            return "#" + self.anchor[(chapter, nm)]
        other = self.concept_home.get(nm)
        if other:
            return f"{other}.md#{self.anchor[(other, nm)]}"
        return None

    def block_link(self, chapter, ident):
        other = self.home.get(ident)
        if other is None:
            return None
        return ("" if other == chapter else f"{other}.md") + "#" + slug(ident)


def src(file, a, b):
    """A link from docs/core/ to lines a..b of a repo file."""
    return f"../../{file}#L{a}-L{b}"


class Chapter:
    def __init__(self, book, name):
        self.book, self.repo, self.name = book, book.repo, name
        self.spec = book.specs[name]
        self.errors = book.errors

    def render_concept(self, nm):
        d = self.repo.resolve(nm)
        out = [f'<a id="{self.book.anchor[(self.name, nm)]}"></a>', f"#### `{nm}`", ""]
        out += [f"*{d.kind}*", ""]
        if d.doc:
            out += [d.doc, ""]
        else:
            self.errors.append(f"{self.name}: concept {nm} ({d.file}:{d.start}) has no doc comment")
        flt = self.spec.get("member_filter", {}).get(nm)
        members = [m for m in d.members if flt is None or m[0] in flt]
        for mn, md in members:
            out.append(f"- `{mn}`" + (f": {' '.join(md.split())}" if md else ""))
        if members:
            out.append("")
        out += [f"[Lean source: `{d.file}` L{d.start}-L{d.end}]({src(d.file, d.start, d.end)})", ""]
        return out

    def def_link(self, nm, c):
        d = self.repo.resolve(nm)
        if d is None:
            self.errors.append(f"{c.ident} ({c.file}:{c.start}): Defs name {nm} does not resolve")
            return f"`{nm}`"
        text = f"[`{nm}`]({src(d.file, d.start, d.end)})"
        concept = self.book.concept_link(self.name, nm)
        if concept:
            text += f" ([concept]({concept}))"
        return text

    def ref_link(self, ident):
        link = self.book.block_link(self.name, ident)
        if link:
            return f"[{ident}]({link})"
        c = self.repo.comments.get(ident)
        if c:
            return f"[{ident}]({src(c.file, c.start, c.end)})"
        return ident

    def readme_section(self, marker):
        """The text between `<!-- BEGIN marker -->` and `<!-- END marker -->` of Core/README.md,
        with its definition names and rule IDs linked."""
        begin, end = f"<!-- BEGIN {marker} -->", f"<!-- END {marker} -->"
        text = self.repo.readme
        if text.count(begin) != 1 or text.count(end) != 1 or text.index(begin) > text.index(end):
            self.errors.append(f"{self.name}: Core/README.md needs one {begin} ... {end} pair")
            return []
        body = text.split(begin)[1].split(end)[0].strip("\n")
        where = f"Core/README.md ({marker})"

        def defs(m):
            file, out = m.group(1), []
            for nm in re.findall(r"`([^`]+)`", m.group(2)):
                d = self.repo.resolve(nm)
                if d is None or d.file != file:
                    self.errors.append(f"{where}: {nm} is not a declaration of {file}")
                    out.append(f"`{nm}`")
                else:
                    out.append(f"[`{nm}`]({src(d.file, d.start, d.end)})")
            return f"`{file}`: " + ", ".join(out)

        def rule(m):
            ident = m.group(1)
            if ident not in self.repo.comments:
                self.errors.append(f"{where}: no contract block or note {ident}")
                return ident
            return self.ref_link(ident)

        return RULE_REF.sub(rule, FILE_DEFS.sub(defs, body)).split("\n") + [""]

    def render_rule(self, ident):
        c = self.repo.comments[ident]
        is_note = c.level == 3
        is_ext = ident.startswith("EXT-")
        tag = "Interpretation (EXT)" if is_ext else "Rule"
        if ident.startswith("OPEN-"):
            tag = "Open issue"
        out = [
            f'<a id="{slug(ident)}"></a>',
            f"{'#####' if is_note else '####'} {c.title} (`{ident}`)",
        ]
        out += ["", f"*{tag}* · [Lean comment: `{c.file}` L{c.start}-L{c.end}]"]
        out[-1] += f"({src(c.file, c.start, c.end)})"
        out.append("")
        statement = c.fields.get("Statement")
        if statement:
            out += [" ".join(statement.split()), ""]
        else:
            self.errors.append(f"{ident} ({c.file}:{c.start}) has no Statement")
        details = []
        for key, text in c.segments:
            if key in HIDDEN_FIELDS or key in ("Statement", "Direction"):
                continue
            if key == "Source":
                parts, readings = split_source(text)
                out += ["Source:", ""] + [f"- {part}" for part in parts] + [""]
                if readings:
                    out += ["Readings relied on: " + ", ".join(map(self.ref_link, readings)), ""]
            elif key == "Premises" and text.strip().lower() in ("none", "none."):
                continue
            elif key:
                details += [f"**{key}:** {' '.join(text.split())}", ""]
            else:
                details += [text, ""]
        direction = c.fields.get("Direction")
        if direction:
            label = direction.split()[0].strip("(),.;")
            txt = f"Direction: `{label}`"
            rest = " ".join(direction.split())[len(label) :].strip()
            if rest:
                txt += f" {rest}"
            meaning = self.repo.directions.get(label)
            if meaning:
                txt += f" ({meaning[0].lower() + meaning[1:]})"
            if is_ext:
                txt += (
                    ". This is an interpretation (EXT): a reading the model adopts beyond what "
                    "the PTX text states."
                )
            out += [txt, ""]
        defs = split_defs(c.fields.get("Defs", ""))
        if defs == ["*"]:
            out += [f"Lean definitions: every definition of [`{c.file}`](../../{c.file}).", ""]
        elif defs and not is_note:
            out += ["Lean definitions: " + ", ".join(self.def_link(d, c) for d in defs), ""]
        if details:
            out += ["<details>", "<summary>Details for reviewers</summary>", ""]
            out += details + ["</details>", ""]
        return out

    def render(self):
        spec = self.spec
        bad = []
        for nm in spec_concepts(spec):
            d = self.repo.resolve(nm)
            if d is None or d.kind not in CONCEPT_KINDS:
                bad.append(f"{self.name}: concept {nm} does not resolve to a definition")
        if bad:
            self.errors.extend(bad)
            return ""
        items = spec_items(spec)
        out = [f"# {spec['title']}", "", spec["intro"], ""]
        out += [
            "Generated from the Lean comments of `Core/` by `Tools/coredoc.py`. Every entry links "
            "to the Lean source it was generated from. [All chapters](README.md).",
            "",
            "## Contents",
            "",
            "- [Concepts](#concepts)",
        ]
        for g in spec["concept_groups"]:
            out.append(f"  - [{g['name']}](#{slug(g['name'])})")
            for nm in g["items"]:
                out.append(f"    - [`{nm}`](#{self.book.anchor[(self.name, nm)]})")
        out.append("- [Rules](#rules)")
        tables = spec.get("tables")
        for g in spec["groups"]:
            out.append(f"  - [{g['name']}](#{slug(g['name'])})")
            for gname, ident in items:
                if gname == g["name"] and ident in self.repo.comments:
                    c = self.repo.comments[ident]
                    pad = "      " if c.level == 3 else "    "
                    out.append(f"{pad}- [{c.title}](#{slug(ident)}) (`{ident}`)")
        sections = spec.get("readme_sections", [])
        for s in sections:
            out.append(f"- [{s['title']}](#{slug(s['title'])})")
        if tables:
            out.append("- [Instruction tables](#instruction-tables)")
            for g in tables["groups"]:
                out.append(f"  - [{g['name']}](#{slug(g['name'])})")
            out.append("  - [Special registers](#special-registers)")
            out.append("  - [Not decoded](#not-decoded)")
        out += ["", "## Concepts", "", spec.get("concepts_intro", ""), ""]
        for g in spec["concept_groups"]:
            out += [f"### {g['name']}", "", g.get("intro", ""), ""]
            for nm in g["items"]:
                out += self.render_concept(nm)
        out += ["## Rules", "", spec.get("rules_intro", ""), ""]
        for g in spec["groups"]:
            out += [f"### {g['name']}", "", g.get("intro", ""), ""]
            for gname, ident in items:
                if gname == g["name"] and ident in self.repo.comments:
                    out += self.render_rule(ident)
        for s in sections:
            out += [f"## {s['title']}", ""] + self.readme_section(s["marker"])
        if tables:
            out += self.render_tables(tables)
        return "\n".join(out).rstrip() + "\n"

    def render_tables(self, tables):
        """The instruction tables: one per group of families, from isa-coverage.json."""
        cov = doc_table.load(self.repo.root / DOCS / "isa-coverage.json")
        link = lambda ident: self.book.block_link(self.name, ident)  # noqa: E731
        out = ["## Instruction tables", "", tables["intro"], ""]
        for g in tables["groups"]:
            core, dec, rej = doc_table.counts(cov, g["families"])
            out += [f"### {g['name']}", "", g["intro"], ""]
            out += [f"Entries: {core} with Core semantics, {dec} decode only, {rej} rejected.", ""]
            out += doc_table.render_family_table(cov, g["families"], link) + [""]
        core, dec, rej = doc_table.sreg_counts(cov)
        out += ["### Special registers", "", tables["sreg_intro"], ""]
        out += [f"Registers: {core} with Core semantics, {dec} decode only, {rej} rejected.", ""]
        out += doc_table.render_sreg_table(cov, link) + [""]
        out += ["### Not decoded", "", tables["excluded_intro"], ""]
        out += doc_table.render_excluded(cov) + [""]
        return out

    def counts(self):
        rules = ext = 0
        for _, ident in spec_items(self.spec):
            c = self.repo.comments.get(ident)
            if c and c.level == 3:
                ext += 1
            elif c:
                rules += 1
        return rules, ext, len(spec_concepts(self.spec))


def render_index(book):
    out = ["<!-- Generated by Tools/coredoc.py; do not edit. -->", "", "# TxVerify Core", "", INTRO]
    out += ["", "## Chapters", "", "In reading order:", ""]
    for n, name in enumerate(CHAPTERS, 1):
        spec = book.specs[name]
        rules, ext, concepts = Chapter(book, name).counts()
        first = spec["intro"].split(". ")[0].rstrip(".") + "."
        out.append(
            f"{n}. [{spec['title']}]({name}.md): {first} "
            f"({concepts} concepts, {rules} rules, {ext} EXT notes)"
        )
    return "\n".join(out) + "\n"


def rule_id_errors(repo):
    """An error for each contract block (`## ID`) whose ID does not match RULE_ID of
    Tools/contract_index.py: a prefix followed by at least one hyphenated part, or CORRECT."""
    return [
        f"{c.file}: rule ID {c.ident} is not one of the prefixes {', '.join(RULE_PREFIXES)}"
        " followed by a hyphenated part, nor CORRECT"
        for c in repo.comments.values()
        if c.level == 2 and not RULE_ID.fullmatch(c.ident)
    ]


def render_all(root):
    """{repo-relative path: text} of every generated file, and the list of errors."""
    repo = Repo(root)
    specs = {}
    for name in CHAPTERS:
        spec = json.loads((Path(root) / DOCS / "chapters" / f"{name}.json").read_text())
        if spec["name"] != name:
            raise SystemExit(f"chapter spec {name}.json has name {spec['name']}")
        specs[name] = spec
    book = Book(repo, specs)
    book.errors += rule_id_errors(repo)
    files = {f"{DOCS}/{name}.md": Chapter(book, name).render() for name in CHAPTERS}
    files[f"{DOCS}/README.md"] = render_index(book)
    return files, book.errors, repo, book


# ---------------------------------------------------------------- report

REVIEWER = [
    (
        re.compile(
            r"\bthe review checklist\b|\breview (?:the|each|how)\b|\breviewer|\bto review\b"
            r"|\bcheck (?:the )?quantifiers\b|\bis reviewed\b|\bare reviewed\b",
            re.I,
        ),
        "refers to review",
    ),
    (re.compile(r"\bLitmus\b|Tests/|\bKernels?/|Theorem\.lean"), "mentions a kernel or test"),
    (re.compile(r"\bdisclos", re.I), "disclosure wording"),
    (re.compile(r"\b[Ff]ormally,|\bkeeps more executions\b"), "the model's own strictness"),
]


def report(repo):
    for c in repo.comments.values():
        for ln, line in enumerate(c.body):
            if c.line_keys[ln] in HIDDEN_FIELDS:
                continue
            for rx, why in REVIEWER:
                if rx.search(line):
                    print(f"{c.file}:{c.nums[ln]}: {c.ident}: {why}: {line.strip()}")
        for ln, text in c.adjacent:
            print(f"{c.file}:{ln}: {c.ident}: prose glued to a field line: {text}")


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--check", action="store_true", help="fail if docs/core is stale")
    parser.add_argument("--report", action="store_true", help="print reviewer-tone lines")
    args = parser.parse_args()
    files, errors, repo, _ = render_all(ROOT)
    if args.report:
        report(repo)
    if errors:
        raise SystemExit("coredoc errors:\n" + "\n".join(errors))
    stale = [p for p, t in files.items() if not (ROOT / p).is_file() or (ROOT / p).read_text() != t]
    if args.check:
        if stale:
            raise SystemExit("docs/core is stale: run Tools/coredoc.py\n" + "\n".join(stale))
        return
    for p in stale:
        (ROOT / p).parent.mkdir(parents=True, exist_ok=True)
        (ROOT / p).write_text(files[p])
        print(f"wrote {p}", file=sys.stderr)


if __name__ == "__main__":
    main()
