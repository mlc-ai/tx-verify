# SPDX-License-Identifier: Apache-2.0
"""Line breaking for generated Lean text.

The generators write one declaration or list item per line. `wrap` breaks a line that is longer
than `WIDTH` columns at the places where Lean allows a break: after the commas of a bracketed
group (`[...]`, `⟨...⟩`, `{...}`, `(...)`), or between the arguments of an application. Only
whitespace changes: the non-whitespace characters of the result are those of the input.
Strings are never broken.
"""

import re

WIDTH = 100
OPEN = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
CLOSE = set(OPEN.values())
IDENT = re.compile(r"[\w?!']")


class Atom:
    def __init__(self, text):
        self.text = text

    def flat(self):
        return self.text


class Group:
    def __init__(self, opener, pad):
        self.open, self.close, self.pad = opener, OPEN[opener[-1]], pad
        self.segs = [[]]
        self.post = ""
        self.unclosed = False  # a line that opens a bracket closed on a later line

    def flat(self):
        inner = ", ".join(" ".join(t.flat() for t in seg) for seg in self.segs)
        if self.unclosed:
            return self.open + (" " if self.pad else "") + inner
        pad = " " if self.pad else ""
        return self.open + pad + inner + pad + self.close + self.post


def parse(text):
    """The tokens of a flat line: atoms and bracketed groups."""
    root = Group("(", False)
    stack, i, n = [root], 0, len(text)
    while i < n:
        c = text[i]
        cur = stack[-1].segs[-1]
        if c == " ":
            i += 1
        elif c == '"':
            j = i + 1
            while text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            glued = i > 0 and text[i - 1] not in " ([{⟨"
            if glued and cur and isinstance(cur[-1], Atom):
                cur[-1].text += text[i : j + 1]
            else:
                cur.append(Atom(text[i : j + 1]))
            i = j + 1
        elif c in OPEN:
            glued = i > 0 and cur and text[i - 1] not in " ([{⟨,"
            index = c == "[" and glued and cur and IDENT.match(text[i - 1] if i else " ")
            pad = c == "{" and text[i + 1 : i + 2] == " "
            if index and isinstance(cur[-1], Atom):
                # `a[i]?`: an index stays glued to its term
                depth, j = 0, i
                while True:
                    depth += (text[j] in OPEN) - (text[j] in CLOSE)
                    j += 1
                    if depth == 0:
                        break
                cur[-1].text += text[i:j]
                i = j
                continue
            opener = c
            if c == "[" and cur and isinstance(cur[-1], Atom) and cur[-1].text == "#":
                cur.pop()
                opener = "#["
            g = Group(opener, pad)
            cur.append(g)
            stack.append(g)
            i += 1
        elif c in CLOSE and len(stack) == 1:
            # the closer of a group opened on an earlier line: an atom of its own
            cur.append(Atom(c))
            i += 1
        elif c in CLOSE:
            g = stack.pop()
            i += 1
            j = i
            while j < n and text[j] not in " ([{⟨)]}⟩,":
                j += 1
            g.post = text[i:j]
            i = j
        elif c == "," and len(stack) > 1:
            stack[-1].segs.append([])
            i += 1
        else:
            j = i
            while j < n and text[j] not in ' ([{⟨)]}⟩"' and not (text[j] == "," and len(stack) > 1):
                j += 1
            if j == i:  # a top-level comma or stray closer
                j = i + 1
            glued = i > 0 and text[i - 1] not in " ([{⟨,"
            if glued and cur:
                last = cur[-1]
                if isinstance(last, Atom):
                    last.text += text[i:j]
                else:
                    last.post += text[i:j]
            else:
                cur.append(Atom(text[i:j]))
            i = j
    for g in stack[1:]:
        g.unclosed = True
    return root.segs[0]


class Writer:
    def __init__(self, col, width):
        self.out, self.col, self.width = [], col, width

    def put(self, s):
        self.out.append(s)
        self.col += len(s)

    def newline(self, ind):
        self.out.append("\n" + " " * ind)
        self.col = ind

    def seq(self, tokens, ind, nested, tail, first_sep):
        for k, t in enumerate(tokens):
            sep = " " if (k > 0 or first_sep) else ""
            need = len(t.flat()) + (tail if k == len(tokens) - 1 else 0)
            if self.col + len(sep) + need <= self.width:
                self.put(sep + t.flat())
            elif isinstance(t, Group):
                self.group(t, ind, nested, tail if k == len(tokens) - 1 else 0, sep)
            else:
                if self.out:  # a line's first token stays on it
                    self.newline(ind)
                self.put(t.flat())
                if self.col > self.width:
                    self.gaps(t, ind)

    def gaps(self, t, ind):
        """Redo the last atom `t`, a string literal wider than the line, with string gaps: a
        `\\` at the end of a line skips the white space that starts the next one, so the
        string keeps its value."""
        text = t.flat()
        if not (text.startswith('"') and text.endswith('"') and "\\" not in text):
            return
        self.out.pop()
        self.col -= len(text)
        body = text[1:-1]
        self.put('"')
        while self.col + len(body) + 3 > self.width:  # the closing quote, `,` and `]`
            cut = min(self.width - self.col - 1, len(body) - 1)
            while cut > 1 and body[cut] == " ":
                cut -= 1
            self.put(body[:cut] + "\\")
            body = body[cut:]
            self.newline(ind)
        self.put(body + '"')

    def group(self, g, line, child, tail, sep):
        multi = len(g.segs) > 1
        if not multi and not g.pad:
            # an application in parentheses: move it to a fresh line if it fits there
            if line + len(g.flat()) + tail <= self.width:
                self.newline(line)
                self.put(g.flat())
                return
        if g.pad and g.open == "{" and self.col != line and self.out:
            # a structure instance: its fields must not start left of the first one
            self.newline(line)
            sep = ""
        if self.col + len(sep) + len(g.open) + 2 > self.width:
            self.newline(line)
            sep = ""
        self.put(sep + g.open + (" " if g.pad else ""))
        if g.pad and g.open == "{":
            child = self.col
        for s, seg in enumerate(g.segs):
            last = s == len(g.segs) - 1
            if g.unclosed:
                end = 1
            else:
                end = len(g.close) + len(g.post) + tail + (2 if g.pad else 0) if last else 1
            if not seg:
                continue
            if g.pad and g.open == "{":
                # a field starts at the column of the first one; its continuation lines are
                # indented further, or they would end the field
                flat = " ".join(t.flat() for t in seg)
                if s > 0 and self.col + 1 + len(flat) + end <= self.width:
                    self.put(" " + flat)
                else:
                    if s > 0:
                        self.newline(child)
                    self.seq(seg, child + 2, child + 4, end, False)
            else:
                self.seq(seg, child, child + 2, end, s > 0)
            if not last:
                self.put(",")
        if not g.unclosed:
            self.put((" " if g.pad else "") + g.close + g.post)


def wrap(line, step=4, width=WIDTH):
    """`line` broken to at most `width` columns where possible; continuation lines are indented
    `step` columns more than `line`."""
    if len(line) <= width:
        return line
    lead = len(line) - len(line.lstrip(" "))
    tokens = parse(line.strip(" "))
    groups = [k for k, t in enumerate(tokens) if isinstance(t, Group)]
    if groups and all(isinstance(t, Atom) for t in tokens[groups[-1] + 1 :]):
        # the trailing `:= by` stays with the last group
        tail = tokens[groups[-1] + 1 :]
        tokens[groups[-1]].post += "".join(" " + t.text for t in tail)
        tokens = tokens[: groups[-1] + 1]
    w = Writer(lead, width)
    w.seq(tokens, lead + step, lead + step, 0, False)
    result = " " * lead + "".join(w.out)
    if "".join(re.sub(r"\\\n\s*", "", result).split()) != "".join(line.split()):
        raise ValueError(f"cannot break {line[:60]!r}: unbalanced brackets")
    return result


def wrap_lines(lines, step=4, width=WIDTH):
    """Apply `wrap` to every code line of `lines`; comment lines are left as they are. The
    result has one entry per output line."""
    out = []
    for line in lines:
        if len(line) > width and not line.lstrip().startswith(("--", "/-")):
            line = wrap(line, step, width)
        out.extend(line.split("\n"))
    return out
