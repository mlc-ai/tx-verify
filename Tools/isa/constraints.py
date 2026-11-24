# SPDX-License-Identifier: Apache-2.0
"""The legal modifier combinations of an entry as cubes, and its operand facts as lookup tables.

A cube assigns every slot a set of allowed values (a token, or `""` for an omitted optional
slot). `cubes(entry)` returns cubes whose union is exactly the entry's legal combinations: it
splits the combination set on the slot whose cofactors fall into the fewest classes, groups the
values with equal cofactors, recurses, and finally merges cubes that differ in one slot. The
cubes are pairwise disjoint. `verify_cubes` expands them and compares with the legal set.

An operand fact (`lanes`, `dtype`, `sink`) is a function of the legal combination.
`fact_table(entry, op, key)` finds a smallest set of slots the fact depends on and returns the
fact as a constant, as the value of one slot (`("slot", k)`, used for the type of most register
operands), or as rows `(values of the key slots, fact)`. `verify_fact` checks it on every legal
combination.
"""

import itertools

# Normalization of the table's private dtype tokens to the PTX type the register has. The
# table uses them only to choose a C carrier; the instruction sees a register of this type.
DTYPE_NORMAL = {
    "b32i": "b32",
    "b64i": "b64",
    "tma_size_b8": "b8",
    "cvt_scale_ue8m0": "b8",
    "st_async_b8reg": "b8",
    "mbarrier_report_b8reg": "b8",
}


def normal_dtype(t):
    return DTYPE_NORMAL.get(t, t)


def domains(entry):
    return [list(c) + ([""] if opt else []) for _, c, opt in entry["slots"]]


def _decompose(points, slots):
    """Cubes (dict slot -> frozenset) covering exactly `points` (tuples over `slots`)."""
    if not slots:
        return [{}] if points else []
    best = None
    for j in range(len(slots)):
        cof = {}
        for p in sorted(points):
            cof.setdefault(p[j], set()).add(p[:j] + p[j + 1 :])
        groups = {}
        for v, c in cof.items():
            groups.setdefault(frozenset(c), []).append(v)
        score = (len(groups), sum(len(c) for c in groups))
        if best is None or score < best[0]:
            best = (score, j, groups)
    _, j, groups = best
    rest = slots[:j] + slots[j + 1 :]
    out = []
    for cof, vals in sorted(groups.items(), key=lambda g: sorted(g[1])):
        for sub in _decompose(cof, rest):
            sub = dict(sub)
            sub[slots[j]] = frozenset(vals)
            out.append(sub)
    return out


def _merge(cubes, n):
    changed = True
    while changed:
        changed = False
        for a, b in itertools.combinations(range(len(cubes)), 2):
            ca, cb = cubes[a], cubes[b]
            diff = [k for k in range(n) if ca[k] != cb[k]]
            if len(diff) == 1:
                k = diff[0]
                cubes[a] = tuple(ca[i] if i != k else ca[i] | cb[i] for i in range(n))
                del cubes[b]
                changed = True
                break
    return cubes


def cubes(entry):
    """Disjoint cubes, each a tuple (one frozenset of values per slot)."""
    n = len(entry["slots"])
    points = set(entry["variants"])
    raw = _decompose(points, list(range(n)))
    out = sorted((tuple(c[k] for k in range(n)) for c in raw), key=_order)
    return sorted(_merge(out, n), key=_order)


def _order(cube):
    return [sorted(s) for s in cube]


def expand(cube):
    return set(itertools.product(*[sorted(s) for s in cube]))


def verify_cubes(entry, cs):
    legal = set(entry["variants"])
    union = set()
    for c in cs:
        pts = expand(c)
        if union & pts:
            return f"{entry['name']}: cubes overlap"
        union |= pts
    if union != legal:
        return f"{entry['name']}: cubes cover {len(union)} combinations, legal {len(legal)}"
    return None


def fact_table(entry, op, key):
    """The fact `key` of operand `op` as ("const", v), ("slot", k) or ("table", slots, rows)."""
    col = op[key]
    if key == "dtype":
        col = [normal_dtype(t) if t is not None else None for t in col]
    variants = entry["variants"]
    if len(set(map(repr, col))) == 1:
        return ("const", col[0])
    n = len(entry["slots"])
    if key == "dtype":
        for k in range(n):
            if all(v[k] == c for v, c in zip(variants, col, strict=True)):
                return ("slot", k)
    for size in range(1, n + 1):
        for ks in itertools.combinations(range(n), size):
            f = {}
            ok = True
            for v, c in zip(variants, col, strict=True):
                kv = tuple(v[k] for k in ks)
                if f.setdefault(kv, c) != c:
                    ok = False
                    break
            if ok:
                return ("table", list(ks), sorted(f.items(), key=lambda r: [str(x) for x in r[0]]))
    raise ValueError(f"{entry['name']}.{op['name']}: {key} is not a function of the modifiers")


def eval_fact(spec, combo):
    if spec[0] == "const":
        return spec[1]
    if spec[0] == "slot":
        return combo[spec[1]]
    _, ks, rows = spec
    kv = tuple(combo[k] for k in ks)
    for r, v in rows:
        if tuple(r) == kv:
            return v
    raise KeyError(kv)


def verify_fact(entry, op, key, spec):
    col = op[key]
    if key == "dtype":
        col = [normal_dtype(t) if t is not None else None for t in col]
    for v, c in zip(entry["variants"], col, strict=True):
        if eval_fact(spec, v) != c:
            return f"{entry['name']}.{op['name']}: {key} table wrong at {v}"
    return None


def verify_all(final):
    """Cube and fact verification for every non-excluded entry; returns error strings."""
    errors = []
    for e in final:
        if e["family"] == "excluded":
            continue
        err = verify_cubes(e, cubes(e))
        if err:
            errors.append(err)
        for op in e["operands"]:
            for key in ("lanes", "dtype", "sink"):
                err = verify_fact(e, op, key, fact_table(e, op, key))
                if err:
                    errors.append(err)
    return errors


if __name__ == "__main__":
    import sys
    from pathlib import Path

    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import families

    final = families.entries()
    total = sum(len(cubes(e)) for e in final if e["family"] != "excluded")
    print("cubes", total)
    print("\n".join(verify_all(final)) or "cubes and facts ok")
