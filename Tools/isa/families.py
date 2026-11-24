# SPDX-License-Identifier: Apache-2.0
"""Assign every instruction entry (vendored table plus `extra.py`) to exactly one family.

`entries()` returns the final entry list the generator works on. Each entry gets:

* `family`: one of `FAMILIES`. `excluded` entries are not decoded; `reason` says why.
* `section`: the PTX ISA 9.5 section whose heading names the instruction.
* `effect`: `event` when the entry has an address operand or orders memory (`orders_memory` of
  the table), `ctl` for the control-flow entries of `extra.py`, `local` otherwise.

A few table entries mix integer and floating-point types in one type slot (`setp`, `set`, `min`,
`max`). Those are split by the token of that slot into an `_int` and an `_f` entry, so that each
family's layer sees only its own types; `prefetch` is split by its optional `.tensormap` token.
The split entries keep the table's slots and operands, and their legal combinations are the
table's, filtered by the token; `check_partition` verifies that every legal combination of every
table entry lands in exactly one final entry.
"""

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import extra  # noqa: E402
from load_table import load  # noqa: E402

FAMILIES = [
    "int",
    "move",
    "cvt",
    "mem",
    "warp",
    "ctl",
    "float",
    "barrier",
    "fence",
    "mbarrier",
    "async",
    "tc",
    "clc",
    "matrix",
    "multimem",
    "texture",
    "misc",
    "unmodeled",
    "excluded",
]

# Default family of a mnemonic; `ENTRY_FAMILY` and `SPLITS` refine it per entry.
MNEMONIC_FAMILY = {
    **dict.fromkeys(
        "and or xor not cnot lop3 shf shl shr prmt selp popc clz bfind fns brev bfe bfi szext "
        "bmsk dp4a dp2a clmad mul24 mad24 sad rem div abs neg set setp min max addc subc "
        "madc".split(),
        "int",
    ),
    # `slct.dtype.ctype`: the selection compares `c` with zero, as `.s32` or as `.f32`. The entry
    # selects a value of any `.dtype`, so it stays with the comparison/select instructions.
    "slct": "int",
    "mov": "move",
    "cvt": "cvt",
    "cvt.pack": "cvt",
    **dict.fromkeys(
        "ld ldu st st.bulk atom red cvta mapa getctarank prefetch prefetchu isspacep discard "
        "applypriority".split(),
        "mem",
    ),
    **dict.fromkeys(
        "shfl.sync vote.sync match redux.sync activemask elect.sync".split(),
        "warp",
    ),
    **dict.fromkeys("bra brx.idx ret exit trap".split(), "ctl"),
    # The debugger can suspend the thread. A correctness proof must exclude a reached breakpoint.
    "brkpt": "unmodeled",
    **dict.fromkeys(
        "add sub mul mad fma testp copysign rcp sqrt rsqrt sin cos lg2 ex2 tanh".split(), "float"
    ),
    **dict.fromkeys(["bar", "barrier"], "barrier"),
    "fence": "fence",
    "membar": "fence",
    "mbarrier": "mbarrier",
    # tensormap.replace writes fields of a tensor map and tensormap.cp_fenceproxy copies one;
    # both belong with the tensor copies that read tensor maps.
    **dict.fromkeys(["cp", "red.async", "st.async", "tensormap.replace"], "async"),
    "tensormap.cp_fenceproxy": "async",
    "tcgen05": "tc",
    "clusterlaunchcontrol": "clc",
    # spcompress/spdecompress pack and unpack sparse matrix fragments across a warp.
    **dict.fromkeys("ldmatrix stmatrix movmatrix mma spcompress spdecompress".split(), "matrix"),
    **dict.fromkeys(
        "multimem.cp multimem.ld_reduce multimem.red multimem.red.async multimem.st "
        "multimem.st.async".split(),
        "multimem",
    ),
    **dict.fromkeys(
        ["setmaxnreg", "griddepcontrol", "createpolicy", "nanosleep", "pmevent"], "misc"
    ),
    "fabric": "unmodeled",
    "wgmma": "excluded",
}

ENTRY_FAMILY = {
    **dict.fromkeys(
        "add_int sub_int mul_int mul_wide mad_int mad_wide neg_int add_cc sub_cc mad_cc".split(),
        "int",
    ),
    **dict.fromkeys(["abs_f", "abs_half", "neg", "neg_half", "div_f", "min3", "max3"], "float"),
    # Half-precision comparisons (§9.7.8) compare `.f16`/`.bf16` values.
    **dict.fromkeys(
        "set_half set_half_bool setp_half setp_half_pq setp_half_bool setp_half_bool_pq".split(),
        "float",
    ),
    # `bar.warp.sync` synchronizes the threads of a warp; it is a warp collective.
    "bar_warp_sync": "warp",
    # The bulk forms of applypriority are asynchronous operations (§9.7.10.18, §9.7.10.19).
    **{
        n: "async"
        for n in [
            "applypriority_async_bulk",
            "applypriority_async_bulk_tensor",
            "applypriority_async_bulk_tensor_im2col",
            "applypriority_async_bulk_tensor_override_address",
            "applypriority_async_bulk_tensor_override_global_dim_b8",
            "applypriority_async_bulk_tensor_override_global_dim_b16",
            "applypriority_async_bulk_tensor_override_global_dim_stride_b8",
            "applypriority_async_bulk_tensor_override_global_dim_stride_b16",
            "applypriority_async_bulk_tensor_override_address_im2col",
        ]
    },
}

INT_TYPES = {
    "b8",
    "b16",
    "b32",
    "b64",
    "u8",
    "u16",
    "u32",
    "u64",
    "s8",
    "s16",
    "s32",
    "s64",
    "u16x2",
    "s16x2",
    "u8x4",
    "s8x4",
}

# entry -> (slot, token -> (name suffix, family)). The comparison type decides the family of
# `set` and `setp`; the operand type decides it for `min` and `max`.
SPLITS = {
    **{
        n: ("type", lambda t: ("_int", "int") if t in INT_TYPES else ("_f", "float"))
        for n in ["setp", "setp_pq", "setp_bool", "setp_bool_pq", "min", "max"]
    },
    **{
        n: ("stype", lambda t: ("_int", "int") if t in INT_TYPES else ("_f", "float"))
        for n in ["set", "set_bool"]
    },
    "prefetch": ("tensormap", lambda t: ("_tensormap", "async") if t else ("", "mem")),
    # `mapa` with `.space` takes a variable as `a`; without it `a` is a register (§9.7.10.26).
    "mapa": ("space", lambda t: ("", "mem") if t else ("_generic", "mem")),
}

EXCLUDED_REASON = {"wgmma": "out of scope: wgmma"}

# Entries whose PTX spelling is that of another entry: the table separates them only by the C
# type of an argument (a pointer or an integer for mapa's address, so `mapa_u32` is mapa's
# `.u32` combination with the space written; a `.b8` or `.b16` register
# for the TMA override tensor sizes). Each alias decodes as its canonical entry; an operand
# whose type differs between the two gets no type token (`dtype` none), and the family layer
# reads the register's width.
ALIASES = {
    "mapa_u64_raw": "mapa_generic",
    "mapa_u32": "mapa",
    "mapa_u64_shared": "mapa",
    **{
        f"{base}_b16": f"{base}_b8"
        for base in [
            f"{op}_override_global_dim{stride}"
            for op in [
                "cp_async_bulk_tensor_g2s_cta",
                "cp_async_bulk_tensor_g2s_cluster",
                "cp_async_bulk_tensor_s2g",
                "cp_reduce_async_bulk_tensor",
                "cp_async_bulk_tensor_prefetch",
                "applypriority_async_bulk_tensor",
            ]
            for stride in ["", "_stride"]
        ]
        + [
            "cp_async_bulk_tensor_prefetch_override_global_dim_evict_last",
            "cp_async_bulk_tensor_prefetch_override_global_dim_stride_evict_last",
        ]
    },
}

# Slot pairs written in either order. §9.7.10.28.5.3 lists `{.cta_group}{.level::cache_hint}`
# for cp.async.bulk.tensor; the text gives qualifier order no meaning and ptxas accepts both
# orders (PROG-DECODE), so an entry with both slots also accepts them swapped.
SWAPS = [("cta_group", "cache")]

# (regex on the entry name, section). The first match wins; checked against the headings of
# ptx-isa-9.5.txt by `check_sections`.
SECTIONS = [
    (r"(add|sub|mul|mad|neg)_int$|mul_wide$|mad_wide$", None),  # by mnemonic, integer table
    (r"(add|sub)_mixed", "9.7.5.{add:1,sub:2}"),
    (r"fma_mixed", "9.7.5.3"),
    (r"mul_mixed", "9.7.5.4"),
    (r"^(add|sub|mul|fma|neg|abs)_half$", "9.7.4.{add:1,sub:2,mul:3,fma:4,neg:5,abs:6}"),
    (r"^tanh_half$", "9.7.4.9"),
    (r"^ex2_half$", "9.7.4.10"),
    (r"^set_half", "9.7.8.1"),
    (r"^setp_half", "9.7.8.2"),
    (r"^set(_bool|_packed)?(_int|_f)?$", "9.7.7.1"),
    (r"^setp(_bool)?(_pq)?(_int|_f)?$", "9.7.7.2"),
    (r"^(min|max)(3|_f)$", "9.7.3.{min:11,max:12}"),
    (r"^(min|max)_int$", "9.7.1.{min:13,max:14}"),
    (r"^(abs_f|neg|div_f|mad_f)$", "9.7.3.{abs:9,neg:10,div:8,mad:7}"),
    (r"^mov_(un)?pack", "9.7.10.4"),
    (r"^ld_proxy_readonly$|^ld_param", "9.7.10.8"),
    (r"^prefetch", "9.7.10.16"),
    (r"^applypriority_async_bulk_tensor", "9.7.10.19"),
    (r"^applypriority_async_bulk$", "9.7.10.18"),
    (r"^cp_async_(ca|cg)", "9.7.10.28.3.1"),
    (r"^cp_async_commit_group$", "9.7.10.28.3.2"),
    (r"^cp_async_wait_(group|all)$", "9.7.10.28.3.3"),
    (r"^cp_async_bulk_commit_group$", "9.7.10.28.6.1"),
    (r"^cp_async_bulk_wait_group$", "9.7.10.28.6.2"),
    (r"^cp_async_bulk_tensor_prefetch", "9.7.10.28.5.5"),
    (r"^cp_async_bulk_tensor", "9.7.10.28.5.3"),
    (r"^cp_reduce_async_bulk_tensor", "9.7.10.28.5.4"),
    (r"^cp_async_bulk_prefetch", "9.7.10.28.4.3"),
    (r"^cp_async_bulk", "9.7.10.28.4.1"),
    (r"^cp_reduce_async_bulk", "9.7.10.28.4.2"),
    (r"^cp_async_mbarrier_arrive$", "9.7.15.16.18"),
    (r"^multimem_cp_reduce", "9.7.10.28.4.5"),
    (r"^multimem_cp_async", "9.7.10.28.4.4"),
    (r"^multimem_st_async$", "9.7.10.13"),
    (r"^multimem_red_async$", "9.7.15.8"),
    (r"^multimem_", "9.7.10.15"),
    (r"^mma_sp", "9.7.16.6.3"),
    (r"^barrier_cluster", "9.7.15.3"),
    (r"^bar_warp_sync$", "9.7.15.2"),
    (r"^mbarrier_init$", "9.7.15.16.12"),
    (r"^mbarrier_inval$", "9.7.15.16.13"),
    (r"^mbarrier_expect_tx", "9.7.15.16.14"),
    (r"^mbarrier_complete_tx", "9.7.15.16.15"),
    (r"^mbarrier_arrive_drop", "9.7.15.16.17"),
    (r"^mbarrier_arrive", "9.7.15.16.16"),
    (r"^mbarrier_(test|try)_wait", "9.7.15.16.19"),
    (r"^mbarrier_pending_count$", "9.7.15.16.20"),
    (r"^mbarrier_check_layout$", "9.7.15.16.21"),
    (r"^clusterlaunchcontrol_try_cancel$", "9.7.15.18"),
    (r"^clusterlaunchcontrol_query", "9.7.15.19"),
    (r"^tcgen05_(alloc|dealloc|relinquish)", "9.7.18.7.1"),
    (r"^tcgen05_ld", "9.7.18.8.3"),
    (r"^tcgen05_st", "9.7.18.8.4"),
    (r"^tcgen05_wait$", "9.7.18.8.5"),
    (r"^tcgen05_cp$", "9.7.18.9.2"),
    (r"^tcgen05_mma_ws_sp", "9.7.18.10.10.4"),
    (r"^tcgen05_mma_ws", "9.7.18.10.10.3"),
    (r"^tcgen05_mma_sp", "9.7.18.10.10.2"),
    (r"^tcgen05_mma", "9.7.18.10.10.1"),
    (r"^tcgen05_fence$", "9.7.18.11.1"),
    (r"^tcgen05_commit", "9.7.18.12.1"),
    (r"^fabric_try_get", "9.7.11.5.1"),
    (r"^fabric_try_put", "9.7.11.5.2"),
    (r"^fabric_try_red", "9.7.11.5.3"),
    (r"^fabric_try_pullred", "9.7.11.5.4"),
    (r"^fabric_submit", "9.7.11.5.5"),
    (r"^fabric_wait", "9.7.11.5.6"),
    (r"^wgmma_fence", "9.7.17.7.1"),
    (r"^wgmma_commit_group", "9.7.17.7.2"),
    (r"^wgmma_wait_group", "9.7.17.7.3"),
    (r"^wgmma_", "9.7.17.5.2"),
]

# Section of a mnemonic when no entry pattern above applies, keyed by (family, mnemonic).
MNEMONIC_SECTION = {
    **{
        ("int", m): f"9.7.1.{i}"
        for i, m in enumerate(
            "add sub mul mad clmad mul24 mad24 sad div rem abs neg min max popc clz bfind fns "
            "brev bfe bfi szext bmsk dp4a dp2a".split(),
            1,
        )
    },
    ("int", "selp"): "9.7.7.3",
    ("int", "slct"): "9.7.7.4",
    **{
        ("int", m): f"9.7.9.{i}"
        for i, m in enumerate("and or xor not cnot lop3 shf shl shr".split(), 1)
    },
    **{
        ("float", m): f"9.7.3.{i}"
        for i, m in [
            (1, "testp"),
            (2, "copysign"),
            (3, "add"),
            (4, "sub"),
            (5, "mul"),
            (6, "fma"),
            (13, "rcp"),
            (15, "sqrt"),
            (16, "rsqrt"),
            (18, "sin"),
            (19, "cos"),
            (20, "lg2"),
            (21, "ex2"),
            (22, "tanh"),
        ]
    },
    ("move", "mov"): "9.7.10.3",
    ("warp", "shfl.sync"): "9.7.10.6",
    ("int", "prmt"): "9.7.10.7",
    ("mem", "ld"): "9.7.10.8",
    ("mem", "ldu"): "9.7.10.10",
    ("mem", "st"): "9.7.10.11",
    ("async", "st.async"): "9.7.10.12",
    ("mem", "st.bulk"): "9.7.10.14",
    ("mem", "prefetchu"): "9.7.10.16",
    ("mem", "applypriority"): "9.7.10.17",
    ("mem", "discard"): "9.7.10.20",
    ("misc", "createpolicy"): "9.7.10.21",
    ("mem", "isspacep"): "9.7.10.22",
    ("mem", "cvta"): "9.7.10.23",
    ("cvt", "cvt"): "9.7.10.24",
    ("cvt", "cvt.pack"): "9.7.10.25",
    ("mem", "mapa"): "9.7.10.26",
    ("mem", "getctarank"): "9.7.10.27",
    ("async", "tensormap.replace"): "9.7.10.29",
    ("matrix", "spcompress"): "9.7.10.31",
    ("matrix", "spdecompress"): "9.7.10.32",
    ("barrier", "bar"): "9.7.15.1",
    ("barrier", "barrier"): "9.7.15.1",
    ("fence", "fence"): "9.7.15.4",
    ("mem", "atom"): "9.7.15.5",
    ("mem", "red"): "9.7.15.6",
    ("async", "red.async"): "9.7.15.7",
    ("warp", "vote.sync"): "9.7.15.10",
    ("warp", "match"): "9.7.15.11",
    ("warp", "activemask"): "9.7.15.12",
    ("warp", "redux.sync"): "9.7.15.13",
    ("misc", "griddepcontrol"): "9.7.15.14",
    ("warp", "elect.sync"): "9.7.15.15",
    ("async", "tensormap.cp_fenceproxy"): "9.7.15.17",
    ("matrix", "mma"): "9.7.16.5.14",
    ("matrix", "ldmatrix"): "9.7.16.5.15",
    ("matrix", "stmatrix"): "9.7.16.5.16",
    ("matrix", "movmatrix"): "9.7.16.5.17",
    ("misc", "setmaxnreg"): "9.7.21.5",
}


def _pattern_section(name, mnemonic, template):
    m = re.fullmatch(r"([\d.]+)\{(.*)\}", template)
    if not m:
        return template
    table = dict(kv.split(":") for kv in m.group(2).split(","))
    return m.group(1) + table[mnemonic.split(".")[0]]


def section(e):
    if e.get("section"):
        return e["section"]
    for pattern, template in SECTIONS:
        if re.search(pattern, e["name"]):
            if template is None:
                break
            return _pattern_section(e["name"], e["mnemonic"], template)
    key = (e["family"], e["mnemonic"])
    if key not in MNEMONIC_SECTION:
        raise KeyError(f"{e['name']}: no section for {key}")
    return MNEMONIC_SECTION[key]


def _family(e):
    if e["name"] in ENTRY_FAMILY:
        return ENTRY_FAMILY[e["name"]]
    return MNEMONIC_FAMILY[e["mnemonic"]]


def _effect(e):
    if e["family"] == "ctl":
        return "ctl"
    if e["orders_memory"] or any(op["kind"] == "addr" for op in e["operands"]):
        return "event"
    return "local"


def _split(e):
    slot, classify = SPLITS[e["name"]]
    k = [s[0] for s in e["slots"]].index(slot)
    parts = {}
    for i, v in enumerate(e["variants"]):
        parts.setdefault(classify(v[k]), []).append(i)
    out = []
    for (suffix, family), idx in parts.items():
        piece = dict(e)
        piece["name"] = e["name"] + suffix
        piece["table_name"] = e["name"]
        piece["family"] = family
        piece["variants"] = [e["variants"][i] for i in idx]
        piece["operands"] = [
            {**op, **{key: [op[key][i] for i in idx] for key in ("lanes", "dtype", "sink")}}
            for op in e["operands"]
        ]
        # Drop the tokens of the split slot that no longer occur.
        used = {v[k] for v in piece["variants"]}
        name, choices, optional = e["slots"][k]
        piece["slots"] = list(e["slots"])
        piece["slots"][k] = [name, [c for c in choices if c in used], optional and "" in used]
        if used == {""}:
            # The piece never writes the slot: drop it.
            piece["slots"] = piece["slots"][:k] + piece["slots"][k + 1 :]
            piece["variants"] = [v[:k] + v[k + 1 :] for v in piece["variants"]]
        out.append(piece)
    return out


def entries(table=None):
    table = table or load()
    out = []
    for e in table["entries"]:
        e = dict(e, table_name=e["name"], family=_family(e))
        out.extend(_split(e) if e["name"] in SPLITS else [e])
    extra.apply_extend(out)
    extra.apply_overrides(out)
    out.extend(extra.nomask_siblings(out))
    for e in extra.entries():
        out.append(dict(e, table_name=None, family=_family(e)))
    _merge_aliases(out)
    for e in out:
        e["orders"] = _orders(e)
        e["effect"] = _effect(e)
        e["section"] = section(e)
        e["reason"] = (
            EXCLUDED_REASON.get(e["mnemonic"].split(".")[0]) if e["family"] == "excluded" else None
        )
    return out


def _merge_aliases(out):
    by_name = {e["name"]: e for e in out}
    for alias, canon in ALIASES.items():
        a, c = by_name[alias], by_name[canon]
        a["alias_of"] = canon
        a["family"] = c["family"]
        cnames = [s[0] for s in c["slots"]]
        cidx = {v: i for i, v in enumerate(c["variants"])}
        anames = [s[0] for s in a["slots"]]
        pairs = []
        for i, v in enumerate(a["variants"]):
            mods = dict(zip(anames, v))
            j = cidx.get(tuple(mods.get(n, "") for n in cnames))
            if j is not None:
                pairs.append((i, j))
        for oa, oc in zip(a["operands"], c["operands"], strict=True):
            if any(oa["dtype"][i] != oc["dtype"][j] for i, j in pairs):
                oc["dtype"] = [None] * len(oc["dtype"])
                oc["dtype_varies"] = True


def _orders(e):
    """Alternative slot orders: lists of slot indices in written order."""
    names = [s[0] for s in e["slots"]]
    out = []
    # CUTLASS writes .num and optional .trans before .m8n8 in both matrix moves.
    # Keep the same operand checks and pass slot values back in canonical order.
    if e["name"] in {"ldmatrix", "stmatrix"}:
        order = ("sync", "aligned", "num", "trans", "shape", "space", "type")
        out.append([names.index(slot) for slot in order])
    for a, b in SWAPS:
        if a in names and b in names:
            perm = list(range(len(names)))
            i, j = names.index(a), names.index(b)
            perm[i], perm[j] = perm[j], perm[i]
            out.append(perm)
    return out


def check_aliases(final):
    """Every legal combination of an alias is legal, with the same slot values, for its
    canonical entry, and the operands have the same names and kinds up to pointer/register."""
    errors = []
    by_name = {e["name"]: e for e in final}
    for e in final:
        if not e.get("alias_of"):
            continue
        c = by_name[e["alias_of"]]
        cnames = [s[0] for s in c["slots"]]
        legal = {tuple(zip(cnames, v)) for v in c["variants"]}
        for v in e["variants"]:
            mods = dict(zip([s[0] for s in e["slots"]], v))
            full = tuple((n, mods.get(n, "")) for n in cnames)
            if set(mods) - set(cnames) or full not in legal:
                errors.append(f"{e['name']}: {v} is not a combination of {c['name']}")
                break
        kinds = [(o["name"], o["kind"]) for o in e["operands"]]
        ckinds = [(o["name"], o["kind"]) for o in c["operands"]]
        same = all(
            n1 == n2 and (k1 == k2 or {k1, k2} <= {"reg", "ptr", "var"})
            for (n1, k1), (n2, k2) in zip(kinds, ckinds, strict=True)
        )
        if len(kinds) != len(ckinds) or not same:
            errors.append(f"{e['name']}: operands differ from {c['name']}")
    return errors


def check_partition(table, final):
    """Every legal combination of every table entry lands in exactly one final entry, every
    final entry has one family of `FAMILIES`, and names are unique."""
    errors = []
    names = [e["name"] for e in final]
    if len(set(names)) != len(names):
        errors.append("duplicate entry names")
    seen = {}
    for e in final:
        if e["family"] not in FAMILIES:
            errors.append(f"{e['name']}: unknown family {e['family']}")
        if e["family"] == "excluded" and not e["reason"]:
            errors.append(f"{e['name']}: excluded without a reason")
        if e["table_name"] is None:
            continue
        slots = [s[0] for s in e["slots"]]
        for v in e["variants"]:
            key = (e["table_name"], tuple((s, t) for s, t in zip(slots, v, strict=True) if t))
            if key in seen:
                errors.append(f"{e['name']}: combination {v} also in {seen[key]}")
            seen[key] = e["name"]
    for e in table["entries"]:
        slots = [s[0] for s in e["slots"]]
        for v in e["variants"]:
            if (e["name"], tuple((s, t) for s, t in zip(slots, v, strict=True) if t)) not in seen:
                errors.append(f"{e['name']}: combination {v} has no final entry")
                break
    return errors


def check_sections(final, spec_text):
    """Each entry's section heading in the PTX ISA text names the entry's mnemonic."""
    errors = []
    for e in final:
        sec = e["section"]
        m = re.search(re.escape(sec) + r"\. ([^]{1,160}?) ", spec_text)
        if not m:
            errors.append(f"{e['name']}: no heading {sec}")
            continue
        head = e["mnemonic"].split(".")[0]
        if head not in m.group(1):
            errors.append(f"{e['name']}: heading {sec} '{m.group(1)}' does not name {head}")
    return errors


if __name__ == "__main__":
    t = load()
    f = entries(t)
    errs = check_partition(t, f) + check_aliases(f)
    import collections

    print(collections.Counter(e["family"] for e in f))
    print("\n".join(errs) or "partition ok")
