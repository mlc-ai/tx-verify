# SPDX-License-Identifier: Apache-2.0
"""Instruction entries the TIRx table does not have, in the decoded form of `load_table.load()`.

Each entry quotes its syntax line verbatim from PTX ISA 9.5 (`syntax`) and names its section.
The entries have no cross-slot check: their legal combinations are the whole slot product.

* `ld_param`, `ld_param_vec`: `ld` from the `.param` state space (`.param`, `.param::entry`,
  `.param::func`, with an optional `.weak`), which the table leaves out. `.v4` with a 64-bit
  element is excluded: the ISA supports it only in the global space. The address operand is `[p]`, `[p+imm]`, `[r]` or `[r+imm]` like any address operand
  (§6.4.1); which of these a family accepts is decided by the family layer.
* `tcgen05_shift`: `tcgen05.shift`, which the table leaves out, in the qualifier order of its
  syntax line (§9.7.18.9.3).
* `membar`: the old-style thread fence `membar.level`, which the table leaves out; it orders
  memory like the table's `fence` entries.
* `fence_proxy_sem`: the bi-directional proxy fence with a scope and an optional `.sem`
  (`fence.proxy.proxykind{.sem}.scope`), which the table leaves out; only `.async` takes a state
  space, as in the table's `fence_proxy`.
* `add_cc`, `addc`, `sub_cc`, `subc`, `mad_cc`, `madc`: the extended-precision instructions
  (§9.7.2), which the table leaves out.
* `nanosleep`, `pmevent`: the miscellaneous instructions of §9.7.21.2 and §9.7.21.3, which the
  table leaves out.
* `bra`, `brx_idx`, `ret`, `exit`, `trap`: control flow. The operand kind `label` is used only
  here: `bra`'s target and `brx.idx`'s `tlist` are labels.

Corrections of table entries, each with the sentence of the PTX ISA that requires it:

* `EXTEND`: a slot token the table lacks, added as a copy of the legal combinations with
  another token (the `.u32` size of `cvta` and `mapa`, the `.const` space of `ld` (with the
  combinations of `.local`), and
  `cp.async.bulk.wait_group.sync_restrict::proxy::async`).
* `OVERRIDES`: operand facts or kinds that differ from the table (`elect.sync`'s `d` may be `_`,
  and either destination of `match.all.sync d|p` may be `_`;
  the source of `cvta.space`, of `mapa.shared::cluster` and of `getctarank.shared::cluster` may
  be a variable `var` or `var+imm`, operand kind `var`; the source of `mov` may also be a
  variable with an optional offset, operand kind `regvar`, which accepts everything a `reg`
  source accepts and `var+imm`). `mapa` without `.space` is the separate entry `mapa_generic`,
  whose source is a register: "When the optional qualifier .space is not specified, both a and
  d are registers containing generic addresses pointing to shared memory."
* `nomask_siblings`: every `tcgen05.mma` entry with a `disable-output-lane` vector gets a
  sibling `<name>_nomask` without it, the form of the ISA's examples, and every `tcgen05.mma.ws`
  entry a sibling `<name>_nozcm` without the optional `zero-column-mask-desc`.
"""

import itertools

# ld's `.type` list (§9.7.10.8); the vector forms exclude `.b128` as the table's ld_vec does.
LD_TYPES = [
    "b8",
    "b16",
    "b32",
    "b64",
    "b128",
    "u8",
    "u16",
    "u32",
    "u64",
    "s8",
    "s16",
    "s32",
    "s64",
    "f32",
    "f64",
]
LD_VEC_TYPES = [t for t in LD_TYPES if t != "b128"]
# `.param{::entry, ::func}` of ld's `.ss`.
LD_PARAM_SPACES = ["param", "param::entry", "param::func"]

LD_SYNTAX = (
    "ld{.weak}{.ss}{.cop}{.level::cache_hint}{.level::prefetch_size}{.vec}.type d, [a]"
    "{.unified}{, cache_policy};"
)
LD_SS = ".ss = { .const, .global, .local, .param{::entry, ::func}, .shared{::cta, ::cluster} };"


def _operand(name, kind, rw="r", group=False, space=None):
    return {
        "name": name,
        "kind": kind,
        "rw": rw,
        "space": space,
        "literal": None,
        "choices": None,
        "bracket": None,
        "pipe": None,
        "group": group,
        "imm_offset": kind == "addr",
    }


def _entry(name, mnemonic, slots, operands, facts, syntax, section, quotes=(), legal=None):
    """`facts(op_name, mods) -> (dtype, lanes)` for every operand and legal combination; the
    legal combinations are the slot product filtered by `legal(mods)` when given."""
    axes = [[*choices, ""] if optional else list(choices) for _, choices, optional in slots]
    names = [s[0] for s in slots]
    variants = [v for v in itertools.product(*axes) if legal is None or legal(dict(zip(names, v)))]
    for op in operands:
        cols = [facts(op["name"], dict(zip([s[0] for s in slots], v))) for v in variants]
        op["dtype"] = [c[0] for c in cols]
        op["lanes"] = [c[1] for c in cols]
        op["sink"] = [False for _ in cols]
    return {
        "name": name,
        "mnemonic": mnemonic,
        "cert_arch": None,
        "orders_memory": False,
        "check": "",
        "slots": slots,
        "operands": operands,
        "variants": variants,
        "syntax": syntax,
        "quotes": list(quotes),
        "section": section,
        "extra": True,
    }


def _ld_facts(name, m):
    if name == "d":
        return (m["type"], {"v2": 2, "v4": 4}.get(m.get("vec", ""), 1))
    return (None, 1)


SETP_SINK_QUOTE = "The sink symbol ‘_’ may be used in place of any one of the destination operands."

# (entry, operand) -> facts or operand fields replacing the table's, with the sentence that
# requires them.
OVERRIDES = {
    ("elect_sync", "d"): (
        {"sink": True},
        "The sink symbol ‘_’ can be used for destination operand d .",
        "9.7.15.15",
    ),
    ("cvta_generic", "a"): (
        {"kind": "var"},
        "cvta.space.size p, var+imm; // generic address of var+offset",
        "9.7.10.23",
    ),
    ("mapa", "a"): (
        {"kind": "var"},
        "mapa.shared::cluster.type d, sh + imm, b;",
        "9.7.10.26",
    ),
    ("getctarank", "a"): (
        {"kind": "var"},
        "getctarank.shared::cluster.type d, var + imm;",
        "9.7.10.27",
    ),
    ("setp_pq_int", "p"): ({"sink": True}, SETP_SINK_QUOTE, "9.7.7.2"),
    ("setp_pq_int", "q"): ({"sink": True}, SETP_SINK_QUOTE, "9.7.7.2"),
    ("setp_bool_pq_int", "p"): ({"sink": True}, SETP_SINK_QUOTE, "9.7.7.2"),
    ("setp_bool_pq_int", "q"): ({"sink": True}, SETP_SINK_QUOTE, "9.7.7.2"),
    ("setp_pq_f", "p"): ({"sink": True}, SETP_SINK_QUOTE, "9.7.7.2"),
    ("setp_pq_f", "q"): ({"sink": True}, SETP_SINK_QUOTE, "9.7.7.2"),
    ("setp_bool_pq_f", "p"): ({"sink": True}, SETP_SINK_QUOTE, "9.7.7.2"),
    ("setp_bool_pq_f", "q"): ({"sink": True}, SETP_SINK_QUOTE, "9.7.7.2"),
    ("match_all_sync_p", "d"): ({"sink": True}, SETP_SINK_QUOTE, "9.7.15.11"),
    ("match_all_sync_p", "p"): ({"sink": True}, SETP_SINK_QUOTE, "9.7.15.11"),
    ("mov", "a"): (
        {"kind": "regvar"},
        "mov.type d, avar+imm; // get address of variable with offset",
        "9.7.10.3",
    ),
}

# (entry, slot, existing token, added token, quote): every legal combination with the existing
# token is copied with the added one; an operand type equal to the existing token becomes the
# added one.
EXTEND = [
    ("cvta", "type", "u64", "u32", ".size = { .u32, .u64 };"),
    ("cvta_generic", "type", "u64", "u32", ".size = { .u32, .u64 };"),
    ("mapa", "type", "u64", "u32", ".type = { .u32, .u64 }"),
    ("mapa_generic", "type", "u64", "u32", ".type = { .u32, .u64 }"),
    # `.const` is decoded with the combinations of `.local`: the ISA states no modifier for the
    # space beyond the list of `.ss`, and the modifiers of `.local` are the ones that every state
    # space accepts.
    ("ld", "space", "local", "const", LD_SS),
    ("ld_vec", "space", "local", "const", LD_SS),
    # The slot is the table's `read` slot of cp.async.bulk.wait_group.
    (
        "cp_async_bulk_wait_group",
        "read",
        "read",
        "sync_restrict::proxy::async",
        "cp.async.bulk.wait_group.sync_restrict::proxy::async N;",
    ),
]

LD_V4_QUOTE = (
    "The .v4 ( .vec ) qualifier with type .b64 or .s64 or .u64 or .f64 is supported if: State "
    "space is .global or with generic addressing where address points to .global state space"
)


def apply_extend(entries_):
    """Apply `EXTEND` in place."""
    by_name = {e["name"]: e for e in entries_}
    for name, slot, old, new, quote in EXTEND:
        e = by_name[name]
        k = [s[0] for s in e["slots"]].index(slot)
        e["slots"] = [list(x) for x in e["slots"]]
        if new in e["slots"][k][1]:
            raise ValueError(f"{name}.{slot} already has {new}")
        e["slots"][k][1] = [*e["slots"][k][1], new]
        idx = [i for i, v in enumerate(e["variants"]) if v[k] == old]
        e["variants"] = list(e["variants"]) + [
            e["variants"][i][:k] + (new,) + e["variants"][i][k + 1 :] for i in idx
        ]
        e["operands"] = [dict(op) for op in e["operands"]]
        for op in e["operands"]:
            op["lanes"] = op["lanes"] + [op["lanes"][i] for i in idx]
            op["sink"] = op["sink"] + [op["sink"][i] for i in idx]
            op["dtype"] = op["dtype"] + [
                new if op["dtype"][i] == old else op["dtype"][i] for i in idx
            ]
        e.setdefault("quotes", []).append(quote)


NOMASK_QUOTE = "tcgen05.mma.cta_group::1.kind::f16 [taddr0], a-desc, b-desc, idesc, p;"


def apply_overrides(entries_):
    """Apply `OVERRIDES` in place; every override must name an existing operand."""
    by_name = {e["name"]: e for e in entries_}
    for (name, opname), (facts, quote, section) in OVERRIDES.items():
        e = by_name[name]
        (op,) = [o for o in e["operands"] if o["name"] == opname]
        for k, v in facts.items():
            op[k] = [v] * len(e["variants"]) if k in ("lanes", "dtype", "sink") else v
        e.setdefault("quotes", []).append(quote)


WS_QUOTE = (
    "tcgen05.mma.ws.cta_group::1.kind{.collector_usage} [d-tmem], a-desc, b-desc, idesc, "
    "enable-input-d {, zero-column-mask-desc };"
)

# Operands the ISA lets an instruction omit although the table requires them: (operand, name
# suffix of the sibling without it, quote).
DROPPABLE = [
    ("disable_output_lane", "_nomask", NOMASK_QUOTE),
    ("zero_col_mask", "_nozcm", WS_QUOTE),
]


def nomask_siblings(entries_):
    """For every `DROPPABLE` operand, a sibling `<name><suffix>` of every entry that has it,
    without it (siblings of siblings included, so the operands are dropped independently),
    unless an entry with that spelling exists (the ti16 `.ws` entries come in both forms)."""
    out = []
    for opname, suffix, quote in DROPPABLE:
        for e in list(entries_) + out:
            if not any(o["name"] == opname for o in e["operands"]):
                continue
            sib = dict(e)
            sib["name"] = e["name"] + suffix
            sib["operands"] = [o for o in e["operands"] if o["name"] != opname]
            sib["quotes"] = [*e.get("quotes", []), quote] if e.get("derived_from") else [quote]
            sib["derived_from"] = e["name"]
            sib["table_name"] = None
            if not any(_covers(x, sib) for x in list(entries_) + out):
                out.append(sib)
    return out


def _covers(x, e):
    """Whether entry `x` already has the spelling of `e`: the same mnemonic, slots and operand
    names, and every legal combination of `e`."""
    return (
        x["mnemonic"] == e["mnemonic"]
        and [s[0] for s in x["slots"]] == [s[0] for s in e["slots"]]
        and [o["name"] for o in x["operands"]] == [o["name"] for o in e["operands"]]
        and set(e["variants"]) <= set(x["variants"])
    )


# The `.type` of the extended-precision instructions (§9.7.2).
CC_TYPES = ["u32", "s32", "u64", "s64"]
CC_TYPE_QUOTE = ".type = { .u32, .s32, .u64, .s64 };"


def _carry_entries():
    """`add.cc`, `addc`, `sub.cc`, `subc`, `mad.cc` and `madc` (§9.7.2). `.cc` is written on
    `add.cc`, `sub.cc` and `mad.cc` and optional on the others; the `.hi`/`.lo` mode of `mad.cc`
    and `madc` is required, since their Semantics sections define only those two variants."""

    def facts(n, m):
        return (m["type"], 1)

    def ops(names):
        return [_operand("d", "reg", "w")] + [_operand(n, "reg") for n in names]

    mode = ["mode", ["hi", "lo"], False]
    typ = ["type", CC_TYPES, False]
    return [
        _entry(name, mn, slots, ops(srcs), facts, syntax, sec, [CC_TYPE_QUOTE])
        for name, mn, slots, srcs, syntax, sec in [
            (
                "add_cc",
                "add",
                [["cc", ["cc"], False], typ],
                "ab",
                "add.cc.type d, a, b;",
                "9.7.2.1",
            ),
            (
                "addc",
                "addc",
                [["cc", ["cc"], True], typ],
                "ab",
                "addc{.cc}.type d, a, b;",
                "9.7.2.2",
            ),
            (
                "sub_cc",
                "sub",
                [["cc", ["cc"], False], typ],
                "ab",
                "sub.cc.type d, a, b;",
                "9.7.2.3",
            ),
            (
                "subc",
                "subc",
                [["cc", ["cc"], True], typ],
                "ab",
                "subc{.cc}.type d, a, b;",
                "9.7.2.4",
            ),
            (
                "mad_cc",
                "mad",
                [mode, ["cc", ["cc"], False], typ],
                "abc",
                "mad{.hi,.lo}.cc.type d, a, b, c;",
                "9.7.2.5",
            ),
            (
                "madc",
                "madc",
                [mode, ["cc", ["cc"], True], typ],
                "abc",
                "madc{.hi,.lo}{.cc}.type d, a, b, c;",
                "9.7.2.6",
            ),
        ]
    ]


def entries():
    return [
        _entry(
            "ld_param",
            "ld",
            [
                ["weak", ["weak"], True],
                ["space", LD_PARAM_SPACES, False],
                ["type", LD_TYPES, False],
            ],
            [_operand("d", "reg", "w"), _operand("a", "addr", space="param")],
            _ld_facts,
            LD_SYNTAX,
            "9.7.10.8",
            [LD_SS],
        ),
        _entry(
            "ld_param_vec",
            "ld",
            [
                ["weak", ["weak"], True],
                ["space", LD_PARAM_SPACES, False],
                ["vec", ["v2", "v4"], False],
                ["type", LD_VEC_TYPES, False],
            ],
            [_operand("d", "reg", "w", group=True), _operand("a", "addr", space="param")],
            _ld_facts,
            LD_SYNTAX,
            "9.7.10.8",
            [LD_SS, LD_V4_QUOTE],
            legal=lambda m: not (m["vec"] == "v4" and m["type"] in ("b64", "s64", "u64", "f64")),
        ),
        _entry(
            "bra",
            "bra",
            [["uni", ["uni"], True]],
            [_operand("tgt", "label")],
            lambda n, m: (None, 1),
            "bra{.uni} tgt; // unconditional branch",
            "9.7.14.3",
        ),
        _entry(
            "brx_idx",
            "brx.idx",
            [["uni", ["uni"], True]],
            [_operand("index", "reg"), _operand("tlist", "label")],
            lambda n, m: ("u32" if n == "index" else None, 1),
            "brx.idx{.uni} index, tlist;",
            "9.7.14.4",
            ["The index operand is a .u32 register."],
        ),
        *_carry_entries(),
        _entry(
            "nanosleep",
            "nanosleep",
            [["type", ["u32"], False]],
            [_operand("t", "reg")],
            lambda n, m: ("u32", 1),
            "nanosleep.u32 t;",
            "9.7.21.2",
            ["t may be a register or an immediate value."],
        ),
        _entry(
            "pmevent",
            "pmevent",
            [["mask", ["mask"], True]],
            [_operand("a", "imm")],
            lambda n, m: (None, 1),
            "pmevent.mask a; // trigger one or more performance monitor events",
            "9.7.21.3",
            ["pmevent a; // trigger a single performance monitor event"],
        ),
        {
            **_entry(
                "membar",
                "membar",
                [["level", ["cta", "gl", "sys"], False]],
                [],
                None,
                "membar.level;",
                "9.7.15.4",
                [".level = { .cta, .gl, .sys };"],
            ),
            "orders_memory": True,
        },
        {
            **_entry(
                "fence_proxy_sem",
                "fence",
                [
                    ["proxy", ["proxy"], False],
                    ["proxykind", ["alias", "async"], False],
                    ["space", ["global", "shared::cta", "shared::cluster"], True],
                    ["sem", ["sc", "acq_rel", "acquire", "release"], True],
                    ["scope", ["cta", "cluster", "gpu", "sys"], False],
                ],
                [],
                None,
                "fence.proxy.proxykind{.sem}.scope;",
                "9.7.15.4",
                [
                    ".sem = { .sc, .acq_rel, .acquire, .release };",
                    ".scope = { .cta, .cluster, .gpu, .sys };",
                    ".proxykind = { .alias, .async, .async.global, .async.shared::{cta, cluster} };",
                ],
                legal=lambda m: m["space"] == "" or m["proxykind"] == "async",
            ),
            "orders_memory": True,
        },
        _entry("ret", "ret", [["uni", ["uni"], True]], [], None, "ret{.uni};", "9.7.14.6"),
        _entry("exit", "exit", [], [], None, "Syntax exit;", "9.7.14.7"),
        _entry("trap", "trap", [], [], None, "Syntax trap;", "9.7.21.4"),
        _entry(
            "tcgen05_shift",
            "tcgen05",
            [
                ["action", ["shift"], False],
                ["cta_group", ["cta_group::1", "cta_group::2"], False],
                ["shift_dir", ["down"], False],
            ],
            [_operand("taddr", "addr", space="tmem")],
            lambda n, m: (None, 1),
            "tcgen05.shift.cta_group.down [taddr];",
            "9.7.18.9.3",
            [".cta_group = { .cta_group::1, .cta_group::2 }"],
        ),
    ]
