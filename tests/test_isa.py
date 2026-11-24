# SPDX-License-Identifier: Apache-2.0
"""The generated instruction grammar (`Tools/isa/`, `Core/Source/Isa/`).

* the generated Lean files and `Tests/Source/IsaCrossCheck.lean` are up to date with the vendored table
  and the generator;
* every legal combination of every table entry belongs to exactly one entry and family;
* the cubes and operand fact tables equal the vendored legal combinations and facts;
* the Python grammar recognizes every synthesized instruction as its own entry, rejects the
  illegal neighbours, and recognizes every instruction of the repository's kernels;
* with `TXVERIFY_PTX_SPEC`, the section numbers and the quotes of `extra.py` match the ISA text;
* with `TXVERIFY_BUILD=1`, the Lean grammar agrees with the Python one on the ten kernels.
"""

import os
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
ISA = ROOT / "Tools" / "isa"
SPEC = os.environ.get("TXVERIFY_PTX_SPEC")


@pytest.fixture(scope="module")
def isa():
    sys.path.insert(0, str(ISA))
    sys.path.insert(0, str(ROOT / "Tools"))
    import constraints
    import crosscheck
    import extra
    import families
    import gen_lean
    from load_table import load

    m = crosscheck.prepare(gen_lean.build_model())
    return {
        "m": m,
        "table": load(),
        "families": families,
        "constraints": constraints,
        "crosscheck": crosscheck,
        "extra": extra,
    }


def test_generated_files_are_current():
    res = subprocess.run(
        [sys.executable, str(ISA / "gen_lean.py"), "--check"], capture_output=True, text=True
    )
    assert res.returncode == 0, res.stdout + res.stderr


def test_partition(isa):
    fam = isa["families"]
    assert fam.check_partition(isa["table"], isa["m"].final) == []
    assert fam.check_aliases(isa["m"].final) == []
    excluded = {e["name"] for e in isa["m"].final if e["family"] == "excluded"}
    assert excluded == {e["name"] for e in isa["table"]["entries"] if e["mnemonic"] == "wgmma"}


def test_cubes_and_facts(isa):
    final = [e for e in isa["m"].final if not e.get("alias_of")]
    assert isa["constraints"].verify_all(final) == []


def test_python_grammar(isa):
    cc, m = isa["crosscheck"], isa["m"]
    pos, neg = cc.synthesized(m)
    for name, combo, opcode, ops in pos:
        e = m.by_name[name]
        target = m.by_name[e.get("alias_of") or name]
        mods = dict(zip([s[0] for s in e["slots"]], combo, strict=True))
        r = cc.run(m, opcode, ops)
        assert not isinstance(r, cc.Error), (name, opcode)
        assert (r[0], r[1]) == (
            target["name"],
            [(s[0], mods.get(s[0], "")) for s in target["slots"]],
        ), (name, opcode)
    for name, combo, opcode, ops in neg:
        r = cc.run(m, opcode, ops)
        slots = [s[0] for s in m.by_name[name]["slots"]]
        assert isinstance(r, cc.Error) or (r[0], r[1]) != (name, list(zip(slots, combo))), opcode


def test_review_cases(isa):
    assert isa["crosscheck"].review_failures(isa["m"]) == []


def test_variable_sources_and_const_space(isa):
    by = {e["name"]: e for e in isa["m"].entries}
    kind = lambda n, op: [o["kind"] for o in by[n]["operands"] if o["name"] == op]  # noqa: E731
    # The variable form of `a` needs `.shared::cluster`; without `.space` it is a register.
    assert kind("mapa", "a") == ["var"] and kind("mapa_generic", "a") == ["ptr"]
    assert "space" not in [s[0] for s in by["mapa_generic"]["slots"]]
    assert kind("getctarank", "a") == ["var"] and kind("getctarank_generic", "a") == ["reg"]
    assert kind("mov", "a") == ["regvar"]
    for name in ("ld", "ld_vec"):
        (space,) = [s for s in by[name]["slots"] if s[0] == "space"]
        assert "const" in space[1]


def test_repository_kernels_are_recognized(isa):
    cc, m = isa["crosscheck"], isa["m"]
    for path in cc.corpus_files(False).values():
        for opcode, ops in cc.instructions(path):
            r = cc.run(m, opcode, ops)
            assert not isinstance(r, cc.Error), (path.name, opcode, r)


@pytest.mark.skipif(not SPEC, reason="set TXVERIFY_PTX_SPEC to the PTX ISA text")
def test_sections_and_quotes(isa):
    text = Path(SPEC).read_text()
    assert isa["families"].check_sections(isa["m"].final, text) == []
    norm = " ".join(text.split())
    quotes = [isa["extra"].NOMASK_QUOTE, isa["extra"].LD_SS, isa["extra"].LD_V4_QUOTE]
    quotes += [q for *_, q in isa["extra"].EXTEND]
    quotes += [q for _, q, _ in isa["extra"].OVERRIDES.values()]
    quotes += [e["syntax"] for e in isa["extra"].entries()]
    for q in quotes:
        assert " ".join(q.split()) in norm, q


@pytest.mark.skipif(os.environ.get("TXVERIFY_BUILD") != "1", reason="set TXVERIFY_BUILD=1")
def test_lean_agrees_with_python(tmp_path):
    res = subprocess.run(
        [sys.executable, str(ISA / "crosscheck.py"), "--work", str(tmp_path)],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0, res.stdout[-3000:] + res.stderr[-3000:]
