# SPDX-License-Identifier: Apache-2.0
"""Tools/value_table.py: value-table entries of the floating registers a segment writes."""

import importlib
import json
from pathlib import Path

import pytest

TOOLS = Path(__file__).resolve().parents[1] / "Tools"

HEADER = """.version 8.7
.target sm_100a
.address_size 64

.visible .entry vt(
\t.param .u64 vt_param_0
)
{
\t.reg .pred \t%p<3>;
\t.reg .b32 \t%r<20>;
\t.reg .b64 \t%rd<10>;

\tld.param.u64 \t%rd7, [vt_param_0];
"""

FOOTER = """\tst.global.u32 \t[%rd7], %r8;
\tret;
}
"""

BODY = """\tmov.b64 \t%rd1, {%r1, %r2};
\tfma.rn.f32x2 \t%rd2, %rd1, %rd3, %rd4;
\tmov.b64 \t{%r3, %r4}, %rd2;
\tmax.f32 \t%r5, %r3, %r4, %r1;
\tadd.f32 \t%r6, %r5, %r2;
\tsub.f32 \t%r7, %r5, %r2;
\tcvt.rn.f16x2.f32 \t%r8, %r6, %r7;
\tsetp.gt.f32 \t%p1, %r6, %r7;
\tmin.f32 \t%r11, %r6, %r1;
"""

INPUTS = {
    "%r1": {"real": "a"},
    "%r2": {"real": "b"},
    "%rd3": {"pair": [{"real": "c"}, {"real": "d"}]},
    "%rd4": {"pair": [{"real": "e"}, {"real": "f"}]},
    "%rd7": {"value": "b64 0"},
}


@pytest.fixture
def vt(monkeypatch):
    monkeypatch.syspath_prepend(str(TOOLS))
    return importlib.import_module("value_table")


def run(vt, tmp_path, body, inputs=INPUTS, preds=None, templates=None, all_written=False):
    ptx = tmp_path / "vt.ptx"
    ptx.write_text(HEADER + body + FOOTER)
    return vt.generate(
        ptx, "pc:1", "store_0", inputs, preds or {}, templates or {}, all_written
    ).splitlines()


def test_live_entries(vt, tmp_path):
    # only %r8 is live at the store; %r1 is %r<20> id 3 + 1, %p ids come first
    assert run(vt, tmp_path, BODY) == [
        "  (11, .pair (.float .f16 ((max (max (a * c + e) (b * d + f)) a) - b)) "
        "(.float .f16 ((max (max (a * c + e) (b * d + f)) a) + b))),  -- %r8"
    ]


def test_all_written(vt, tmp_path):
    lines = run(vt, tmp_path, BODY, all_written=True)
    by_name = {line.rsplit("-- ", 1)[1]: line for line in lines}
    assert by_name["%rd1"] == "  (24, .pair (.float .f32 (a)) (.float .f32 (b))),  -- %rd1"
    assert ".float .f32 (a * c + e)" in by_name["%r3"]
    assert ".float .f32 (b * d + f)" in by_name["%r4"]
    assert "Assumption.realCompare .gt" in by_name["%p1"]
    assert ".float .f32 (min ((max (max (a * c + e) (b * d + f)) a) + b) a)" in by_name["%r11"]


def test_no_template(vt, tmp_path):
    body = "\tex2.approx.ftz.f32 \t%r8, %r1;\n"
    with pytest.raises(vt.TableError, match="no template for ex2.approx.ftz.f32"):
        run(vt, tmp_path, body)
    tmpl = {"ex2.approx.ftz.f32": {"fmt": "f32", "real": "2 ^ {0}"}}
    assert run(vt, tmp_path, body, templates=tmpl) == ["  (11, .float .f32 (2 ^ a)),  -- %r8"]


def test_directed_rounding_has_no_rule(vt, tmp_path):
    body = "\tadd.rm.f32x2 \t%rd1, %rd3, %rd4;\n\tmov.b64 \t{%r8, %r9}, %rd1;\n"
    with pytest.raises(vt.TableError, match="directed rounding"):
        run(vt, tmp_path, body)


def test_guard_needs_predicate(vt, tmp_path):
    body = "\t@%p2 add.f32 \t%r8, %r1, %r2;\n"
    with pytest.raises(vt.TableError, match="guard %p2"):
        run(vt, tmp_path, body)
    assert run(vt, tmp_path, body, preds={"%p2": True}) == ["  (11, .float .f32 (a + b)),  -- %r8"]
    assert run(vt, tmp_path, body, preds={"%p2": False}) == []


def test_missing_input(vt, tmp_path):
    inputs = {k: v for k, v in INPUTS.items() if k != "%r2"}
    with pytest.raises(vt.TableError, match="no start value for %r2"):
        run(vt, tmp_path, BODY, inputs=inputs)


def test_cli(vt, tmp_path, capsys):
    ptx = tmp_path / "vt.ptx"
    ptx.write_text(HEADER + BODY + FOOTER)
    inputs = tmp_path / "in.json"
    inputs.write_text(json.dumps(INPUTS))
    args = [str(ptx), "--start", "pc:1", "--end", "store_0", "--inputs", str(inputs)]
    assert vt.main(args) == 0
    assert capsys.readouterr().out.startswith("  (11, .pair")
    assert vt.main([*args, "--pred", "x"]) == 1
    assert "expected NAME=true" in capsys.readouterr().err
