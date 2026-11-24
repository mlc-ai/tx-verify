# SPDX-License-Identifier: Apache-2.0
"""Tools/step_gen.py: one step lemma per local instruction, and the freshness of its outputs."""

import importlib
import json
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "Tools"
DECLS = sorted((ROOT / "Tests" / "Gen" / "Step").glob("*.json")) + sorted(
    ROOT.glob("Kernels/*/Gen/Step/*.json")
)


@pytest.fixture(scope="module")
def sg():
    sys.path.insert(0, str(TOOLS))
    return importlib.import_module("step_gen")


@pytest.mark.parametrize("path", DECLS, ids=lambda p: str(p.relative_to(ROOT)))
def test_generated_steps_are_fresh(path):
    r = subprocess.run(
        [sys.executable, str(TOOLS / "step_gen.py"), str(path), "--check"],
        capture_output=True,
        text=True,
    )
    assert r.returncode == 0, r.stdout + r.stderr


def test_selection(sg):
    ins = "{ guard := none, op := PTX.Op.int { op := PTX.IntOp.add, srcs := [PTX.Opnd.reg 1] } }"
    assert sg.selected(ins)
    assert sg.selected(ins.replace("guard := none", "guard := some (3, false)"))
    assert not sg.selected(ins.replace("PTX.Opnd.reg 1", "PTX.Opnd.sreg (PTX.SReg.clock)"))
    assert sg.selected("{ guard := some (15, false), op := PTX.Op.bra 12 false }")
    assert not sg.selected("{ guard := none, op := PTX.Op.mbarWait 1 2 }")
    assert sg.selected("{ guard := none, op := PTX.Op.float { op := PTX.FOp.mul } }")
    assert sg.selected(
        "{ guard := none, op := PTX.Op.mem { kind := PTX.MemKind.load, "
        "space := some (PTX.StateSpace.param), sem := PTX.Sem.weak } }"
    )


def test_lemmas(sg):
    decl = json.loads((ROOT / "Tests" / "Gen" / "Step" / "flashmla_index.json").read_text())
    files = sg.generate(dict(decl, ranges=[[2356, 2360]]), ROOT)
    text = "\n".join(files.values())
    # every pc, the guarded branch 2357 included, is proved from its code lemma
    assert "theorem step_2357 " in text and "PcLocal.of_code code_2357 rfl" in text
    assert "theorem step_2356 " in text and "PcLocal.of_code code_2356 rfl" in text
    # an excluded pc has no lemma
    files = sg.generate(dict(decl, ranges=[[2356, 2360]], exclude=[2356]), ROOT)
    assert "theorem step_2356 " not in "\n".join(files.values())
