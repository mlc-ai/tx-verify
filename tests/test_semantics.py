# SPDX-License-Identifier: Apache-2.0
"""Checks for the PTX semantics and kernel proofs."""

import importlib
import importlib.util
import os
import re
import shutil
import subprocess
from pathlib import Path

import pytest

EXAMPLE = Path(__file__).resolve().parents[1]
# Kernel directory -> PTX file. Each directory also holds the generated `Ptx.lean`.
KERNELS = {
    "CopyDynamic": "copy_dynamic",
    "CopyLdg": "copy_ldg",
    "RowSum": "row_sum",
    "BlockSum": "block_sum",
    "RmsNorm": "rmsnorm",
    "TmaCopy": "tma_copy",
    "TcGemm": "tc_gemm",
    "Fp16Gemm8192": "fp16_gemm_8192",
    "FlashAttn4Fwd": "flash_fwd_sm100",
    "AddOne": "add_one",
    "FlashMlaSparseDecodeH64": "v41_h64_no_split_plain",
    "InklingRelDecode": "rel_verify_sm100a",
    "TmlFa4Fwd": "full_p16_s1",
    "FlashKdaFwd": "packed_fp32_sm100a",
}
# Kernels compiled from CUDA in this directory (rmsnorm comes from tirx-kernels; see
# Kernels/RmsNorm/gen_ptx.py).
CUDA = ["CopyDynamic", "CopyLdg", "RowSum", "BlockSum"]


@pytest.fixture
def exporter(monkeypatch):
    monkeypatch.syspath_prepend(str(EXAMPLE / "Tools"))
    return importlib.import_module("export_lean")


def _instructions(text):
    """PTX lines without comments and license header."""
    return [ln for ln in text.splitlines() if ln and not ln.startswith(("//", " *", "/*"))]


@pytest.mark.parametrize("kernel", sorted(KERNELS))
def test_generated_lean_is_fresh(exporter, kernel):
    folder = EXAMPLE / "Kernels" / kernel
    fresh = exporter.export(
        (folder / f"{KERNELS[kernel]}.ptx").read_text(), f"PTX.Generated.{kernel}"
    )
    assert fresh == (folder / "Ptx.lean").read_text()


@pytest.mark.parametrize("kernel", CUDA)
def test_ptx_matches_nvcc(tmp_path, kernel):
    nvcc = shutil.which("nvcc")
    if nvcc is None:
        pytest.skip("nvcc unavailable")
    folder = EXAMPLE / "Kernels" / kernel
    name = KERNELS[kernel]
    out = tmp_path / f"{name}.ptx"
    subprocess.run(
        [
            nvcc,
            "-ptx",
            "-O3",
            "-arch=sm_100a",
            str(folder / f"{name}.cu"),
            "-o",
            str(out),
        ],
        check=True,
    )
    assert _instructions(out.read_text()) == _instructions((folder / f"{name}.ptx").read_text())


@pytest.mark.parametrize("kernel", ["TmaCopy", "TcGemm", "AddOne"])
def test_hand_written_ptx_assembles(tmp_path, kernel):
    ptxas = shutil.which("ptxas")
    if ptxas is None:
        pytest.skip("ptxas unavailable")
    name = KERNELS[kernel]
    ptx = EXAMPLE / "Kernels" / kernel / f"{name}.ptx"
    out = tmp_path / f"{name}.cubin"
    subprocess.run([ptxas, "-arch=sm_100a", str(ptx), "-o", str(out)], check=True)


def test_contract_index_is_fresh():
    result = subprocess.run(
        ["python", str(EXAMPLE / "Tools" / "contract_index.py"), "--check"],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


@pytest.fixture
def contract_index(monkeypatch):
    monkeypatch.syspath_prepend(str(EXAMPLE / "Tools"))
    return importlib.import_module("contract_index")


def test_index_preserves_manual_text(contract_index):
    before = "Manual introduction.\n\n"
    after = "\n\nManual conclusion.\n"
    old = before + contract_index.BEGIN + "\nstale index\n" + contract_index.END + after
    new = contract_index.replace_index(old, "fresh index\n")
    assert new == before + contract_index.BEGIN + "\nfresh index\n" + contract_index.END + after
    assert contract_index.replace_index(new, "fresh index\n") == new


@pytest.mark.parametrize(
    "markers",
    [
        [],
        ["begin"],
        ["end"],
        ["end", "begin"],
        ["begin", "begin", "end"],
        ["begin", "end", "end"],
    ],
)
def test_index_rejects_bad_markers(contract_index, markers):
    text = "\n".join(contract_index.BEGIN if m == "begin" else contract_index.END for m in markers)
    with pytest.raises(ValueError):
        contract_index.replace_index(text, "index")


def test_index_check_rejects_stale_without_writing(contract_index, monkeypatch, tmp_path):
    root = tmp_path / "project"
    (root / "Core").mkdir(parents=True)
    path = root / "Core/README.md"
    old = contract_index.BEGIN + "\nstale\n" + contract_index.END
    path.write_text(old)
    monkeypatch.setattr(contract_index, "ROOT", root)
    monkeypatch.setattr(contract_index, "render", lambda layout=False: "fresh\n")
    monkeypatch.setattr("sys.argv", ["contract_index.py", "--check"])
    with pytest.raises(SystemExit, match="index is stale"):
        contract_index.main()
    assert path.read_text() == old
    monkeypatch.setattr("sys.argv", ["contract_index.py"])
    contract_index.main()
    assert path.read_text() == contract_index.replace_index(old, "fresh\n")
    monkeypatch.setattr("sys.argv", ["contract_index.py", "--check"])
    contract_index.main()


def test_index_keeps_wrapped_source(contract_index):
    entry = "/-! ## EXAMPLE — example\nDefs: f\nSource: first\n  second\nDirection: equal\n-/"
    assert next(contract_index.sections(entry))[2]["Source"] == "first second"


@pytest.mark.skipif(not os.environ.get("TXVERIFY_BUILD"), reason="set TXVERIFY_BUILD=1 (slow)")
def test_lake_build_checks_all_proofs():
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("lake unavailable")
    result = subprocess.run([lake, "--wfail", "build"], cwd=EXAMPLE, capture_output=True, text=True)
    assert result.returncode == 0, result.stdout + result.stderr
    assert "sorry" not in result.stdout


@pytest.fixture
def production_validation(monkeypatch):
    monkeypatch.syspath_prepend(str(EXAMPLE / "Tools"))
    path = EXAMPLE / "Kernels/Fp16Gemm8192/Scripts/validate.py"
    spec = importlib.util.spec_from_file_location("production_validation", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_production_ptx_identity(production_validation):
    folder = EXAMPLE / "Kernels/Fp16Gemm8192"
    source = (folder / "fp16_gemm_8192.ptx").read_text()
    production_validation.check_same_program(source, source)
    # nvcc's unused C++ globals contain a temporary-module hash.
    tag = re.search(r"[0-9a-f]{8}_14_tvm_kernels_cu_[0-9a-f]{8}", source)
    assert tag is not None
    renamed = source.replace(tag.group(), "01234567_14_tvm_kernels_cu_89abcdef")
    assert renamed != source
    production_validation.check_same_program(source, renamed)
    # Never allow an instruction change to hide behind that normalization.
    changed = source.replace("mbarrier.init.shared.b64", "mbarrier.inval.shared.b64", 1)
    assert changed != source
    with pytest.raises(AssertionError, match="instructions"):
        production_validation.check_same_program(source, changed)


def test_production_manifest(production_validation):
    if not (EXAMPLE.parent / "tirx-kernels").exists():
        pytest.skip("production source checkout unavailable")
    production_validation.check_frozen(EXAMPLE.parent)


def test_production_tensor_maps(production_validation):
    """The manifest's recorded encoder arguments are the Lean tensor maps."""
    import json

    folder = EXAMPLE / "Kernels/Fp16Gemm8192"
    manifest = json.loads((folder / "Data/manifest.json").read_text())
    production_validation.check_tensor_maps(manifest)
    assert sorted(manifest["tensor_maps"]) == ["a", "b", "d"]
    # Any changed encoding argument is rejected, for every operand.
    for name, field, value in [
        ("a", "box", [128, 128]),
        ("b", "swizzle", 2),
        ("d", "global_strides", [8192]),
        ("d", "oob_fill", 1),
    ]:
        changed = json.loads(json.dumps(manifest))
        changed["tensor_maps"][name][field] = value
        with pytest.raises(AssertionError, match="tensor map"):
            production_validation.check_tensor_maps(changed)


FLOW = {
    "TmaCopy": "tma_copy",
    "Fp16Gemm8192": "fp16_gemm_8192",
    "CopyDynamic": "copy_dynamic",
    "CopyLdg": "copy_ldg",
    "RowSum": "row_sum",
    "BlockSum": "block_sum",
    "TcGemm": "tc_gemm",
    "RmsNorm": "rmsnorm",
    "AddOne": "add_one",
    "FlashAttn4Fwd": "flash_fwd_sm100",
    "FlashMlaSparseDecodeH64": "v41_h64_no_split_plain",
    "InklingRelDecode": "rel_verify_sm100a",
    "TmlFa4Fwd": "full_p16_s1",
    "FlashKdaFwd": "packed_fp32_sm100a",
}


@pytest.mark.parametrize("kernel", sorted(KERNELS))
def test_flow_generator_runs(kernel):
    """The flow generator reads every kernel's PTX; branch targets match the decoder."""
    spec = importlib.util.spec_from_file_location("flow_gen", EXAMPLE / "Tools" / "flow_gen.py")
    flow_gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(flow_gen)
    lean, flow = flow_gen.generate(
        EXAMPLE / "Kernels" / kernel / f"{KERNELS[kernel]}.ptx",
        f"PTX.Kernels.{kernel}.Flow",
    )
    assert "abbrev" in "".join(lean.values()) and '"sites"' in flow


@pytest.mark.parametrize("kernel", sorted(KERNELS.keys() - {"TmlFa4Fwd"}))
def test_every_loop_has_a_site(kernel):
    """Every back edge's loop contains an event site, so local runs between sites are
    straight-line segments for the other kernels."""
    spec = importlib.util.spec_from_file_location("flow_gen", EXAMPLE / "Tools" / "flow_gen.py")
    flow_gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(flow_gen)
    program = flow_gen.parse_ptx.parse(
        (EXAMPLE / "Kernels" / kernel / f"{KERNELS[kernel]}.ptx").read_text()
    )
    function = next(f for f in program.functions if not f.declaration)
    assert flow_gen.local_loops(flow_gen.flatten(function)) == []


def test_brx_idx_edges():
    """`brx.idx` reads its index and has one edge per table entry, taken when the index equals
    the entry's position; an index at or beyond the table's length is an unsafe path."""
    spec = importlib.util.spec_from_file_location("flow_gen", EXAMPLE / "Tools" / "flow_gen.py")
    flow_gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(flow_gen)
    ptx = """
.version 9.2
.target sm_100a
.address_size 64
.visible .entry k()
.reqntid 32
{
	.reg .b32 %r<4>;
	ld.global.b32 %r1, [%r0];
	$L_t: .branchtargets
		$L_a,
		$L_b;
	brx.idx %r1, $L_t;
$L_a:
	st.global.b32 [%r0], %r1;
	ret;
$L_b:
	ret;
}
"""
    function = next(f for f in flow_gen.parse_ptx.parse(ptx).functions if not f.declaration)
    code = flow_gen.flatten(function)
    brx = code[1]
    assert brx["opcode"] == "brx.idx"
    assert brx["table"] == [2, 4] and brx["reads"] == ["%r1"] and brx["writes"] == []
    assert flow_gen.successors(brx, len(code)) == [
        (2, ("%r1", ["eq", 0])),
        (4, ("%r1", ["eq", 1])),
    ]
    paths = flow_gen.paths_from(code, 1)
    assert sorted((p["to"] or -1, "unsafe" in p) for p in paths) == [
        (-1, True),
        (2, False),
        (4, False),
    ]
    unsafe = next(p for p in paths if "unsafe" in p)
    assert unsafe["conditions"] == [["%r1", ["ge", 2], 1]]


def test_tmlfa4_local_loop_and_async_sites():
    spec = importlib.util.spec_from_file_location("flow_gen", EXAMPLE / "Tools" / "flow_gen.py")
    flow_gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(flow_gen)
    import json

    ptx = EXAMPLE / "Kernels" / "TmlFa4Fwd" / "full_p16_s1.ptx"
    _, flow = flow_gen.generate(ptx, "PTX.Kernels.TmlFa4Fwd.Flow")
    flow = json.loads(flow)
    assert flow["instructions"] == 9206
    assert len(flow["local_loops"]) == 1
    loop = flow["local_loops"][0]
    assert (loop["entry"], loop["backedge"], loop["exit"]) == (398, 401, 402)
    assert any(path["to"] == loop["name"] and path["length"] == 4 for path in loop["next"])
    assert any(path["to"] != loop["name"] for path in loop["next"])
    assert sum(s["name"].startswith("asyncCopy_") for s in flow["sites"]) == 192
    assert sum(s["name"].startswith("asyncCommit_") for s in flow["sites"]) == 6
    assert sum(s["name"].startswith("asyncArrive_") for s in flow["sites"]) == 6
    assert any(s["opcode"].startswith("ld.local.") for s in flow["sites"])


CODE_TABLE = [
    "Fp16Gemm8192",
    "TmaCopy",
    "CopyDynamic",
    "CopyLdg",
    "RowSum",
    "BlockSum",
    "TcGemm",
    "RmsNorm",
    "AddOne",
    "FlashAttn4Fwd",
    "FlashMlaSparseDecodeH64",
    "InklingRelDecode",
    "TmlFa4Fwd",
    "FlashKdaFwd",
]
# Kernels whose lookups are stated over the decoder cache (`Data/Decoded.lean`) instead of
# `Spec.lean`, so that the specification can change without rebuilding the tables.
CODE_OVER_DECODED = {"TmlFa4Fwd", "FlashKdaFwd"}


@pytest.mark.parametrize("kernel", CODE_TABLE)
def test_code_table_is_fresh(kernel):
    """The instruction lookups of the site machines match the decoded program."""
    folder = EXAMPLE / "Kernels" / kernel
    decoded = folder / "Data" / "Decoded.lean"
    if not decoded.exists():
        decoded = folder / "Spec.lean"
    slices = kernel == "TmlFa4Fwd"
    cache = kernel in CODE_OVER_DECODED
    kernel_ref = f"PTX.Kernels.{kernel}" + (".Decoded.kernel" if cache else ".kernel")
    import_module = f"Kernels.{kernel}" + (".Data.Decoded" if cache else ".Spec")
    result = subprocess.run(
        [
            "python3",
            str(EXAMPLE / "Tools" / "code_table.py"),
            str(decoded),
            str(folder / "Flow" / "flow.json"),
            "--namespace",
            f"PTX.Kernels.{kernel}.Flow",
            "--kernel",
            kernel_ref,
            "--spec",
            import_module,
            "-o",
            str(folder / "Flow" / "Code.lean"),
            "--check",
            *(["--slices"] if slices else []),
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


# Kernels whose flow also lists the instructions that perform an event only in the Core model
# (`flow_gen.generate(core_events=True)`).
CORE_EVENT_FLOWS = {"FlashKdaFwd"}


@pytest.mark.parametrize("kernel", sorted(FLOW))
def test_flow_is_fresh(kernel):
    folder = EXAMPLE / "Kernels" / kernel
    result = subprocess.run(
        [
            "python3",
            str(EXAMPLE / "Tools" / "flow_gen.py"),
            str(folder / f"{FLOW[kernel]}.ptx"),
            "--namespace",
            f"PTX.Kernels.{kernel}.Flow",
            "-o",
            str(folder / "Flow"),
            "--check",
            *(["--core-events"] if kernel in CORE_EVENT_FLOWS else []),
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


# The decoder caches: the entry function each kernel's `Data/Decoded.lean` is decoded from.
DECODED = {
    "AddOne": "add_one",
    "BlockSum": "block_sum",
    "CopyDynamic": "copy_dynamic",
    "CopyLdg": "copy_ldg",
    "RowSum": "row_sum",
    "TmaCopy": "tma_copy",
    "TcGemm": "tc_gemm",
    "RmsNorm": "rmsnorm_kernel",
    "Fp16Gemm8192": "gemm_kernel",
    "InklingRelDecode": "_rel_verify_kernel",
    "FlashAttn4Fwd": "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100"
    "FlashAttentionForwardSm100_object_at__tensor0000o11101213_tensor0000o11101213"
    "_tensor0000o10111213_tensor0000o11101213_None_None_None_Non_0",
    "FlashMlaSparseDecodeH64": "_ZN5sm1006decode6sparse6head6439flash_fwd_splitkv_mla_fp8_sparse_kernelINS2_14Ke"
    "rnelTemplateIXtlNS2_6ConfigEL9ModelType0ELS6_0ELb0EEEEENS7_9TmaParamsIN4cute5tup"
    "leIJiiiiEEENS9_9TiledCopyINS9_9Copy_AtomIJNS9_11Copy_TraitsINS9_13SM90_TMA_LOADE"
    "JNS9_1CILi65536EEENS9_12AuxTmaParamsINSA_IJNS9_11ScaledBasisINSG_ILi1EEEJLi1EEEE"
    "NSJ_ISK_JLi0EEEENSJ_ISK_JLi2EEEENSJ_ISK_JLi3EEEEEEERKNS9_6LayoutINSA_IJNSG_ILi64"
    "EEESR_SK_SK_EEESP_EERKNS9_7SwizzleILi3ELi4ELi3EEEEEEEEN7cutlass10bfloat16_tEEEEN"
    "SQ_INSA_IJSK_NSA_IJNSA_IJNSA_IJSR_SR_EEENSG_ILi8EEEEEEEEEEEENSA_IJNSG_ILi0EEENSA"
    "_IJNSA_IJNSA_IJSR_SK_EEENSG_ILi4096EEEEEEEEEEEEEENSA_IJSR_NSG_ILi512EEEEEEEESB_N"
    "SC_INSD_IJNSE_INS9_14SM90_TMA_STOREEJSH_S10_EEES13_EEENSQ_INSA_IJSK_NSA_IJNSA_IJ"
    "S15_SK_EEEEEEEEENSA_IJS1A_NSA_IJNSA_IJS1B_S1A_EEEEEEEEEEES15_EEEEEEv22SparseAttn"
    "DecodeParamsT0_",
    "TmlFa4Fwd": "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100"
    "FlashAttentionForwardSm100_object_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81"
    "i64div8i64div8_tensorptrbf16gmemalign16o1i64div8_0",
    "FlashKdaFwd": "_Z25_flash_kda_fwd_recurrenceIN4cute9TiledCopyINS0_9Copy_AtomIJNS0_11Copy_Traits"
    "INS0_13SM90_TMA_LOADEJNS0_1CILi2048EEENS0_12AuxTmaParamsINS0_5tupleIJNS0_11Scale"
    "dBasisINS5_ILi1EEEJLi2EEEENS9_ISA_JLi1EEEENS9_IiJLi0EEEEEEERKNS0_6LayoutINS8_IJN"
    "S5_ILi8EEENS5_ILi16EEESA_EEENS8_IJSB_SC_NS9_ISA_JLi0EEEEEEEEERKNS0_7SwizzleILi0E"
    "Li4ELi3EEEEEEEEN7cutlass10bfloat16_tEEEENSF_INS8_IJSA_NS8_IJNS8_IJNS8_IJSG_SH_EE"
    "ESH_EEEEEEEEENS8_IJNS5_ILi0EEENS8_IJNS8_IJNS8_IJSH_SA_EEENS5_ILi128EEEEEEEEEEEEE"
    "ENS8_IJSA_SH_S13_EEEEENS1_INS2_IJNS3_IS4_JNS5_ILi512EEENS7_INS8_IJSJ_EEERKNSF_IN"
    "S8_IJNS5_ILi32EEEEEES1B_EESR_EEEEESV_EEENSF_INS8_IJSA_NS8_IJNS8_IJS1C_SA_EEEEEEE"
    "EENS8_IJS11_NS8_IJNS8_IJSA_S11_EEEEEEEEEEES1D_EENS1_INS2_IJNS3_IS4_JS6_NS7_ISK_S"
    "N_SR_EEEEESV_EEES17_S18_EES1V_S1V_NS1_INS2_IJNS3_IS4_JNS5_ILi4096EEENS7_INS8_IJS"
    "C_SJ_EEERKNSF_INS8_IJS13_SA_EEES1X_EESR_EEEEEfEEENSF_INS8_IJSA_NS8_IJS1Y_EEEEEES"
    "1P_EENS8_IJSA_S13_EEEEENS1_IS1U_NSF_INS8_IJSA_NS8_IJNS8_IJSX_NS5_ILi2EEEEEEEEEEE"
    "ES16_EENS8_IJSA_SH_SH_EEEEES2G_NS1_INS2_IJNS3_IS4_JNS5_ILi32768EEENS7_ISK_RKNSF_"
    "INS8_IJSG_S13_SA_EEESK_EERKNSO_ILi1ELi4ELi3EEEEEEEEfEEENSF_INS8_IJSA_NS8_IJNS8_I"
    "JNS8_IJSG_S13_EEESH_EEEEEEEEENS8_IJS11_NS8_IJNS8_IJS1Y_NS5_ILi1024EEEEEEEEEEEEEE"
    "NS8_IJSA_S13_S13_EEEEENS1_INS2_IJNS3_INS0_14SM90_TMA_STOREEJS2H_S2P_EEEfEEES30_S"
    "31_EENS1_INS2_IJNS3_IS33_JS6_SS_EEESV_EEES17_S18_EELi16ELi128ELi3ELi2ELi192ELb1E"
    "Lb1ELb1ELb1EEvT_T0_T1_T2_T3_T4_T5_T6_T7_T8_T9_PSV_iiiPKli",
}


@pytest.mark.skipif(not os.environ.get("TXVERIFY_BUILD"), reason="set TXVERIFY_BUILD=1 (slow)")
@pytest.mark.parametrize("kernel", sorted(DECODED))
def test_decoded_is_fresh(kernel):
    """A program cache is the Core decoder's output, register ids included."""
    if shutil.which("lake") is None:
        pytest.skip("lake unavailable")
    result = subprocess.run(
        [
            "python3",
            str(EXAMPLE / "Tools" / "export_decoded.py"),
            "--ptx-module",
            f"Kernels.{kernel}.Ptx",
            "--function",
            f"PTX.Generated.{kernel}.{DECODED[kernel]}",
            "--globals",
            f"PTX.Generated.{kernel}.module.globals",
            "--namespace",
            f"PTX.Kernels.{kernel}.Decoded",
            "-o",
            str(EXAMPLE / "Kernels" / kernel / "Data" / "Decoded.lean"),
            "--check",
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


@pytest.mark.skipif(not os.environ.get("TXVERIFY_BUILD"), reason="set TXVERIFY_BUILD=1 (slow)")
@pytest.mark.parametrize("kernel", ["FlashAttn4Fwd", "TmlFa4Fwd"])
def test_decode_chunks_are_fresh(kernel):
    """The chunked `decode_eq` files match the decoded programs."""
    result = subprocess.run(
        ["python3", str(EXAMPLE / "Tools" / "decode_chunks.py"), "--kernel", kernel, "--check"],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


@pytest.mark.skipif(not os.environ.get("TXVERIFY_BUILD"), reason="set TXVERIFY_BUILD=1 (slow)")
def test_flashmla_regeneration_is_fresh():
    """The FlashMLA regeneration command verifies all generated files from the frozen PTX."""
    if shutil.which("lake") is None:
        pytest.skip("lake unavailable")
    result = subprocess.run(
        [
            "python3",
            str(EXAMPLE / "Kernels" / "FlashMlaSparseDecodeH64" / "regenerate.py"),
            "--check",
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


@pytest.mark.skipif(not os.environ.get("TXVERIFY_BUILD"), reason="set TXVERIFY_BUILD=1 (slow)")
def test_flashkda_regeneration_is_fresh():
    """The FlashKDA regeneration command verifies all generated files from the frozen PTX: the
    exported module, the decoder cache, the chunked decode audit, the flow and the code
    lookups."""
    if shutil.which("lake") is None:
        pytest.skip("lake unavailable")
    result = subprocess.run(
        [
            "python3",
            str(EXAMPLE / "Kernels" / "FlashKdaFwd" / "regenerate.py"),
            "--check",
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_flashkda_thread_layer_is_fresh():
    """The generated thread machine of the FlashKDA kernel (`Proof/Thread`) is the output of
    its generator on the frozen flow."""
    result = subprocess.run(
        [
            "python3",
            str(EXAMPLE / "Kernels" / "FlashKdaFwd" / "Gen" / "thread.py"),
            "--check",
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_flashkda_matrix_table_is_fresh():
    """The register table of the FlashKDA tile loop and the generated `Math/FragmentsTable.lean`
    are the output of their script on the frozen PTX (the script also re-runs its checks of the
    table against a symbolic run of the tile loop)."""
    result = subprocess.run(
        [
            "python3",
            str(EXAMPLE / "Kernels" / "FlashKdaFwd" / "Gen" / "matrix_table.py"),
            "--check",
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


@pytest.mark.skipif(not os.environ.get("TXVERIFY_BUILD"), reason="set TXVERIFY_BUILD=1 (slow)")
def test_decode_chunks_are_fresh_inkling():
    """The chunked Inkling relative decode `decode_eq` files match the decoded program."""
    result = subprocess.run(
        [
            "python3",
            str(EXAMPLE / "Tools" / "decode_chunks.py"),
            "--kernel",
            "InklingRelDecode",
            "--code-chunk",
            "256",
            "--no-heartbeats",
            "--header-literal",
            "--check",
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr
