# SPDX-License-Identifier: Apache-2.0
"""Check frozen production provenance and, optionally, execute it on a B200.

The numerical comparison is the production module's cuBLAS tolerance check. It is
runtime evidence, separate from the proved ideal-real Lean theorem.
"""

import argparse
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import re
import sys

FOLDER = Path(__file__).resolve().parents[1]
ROOT = FOLDER.parents[1]
sys.path.insert(0, str(ROOT / "Tools"))
from parse_ptx import parse  # noqa: E402


def check_frozen(workspace):
    manifest = json.loads((FOLDER / "Data/manifest.json").read_text())
    source_bytes = (FOLDER / "fp16_gemm_8192.ptx").read_bytes()
    assert hashlib.sha256(source_bytes).hexdigest() == manifest["ptx_sha256"]
    source = source_bytes.decode()
    alignment = manifest["shared_alignment"]
    assert alignment == 1024
    assert f".extern .shared .align {alignment} .b8 v_ptr[];" in source
    spec = (FOLDER / "Spec.lean").read_text()
    assert f"sharedAlignment : L.sharedBase % {alignment} = 0" in spec
    for name, digest in manifest.items():
        if name.endswith(".py"):
            path = workspace / name
            assert path.is_file(), f"Missing production source: {path}"
            assert hashlib.sha256(path.read_bytes()).hexdigest() == digest, name
    check_tensor_maps(manifest)
    return manifest, source


SWIZZLE = {"none": 0, "b32": 1, "b64": 2, "b128": 3}
FORMAT = {"f16": "float16", "bf16": "bfloat16"}
LEAN_MAP = re.compile(
    r"def map(?P<name>[ABD]) \(base : Nat\) \(cls : AllocationClass\) : Descriptor 1 :=\s*"
    r"encodeTiled \.(?P<format>\w+) base (?P<inner>\d+) (?P<outer>\d+) (?P<stride>\d+) "
    r"(?P<box0>\d+) (?P<box1>\d+) \.(?P<swizzle>\w+) cls"
)


def lean_tensor_maps():
    """The tensor maps stated in TensorMaps.lean, as encoder arguments."""
    text = (FOLDER / "Data/TensorMaps.lean").read_text()
    # encodeTiled fixes unit element strides, no interleave and zero OOB fill.
    assert "box := ⟨fun i => if i.val = 0 then boxInner else boxOuter, fun _ => 1⟩" in text
    assert "fill := .zero" in text
    maps = {}
    for m in LEAN_MAP.finditer(text):
        maps[m["name"].lower()] = {
            "dtype": FORMAT[m["format"]],
            "rank": 2,
            "global_shape": [int(m["inner"]), int(m["outer"])],
            "global_strides": [int(m["stride"])],
            "box": [int(m["box0"]), int(m["box1"])],
            "element_strides": [1, 1],
            "interleave": 0,
            "swizzle": SWIZZLE[m["swizzle"]],
            "oob_fill": 0,
        }
    assert sorted(maps) == ["a", "b", "d"], "TensorMaps.lean must define mapA, mapB and mapD"
    return maps


def check_tensor_maps(manifest):
    """The recorded host encoder arguments are the descriptors the Lean model uses.

    L2 promotion is a cache hint without memory-model effect and is not compared."""
    lean = lean_tensor_maps()
    for name, recorded in manifest["tensor_maps"].items():
        stated = lean[name]
        relevant = {k: v for k, v in recorded.items() if k != "l2_promotion"}
        assert relevant == stated, f"tensor map {name}: manifest {relevant} != Lean {stated}"


def encode_independently(call):
    """Encode the recorded arguments with the driver directly; return the 128 bytes."""
    import ctypes

    cuda = ctypes.CDLL("libcuda.so.1")
    encode = cuda.cuTensorMapEncodeTiled
    u32, u64 = ctypes.c_uint32, ctypes.c_uint64
    encode.argtypes = [ctypes.c_void_p, ctypes.c_int, u32, ctypes.c_void_p,
                       ctypes.POINTER(u64), ctypes.POINTER(u64), ctypes.POINTER(u32),
                       ctypes.POINTER(u32), ctypes.c_int, ctypes.c_int, ctypes.c_int,
                       ctypes.c_int]  # fmt: skip
    rank = call["rank"]
    storage = (ctypes.c_ubyte * 192)()
    address = (ctypes.addressof(storage) + 63) // 64 * 64
    data_type = {"float16": 6, "bfloat16": 9}[call["dtype"]]
    result = encode(
        address, data_type, rank, call["global_address"],
        (u64 * rank)(*call["global_shape"]), (u64 * (rank - 1))(*call["global_strides"]),
        (u32 * rank)(*call["box"]), (u32 * rank)(*call["element_strides"]),
        call["interleave"], call["swizzle"], call["l2_promotion"], call["oob_fill"],
    )  # fmt: skip
    assert result == 0, f"cuTensorMapEncodeTiled failed with {result}"
    return ctypes.string_at(address, 128)


def check_same_program(frozen, fresh):
    """Compare every directive, function and declaration, modulo unused C++ tags."""
    left, right = parse(frozen), parse(fresh)
    assert left.directives == right.directives, "PTX directives changed"
    assert left.functions == right.functions, "Kernel instructions or metadata changed"

    def declarations(program):
        functions = json.dumps([asdict(f) for f in program.functions])
        result = []
        for declaration in program.globals:
            if (
                len(declaration) == 8
                and declaration[:4] == [".global", ".align", "1", ".b8"]
                and declaration[5:] == ["[", "1", "]"]
            ):
                name = declaration[4]
                renamed = re.sub(
                    r"_ZN45_INTERNAL_[0-9a-f]+_14_tvm_kernels_cu_[0-9a-f]+",
                    "_ZN45_INTERNAL_MODULE",
                    name,
                )
                if renamed != name:
                    assert name not in functions, "Referenced global cannot be renamed"
                    declaration = declaration[:4] + [renamed] + declaration[5:]
            result.append(declaration)
        return result

    assert declarations(left) == declarations(right), "Module declarations changed"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, default=ROOT.parent)
    parser.add_argument("--gpu", action="store_true", help="Compile, compare PTX and run")
    parser.add_argument("--device", type=int, default=0)
    parser.add_argument("--seeds", type=int, nargs="+", default=[0, 1, 2])
    parser.add_argument(
        "--launches",
        type=int,
        default=4,
        help="Asynchronous launches per seed, with independent poisoned outputs",
    )
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    if args.launches < 1:
        parser.error("--launches must be positive")
    manifest, frozen = check_frozen(args.workspace)
    report = {
        "frozen_sources": "passed",
        "ptx_sha256": manifest["ptx_sha256"],
        "proof_status": manifest["proof_status"],
    }
    if args.gpu:
        import torch
        from gen_ptx import TensorMapRecorder, compile_production, encoding_arguments
        from tirx_kernels.gemm.fp16_bf16_gemm import prepare_data

        torch.cuda.set_device(args.device)
        assert torch.cuda.get_device_capability() == (10, 0), "Expected SM100"
        executable, fresh = compile_production()
        check_same_program(frozen, fresh)
        recorder = TensorMapRecorder()
        report.update(
            device=torch.cuda.get_device_name(),
            regenerated_program="passed",
            fresh_ptx_sha256=hashlib.sha256(fresh.encode()).hexdigest(),
            reference="torch.matmul(A, B.T)",
            rtol=0.001,
            atol=0.01,
            runs=[],
        )
        for seed in args.seeds:
            torch.manual_seed(seed)
            a, b, output = prepare_data("fp16", 8192, 8192, 8192)
            outputs = [output] + [torch.empty_like(output) for _ in range(args.launches - 1)]
            for target in outputs:
                # A sentinel exposes unwritten tiles; output is not an input.
                target.fill_(float("nan"))
                recorder.calls.clear()
                executable(a, b, target)
                # Check each launch's real host descriptors before the next call.
                assert encoding_arguments(recorder.calls, (a, b, target)) == manifest["tensor_maps"]
                for call in recorder.calls:
                    assert call["bytes"] == encode_independently(call), "tensor map bytes differ"
            torch.cuda.synchronize()
            reference = torch.matmul(a, b.T)
            for target in outputs:
                torch.testing.assert_close(target, reference, rtol=0.001, atol=0.01)
            report["runs"].append(
                {
                    "seed": seed,
                    "status": "passed",
                    "tensor_maps": "matched",
                    "asynchronous_launches": args.launches,
                    "max_abs_error": max(
                        (target - reference).abs().max().item() for target in outputs
                    ),
                }
            )
            del a, b, output, outputs, target, reference
    text = json.dumps(report, indent=2) + "\n"
    if args.report:
        args.report.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
