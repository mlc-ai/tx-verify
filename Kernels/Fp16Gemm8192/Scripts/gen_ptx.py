# SPDX-License-Identifier: Apache-2.0
"""Compile the unmodified production 8192-square FP16 kernel to sm_100a PTX.

Run with the workspace's TVM/TIRx environment. No kernel configuration overrides,
source rewriting or synchronization changes are performed here.
"""

import argparse
import ctypes
import json
from pathlib import Path

from tirx_kernels.gemm import fp16_bf16_gemm
from tirx_kernels.runner import compile_kernel


def compile_production():
    """Return the executable and its exact device PTX, using production dispatch."""
    config = {"cuda": {"arch": "sm_100a", "compiler": "nvcc", "target_format": "ptx"}}
    kernel = fp16_bf16_gemm.get_kernel("fp16", 8192, 8192, 8192, backend_config=config)
    executable = compile_kernel(kernel, backend_config=config)
    pending = [executable.mod]
    sources = []
    while pending:
        module = pending.pop()
        if module.kind == "cuda":
            sources.append(module.inspect_source("ptx"))
        pending.extend(module.imports)
    if len(sources) != 1:
        raise RuntimeError(f"Expected one CUDA module, found {len(sources)}")
    return executable, sources[0]


ENCODER = "runtime.cuTensorMapEncodeTiled"
OPERANDS = ("a", "b", "d")


class TensorMapRecorder:
    """Record every `cuTensorMapEncodeTiled` call the production host code makes.

    The host module looks the encoder up by name on its first call, so installing this
    wrapper before the first launch observes the real calls. Each record keeps the
    arguments and the 128 bytes the driver wrote, which the host then passes by value.
    """

    def __init__(self):
        import tvm_ffi

        self.original = tvm_ffi.get_global_func(ENCODER)
        self.calls = []

        def wrapper(*args):
            result = self.original(*args)
            rank = args[2]
            values = [int(v) for v in args[4:]]
            self.calls.append(
                {
                    "map": args[0].value,
                    "dtype": str(args[1]),
                    "rank": rank,
                    "global_address": args[3].value,
                    "global_shape": values[:rank],
                    "global_strides": values[rank : 2 * rank - 1],
                    "box": values[2 * rank - 1 : 3 * rank - 1],
                    "element_strides": values[3 * rank - 1 : 4 * rank - 1],
                    "interleave": values[4 * rank - 1],
                    "swizzle": values[4 * rank],
                    "l2_promotion": values[4 * rank + 1],
                    "oob_fill": values[4 * rank + 2],
                    "bytes": ctypes.string_at(args[0].value, 128),
                }
            )
            return result

        tvm_ffi.register_global_func(ENCODER, wrapper, override=True)


def encoding_arguments(calls, tensors):
    """The encoder arguments per operand, with addresses replaced by operand names."""
    names = {tensor.data_ptr(): name for name, tensor in zip(OPERANDS, tensors)}
    result = {}
    for call in calls:
        entry = {k: v for k, v in call.items() if k not in ("map", "bytes", "global_address")}
        result[names[call["global_address"]]] = entry
    return result


def record_tensor_maps():
    """Run the production kernel once and return its tensor-map encoder arguments."""
    import torch
    from tirx_kernels.gemm.fp16_bf16_gemm import prepare_data

    executable, _ = compile_production()
    recorder = TensorMapRecorder()
    a, b, output = prepare_data("fp16", 8192, 8192, 8192)
    executable(a, b, output)
    torch.cuda.synchronize()
    return encoding_arguments(recorder.calls, (a, b, output))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("-o", "--output", type=Path)
    parser.add_argument(
        "--tensor-maps",
        type=Path,
        help="Record the host's tensor-map encoder arguments into this manifest (needs a GPU)",
    )
    args = parser.parse_args()
    if args.output:
        _, source = compile_production()
        args.output.write_text(source)
    if args.tensor_maps:
        manifest = json.loads(args.tensor_maps.read_text())
        manifest["tensor_maps"] = record_tensor_maps()
        args.tensor_maps.write_text(json.dumps(manifest, indent=2) + "\n")


if __name__ == "__main__":
    main()
