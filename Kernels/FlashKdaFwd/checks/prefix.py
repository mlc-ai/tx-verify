"""Run the prefix entry from the compiled extension binary on the batches checked by Lean."""

import argparse
import ctypes
import hashlib
import json
from pathlib import Path

import torch
from cuda.bindings import driver


def checked(result):
    status, *values = result
    if status != driver.CUresult.CUDA_SUCCESS:
        raise RuntimeError(f"CUDA driver error {status}")
    return values


def run(binary):
    torch.cuda.init()
    stream = torch.cuda.current_stream()
    (module,) = checked(driver.cuModuleLoad(bytes(binary)))
    try:
        (kernel,) = checked(
            driver.cuModuleGetFunction(module, b"_Z28_flash_kda_build_tile_prefixPKliiPi")
        )
        pattern = (0, 1, 15, 16, 17, 31, 32, 33)
        outputs = {}
        for count in [*range(9), 23]:
            totals, expected = [0], [0]
            for i in range(count):
                size = pattern[i % len(pattern)]
                totals.append(totals[-1] + size)
                expected.append(expected[-1] + (size + 15) // 16)
            offsets = torch.tensor(totals, device="cuda", dtype=torch.int64)
            output = torch.full((count + 3,), -7, device="cuda", dtype=torch.int32)
            # The output pointer skips a sentinel on either side of the actual prefix array.
            args = (
                (offsets.data_ptr(), count, 16, output[1:].data_ptr()),
                (ctypes.c_void_p, ctypes.c_int, ctypes.c_int, ctypes.c_void_p),
            )
            checked(
                driver.cuLaunchKernel(kernel, 1, 1, 1, 32, 1, 1, 0, stream.cuda_stream, args, 0)
            )
            assert output.tolist() == [-7, *expected, -7]
            assert offsets.tolist() == totals
            outputs[count] = expected
        with binary.open("rb") as source:
            digest = hashlib.file_digest(source, "sha256").hexdigest()
        return dict(device=torch.cuda.get_device_name(), binary_sha256=digest, prefixes=outputs)
    finally:
        checked(driver.cuModuleUnload(module))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    print(json.dumps(run(parser.parse_args().binary), indent=2))
