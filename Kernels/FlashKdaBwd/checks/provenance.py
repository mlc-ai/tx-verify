# SPDX-License-Identifier: Apache-2.0
"""Pin the FLA implementation used by the numerical checks."""

import subprocess
from pathlib import Path

import fla
import torch
import triton

COMMIT = "7cecb9233b2331f725585d0f868a541f1a478388"


def environment():
    checkout = Path(fla.__file__).resolve().parent.parent
    commit = subprocess.check_output(
        ["git", "-C", checkout, "rev-parse", "HEAD"], text=True
    ).strip()
    subprocess.run(["git", "-C", checkout, "diff", "--quiet", "HEAD", "--", "fla"], check=True)
    if commit != COMMIT:
        raise ValueError(f"Expected FLA {COMMIT}, loaded {commit}")
    return dict(
        fla_commit=commit,
        device=torch.cuda.get_device_name(),
        torch=str(torch.__version__),
        triton_base_version=triton.__version__.split("+", 1)[0],
    )
