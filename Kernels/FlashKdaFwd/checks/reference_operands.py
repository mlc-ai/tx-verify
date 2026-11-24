"""Capture the first state coordinate at each upstream fused multiply-add call."""

from contextlib import contextmanager
import sys

import torch
from torch_ref import fp32_fma, torch_ref


def bits(value):
    width = value.element_size()
    raw = value.view(torch.int32 if width == 4 else torch.int16).item()
    return f"0x{raw % (1 << (8 * width)):0{2 * width}x}"


@contextmanager
def record_reference_fma():
    operands = []

    def observe(frame, event, arg):
        if event == "call" and frame.f_code is fp32_fma.__code__:
            if frame.f_back.f_code is torch_ref.__code__:
                operands.append([bits(frame.f_locals[n][0, 0]) for n in ("a", "b", "c")])

    previous = sys.getprofile()
    try:
        sys.setprofile(observe)
        yield operands
    finally:
        sys.setprofile(previous)
