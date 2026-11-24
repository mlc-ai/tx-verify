# FlashKDA packed forward recurrence

The selected entry processes a batch of variable-length sequences at head dimension 128.
Each thread block reads one FP32 initial state, processes that sequence and head in tiles of
16 tokens, writes each live output row, and writes the final FP32 state. The preceding
preparation kernel supplies the workspace. Its implementation is outside this single-entry target.

The [PTX](packed_fp32_sm100a.ptx) contains only this entry and its shared memory declaration.
It has 3,835 instructions and no debug directives or comments. The [manifest](manifest.json)
identifies the compiler, source, specialization and file fingerprints. Assembling the selected
entry with the upstream assembler flags gives the same 72,064 machine-code bytes in its text
section as assembling the complete compiler module.

[Sequence.lean](Sequence.lean) proves the real block algorithm agrees with the independent
token recurrence at every output and the outgoing state for every length. The end-to-end
theorem for the compiled entry, from launch and initialized memory to the global writes,
is in progress.

## Reproduction

Build the public extension from the pinned source and its CUTLASS submodule with CUDA 13.2.51.
Use the upstream compiler command for `csrc/smxx/fwd_launch.cu` with the `sm_100a` target,
remove `-lineinfo`, and retain the PTX with `--keep`. The selector checks the function name,
the entire parsed body, the module directives and the shared memory declaration.

```sh
kda=Kernels/FlashKdaFwd
python3 "$kda/checks/select_packed.py" /path/to/fwd_launch.ptx /tmp/packed.ptx
cmp "$kda/packed_fp32_sm100a.ptx" /tmp/packed.ptx
ptxas -arch=sm_100a -m64 --register-usage-level=10 --warn-on-spills /tmp/packed.ptx -o /tmp/packed.cubin
python3 Tools/export_lean.py /tmp/packed.ptx --namespace PTX.Generated.FlashKdaPacked -o /tmp/packed.lean
cmp "$kda/Packed/Ptx.lean" /tmp/packed.lean
```

[StateMap.lean](Packed/StateMap.lean) checks the final state tensor map for every sequence and head.
Each of the 16 transfers covers eight keys in every value row of the 128-by-128 state.
