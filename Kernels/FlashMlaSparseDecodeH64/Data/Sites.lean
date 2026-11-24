-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Data.Decoded

@[expose] public section

/-!
# Instruction sites of the FlashMLA sparse decode head64 kernel

The program is `Decoded.kernel.code`: 3612 instructions (`Decoded.code_length`) decoded from
`v41_h64_no_split_plain.ptx`. Every list below holds pcs, its `…_eq` theorem proves that the
list is exactly the filter over the decoded code that selects the instruction form the list
names, and the doc comment gives the PTX lines and the count. `Assumptions.lean` and the proof
layer name these lists instead of repeating pc arithmetic.

The pc lists were cross-checked against the PTX text, pc by pc, with the line numbers in the
comments; for example `ncLoads` are the 17 `ld.global.nc` instructions of PTX lines 328, 343,
360, 3674, 3687, 4243, 4256, 4518, 4526, 4567, 4598, 4686, 4707, 4805, 4813, 4841 and 4854.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64

open PTX

/-- The pcs of the instructions whose decoded operation satisfies `f`, in source order. -/
def sites (f : Op → Bool) : List Nat :=
  (Decoded.kernel.code.zipIdx.filter fun p => f p.1.op).map (·.2)

/-- The instruction at pc `n`, if the pc is in range. Typed, so that a `match` on it can use
the structure patterns of `Instr` and `Op`. -/
def codeAt (n : Nat) : Option Instr := Decoded.kernel.code[n]?

/-! ## Global loads and tensor copies -/

/-- A non-coherent global load (`ld.global.nc`); `.nc` is the `nc` flag of `MemAccess`. -/
def isNcLoad : Op → Bool
  | .mem a => a.nc
  | _ => false

/-- The 17 `ld.global.nc` loads (PTX 328, 343, 360, 3674, 3687, 4243, 4256, 4518, 4526, 4567,
4598, 4686, 4707, 4805, 4813, 4841, 4854) of `topk_length`, `extra_topk_length`, `seq_lens`,
the scale and sink words, and the sparse index arrays. The kernel writes none of these
addresses, which is the `Assumption.ncReadOnly` site list. -/
def ncLoads : List Nat :=
  [156, 168, 181, 1876, 1886, 2181, 2191, 2360, 2365, 2403, 2429, 2501, 2517, 2596, 2601, 2620,
    2630]

/-- `ncLoads` are exactly the kernel's `.nc` loads. -/
theorem ncLoads_eq : ncLoads = sites isNcLoad := by
  decide +kernel

/-- A global-to-shared tensor copy, of either mode. -/
def isCpTensor : Op → Bool
  | .cpTensor .. => true
  | _ => false

/-- A four-dimensional `.tile` global-to-shared tensor copy. -/
def isTileTensor : Op → Bool
  | .cpTensor _ _ _ _ _ _ _ _ _ .tile _ => true
  | _ => false

/-- A `.2d.tile::gather4` global-to-shared copy of four arbitrary rows. -/
def isGather4Tensor : Op → Bool
  | .cpTensor _ _ _ _ _ _ _ _ _ .fourRows _ => true
  | _ => false

/-- The 8 `cp.async.bulk.tensor.4d.shared::cluster.global` loads (PTX 3714, 3719, 3724, 3729,
3734, 3739, 3744, 3749), all with four coordinates, map register 3058 (`param_1 + 128`, the Q
descriptor) and barrier register 811. -/
def cpTensorLoads : List Nat := [1906, 1909, 1912, 1915, 1918, 1921, 1924, 1927]

/-- `cpTensorLoads` are exactly the kernel's 4-D `.tile` loads. -/
theorem cpTensorLoads_eq : cpTensorLoads = sites isTileTensor := by
  decide +kernel

/-- The 16 `cp.async.bulk.tensor.2d.shared::cta.global.tile::gather4` loads (PTX 4357, 4363,
4369, 4375, 4381, 4387, 4393, 4399, 4405, 4411, 4417, 4423, 4429, 4435, 4441, 4446): five
coordinates (`x, y0, y1, y2, y3`), map register 3049 (the `param_1 + 768` or `+ 896` KV
descriptor, selected by the `selp` at pc 2248) and barrier register 696. -/
def gather4Loads : List Nat :=
  [2259, 2262, 2265, 2268, 2271, 2274, 2277, 2280, 2283, 2286, 2289, 2292, 2295, 2298, 2301, 2303]

/-- `gather4Loads` are exactly the kernel's four-row loads. -/
theorem gather4Loads_eq : gather4Loads = sites isGather4Tensor := by
  decide +kernel

/-- Every global-to-shared tensor load, of both modes: 8 four-dimensional and 16 four-row. -/
def tensorLoads : List Nat := cpTensorLoads ++ gather4Loads

/-- `tensorLoads` are exactly the kernel's tensor loads. -/
theorem tensorLoads_eq : tensorLoads = sites isCpTensor := by
  decide +kernel

/-- A shared-to-global tensor store (`cp.async.bulk.tensor...global.shared::cta`). -/
def isCpTensorStore : Op → Bool
  | .cpTensorStore .. => true
  | _ => false

/-- The 4 `cp.async.bulk.tensor.4d.global.shared::cta.bulk_group` stores of O (PTX 2488, 2861,
3233, 3606), all with four coordinates and map register 3832 (`param_1 + 512`, the O
descriptor). -/
def tensorStores : List Nat := [1358, 1516, 1673, 1831]

/-- `tensorStores` are exactly the kernel's tensor stores. -/
theorem tensorStores_eq : tensorStores = sites isCpTensorStore := by
  decide +kernel

/-- `cp.async.bulk.commit_group`. -/
def isBulkCommit : Op → Bool
  | .bulkCommit => true
  | _ => false

/-- The single `cp.async.bulk.commit_group` (PTX 3610), which closes the group of the four O
stores. -/
def bulkCommits : List Nat := [1832]

/-- `bulkCommits` are exactly the kernel's bulk-group commits. -/
theorem bulkCommits_eq : bulkCommits = sites isBulkCommit := by
  decide +kernel

/-- `cp.async.bulk.wait_group`. -/
def isBulkWait : Op → Bool
  | .bulkWait .. => true
  | _ => false

/-- The single `cp.async.bulk.wait_group.read 0` (PTX 381), which drains an earlier bulk group;
no wait follows the commit of the O stores. -/
def bulkWaits : List Nat := [198]

/-- `bulkWaits` are exactly the kernel's bulk-group waits. -/
theorem bulkWaits_eq : bulkWaits = sites isBulkWait := by
  decide +kernel

/-! ## `tcgen05` instructions -/

/-- `tcgen05.mma`, in every decoded form. -/
def isTcMma : Op → Bool
  | .tcMma .. => true
  | _ => false

/-- The 24 `tcgen05.mma.ws.cta_group::1.kind::f16` (PTX 3921 to 4190): the QK and PV GEMMs of
the two tracks. All 24 have `.ws`, `cta_group::1`, a zero-column-mask descriptor and four
disable-output-lane words; 16 read A from Tensor Memory and 8 from a shared matrix descriptor. -/
def tcMma : List Nat :=
  [2027, 2033, 2038, 2043, 2048, 2053, 2058, 2063, 2068, 2073, 2078, 2083, 2088, 2093, 2098, 2103,
    2117, 2122, 2126, 2130, 2134, 2138, 2142, 2146]

/-- `tcMma` are exactly the kernel's tensor-core MMAs. -/
theorem tcMma_eq : tcMma = sites isTcMma := by
  decide +kernel

/-- `tcgen05.cp`. -/
def isTcCp : Op → Bool
  | .tcCp .. => true
  | _ => false

/-- The 16 `tcgen05.cp.cta_group::1.128x256b` (PTX 3773 to 3847), without a decompression
format: the dequantized bf16 values move from shared memory into Tensor Memory. -/
def tcCp : List Nat :=
  [1936, 1939, 1942, 1945, 1948, 1951, 1954, 1957, 1959, 1962, 1965, 1968, 1971, 1974, 1977, 1980]

/-- `tcCp` are exactly the kernel's `tcgen05.cp` instructions. -/
theorem tcCp_eq : tcCp = sites isTcCp := by
  decide +kernel

/-- `tcgen05.ld`. -/
def isTcLd : Op → Bool
  | .tcLd .. => true
  | _ => false

/-- The 12 `tcgen05.ld.sync.aligned.32x32b` loads: four `.x32` (PTX 487, 492, 499, 504) and
eight `.x64` (PTX 1164, 1375, 1586, 1797, 2119, 2494, 2867, 3239). -/
def tcLd : List Nat := [278, 280, 283, 285, 716, 817, 918, 1019, 1201, 1361, 1519, 1676]

/-- `tcLd` are exactly the kernel's Tensor Memory loads. -/
theorem tcLd_eq : tcLd = sites isTcLd := by
  decide +kernel

/-- `tcgen05.st`. -/
def isTcSt : Op → Bool
  | .tcSt .. => true
  | _ => false

/-- The 4 `tcgen05.st.sync.aligned.32x32b.x64` stores (PTX 1365, 1576, 1787, 1998), which write
P back to Tensor Memory after the softmax. -/
def tcSt : List Nat := [814, 915, 1016, 1117]

/-- `tcSt` are exactly the kernel's Tensor Memory stores. -/
theorem tcSt_eq : tcSt = sites isTcSt := by
  decide +kernel

/-- `tcgen05.wait::ld`. -/
def isTcWaitLd : Op → Bool
  | .tcWaitLd => true
  | _ => false

/-- The 9 `tcgen05.wait::ld.sync.aligned` (PTX 510, 1169, 1380, 1591, 1802, 2124, 2499, 2872,
3244). -/
def tcWaitLd : List Nat := [286, 717, 818, 919, 1020, 1202, 1362, 1520, 1677]

/-- `tcWaitLd` are exactly the kernel's Tensor Memory load waits. -/
theorem tcWaitLd_eq : tcWaitLd = sites isTcWaitLd := by
  decide +kernel

/-- `tcgen05.wait::st`. -/
def isTcWaitSt : Op → Bool
  | .tcWaitSt => true
  | _ => false

/-- The 4 `tcgen05.wait::st.sync.aligned` (PTX 1370, 1581, 1792, 2003), right after the four
Tensor Memory stores. -/
def tcWaitSt : List Nat := [815, 916, 1017, 1118]

/-- `tcWaitSt` are exactly the kernel's Tensor Memory store waits. -/
theorem tcWaitSt_eq : tcWaitSt = sites isTcWaitSt := by
  decide +kernel

/-- `tcgen05.commit`. -/
def isTcCommit : Op → Bool
  | .tcCommit .. => true
  | _ => false

/-- The 3 `tcgen05.commit.cta_group::1.mbarrier::arrive::one.shared::cluster.b64` (PTX 3851,
4093, 4196), one after each group of the two GEMM tracks. -/
def tcCommit : List Nat := [1982, 2105, 2148]

/-- `tcCommit` are exactly the kernel's `tcgen05.commit` instructions. -/
theorem tcCommit_eq : tcCommit = sites isTcCommit := by
  decide +kernel

/-- `tcgen05.fence::after_thread_sync`. -/
def isTcFenceAfter : Op → Bool
  | .tcFenceAfter => true
  | _ => false

/-- The 7 `tcgen05.fence::after_thread_sync` (PTX 482, 1157, 2100, 3769, 3865, 3905, 4108). -/
def tcFenceAfter : List Nat := [275, 711, 1187, 1934, 1986, 2015, 2110]

/-- `tcFenceAfter` are exactly the kernel's after-sync `tcgen05` fences. -/
theorem tcFenceAfter_eq : tcFenceAfter = sites isTcFenceAfter := by
  decide +kernel

/-- `tcgen05.fence::before_thread_sync`. -/
def isTcFenceBefore : Op → Bool
  | .tcFenceBefore => true
  | _ => false

/-- The 2 `tcgen05.fence::before_thread_sync` (PTX 514, 2007). -/
def tcFenceBefore : List Nat := [287, 1119]

/-- `tcFenceBefore` are exactly the kernel's before-sync `tcgen05` fences. -/
theorem tcFenceBefore_eq : tcFenceBefore = sites isTcFenceBefore := by
  decide +kernel

/-! ## mbarrier instructions -/

/-- `mbarrier.init`. -/
def isMbarInit : Op → Bool
  | .mbarInit .. => true
  | _ => false

/-- The 23 `mbarrier.init.shared::cta.b64` (PTX 104 to 239), the barrier rings. Their count
operands are the registers 526, 528, 543 and 545, which the surrounding moves set to 128, 1, 32
and 129 (7, 8, 4 and 4 initializations). -/
def mbarInits : List Nat :=
  [39, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 71, 74, 76, 78, 80, 82, 84, 86]

/-- `mbarInits` are exactly the kernel's barrier initializations. -/
theorem mbarInits_eq : mbarInits = sites isMbarInit := by
  decide +kernel

/-- `mbarrier.arrive`. -/
def isMbarArrive : Op → Bool
  | .mbarArrive .. => true
  | _ => false

/-- The 10 `mbarrier.arrive.shared::cta.b64` (PTX 386, 869, 2018, 3754, 4452, 4459, 4657, 4767,
6652, 6658), all `.release.cta` with count 1; the two at PTX 3754 and 4452 are
`mbarrier.arrive.expect_tx` and carry the transaction byte count. -/
def mbarArrives : List Nat := [200, 571, 1122, 1929, 2305, 2308, 2476, 2565, 3597, 3599]

/-- `mbarArrives` are exactly the kernel's barrier arrivals. -/
theorem mbarArrives_eq : mbarArrives = sites isMbarArrive := by
  decide +kernel

/-- `mbarrier.try_wait.parity`. -/
def isMbarWait : Op → Bool
  | .mbarWait .. => true
  | _ => false

/-- The 16 `mbarrier.try_wait.parity.shared::cta.b64` (PTX 460, 475, 2093, 3762, 3858, 3898,
4101, 4276, 4287, 4321, 4339, 4621, 4730, 4874, 4916, 4930), all `.acquire.cta`. -/
def mbarWaits : List Nat :=
  [264, 272, 1184, 1931, 1983, 2012, 2107, 2205, 2209, 2234, 2245, 2446, 2534, 2644, 2677, 2684]

/-- `mbarWaits` are exactly the kernel's barrier waits. -/
theorem mbarWaits_eq : mbarWaits = sites isMbarWait := by
  decide +kernel

/-- `fence.mbarrier_init`. -/
def isMbarInitFence : Op → Bool
  | .fenceMbarInit => true
  | _ => false

/-- The single `fence.mbarrier_init.release.cluster` (PTX 244), after the 23 initializations. -/
def fenceMbarInit : List Nat := [87]

/-- `fenceMbarInit` is exactly the kernel's barrier-initialization fence. -/
theorem fenceMbarInit_eq : fenceMbarInit = sites isMbarInitFence := by
  decide +kernel

/-! ## Barriers and warp collectives -/

/-- `bar.sync` or `barrier.sync`, with or without a thread count; `bar.arrive` is excluded. -/
def isBar : Op → Bool
  | .barSync .. | .barSyncN .. => true
  | _ => false

/-- The 16 `bar.sync`/`barrier.sync` instructions (PTX 265, 447, 720, 864, 2055, 2059, 2463,
2838, 3210, 3583, 3615, 4212, 4485, 4791, 4819, 6673): one `bar.sync 0` over the whole CTA and
15 with a register barrier id and thread count. 11 are `.aligned` (every `bar.sync`, and one
`barrier.sync.aligned`) and 5 are a plain `barrier.sync`. The kernel has no `bar.arrive`. -/
def bars : List Nat :=
  [97, 256, 475, 569, 1154, 1156, 1342, 1502, 1659, 1817, 1835, 2160, 2330, 2585, 2604, 3610]

/-- `bars` are exactly the kernel's CTA barriers. -/
theorem bars_eq : bars = sites isBar := by
  decide +kernel

/-- `elect.sync`. -/
def isElect : Op → Bool
  | .warp w => match w.kind with
    | .elect => true
    | _ => false
  | _ => false

/-- The 8 `elect.sync` (PTX 62, 91, 2476, 2848, 3220, 3593, 3647, 4223), each the leader
election of an inline-assembly block; the pcs are the `elect.sync` instructions, not the
`mov.s32` that write the elected-lane result. -/
def elects : List Nat := [16, 31, 1350, 1507, 1664, 1822, 1853, 2165]

/-- `elects` are exactly the kernel's leader elections. -/
theorem elects_eq : elects = sites isElect := by
  decide +kernel

/-- `shfl.sync`. -/
def isShfl : Op → Bool
  | .warp w => match w.kind with
    | .shfl _ => true
    | _ => false
  | _ => false

/-- The 7 `shfl.sync` (PTX 48, 51, 3633 `idx`; 4642, 4645, 4752, 4755 `bfly`). -/
def shfls : List Nat := [6, 9, 1843, 2464, 2467, 2553, 2556]

/-- `shfls` are exactly the kernel's warp shuffles. -/
theorem shfls_eq : shfls = sites isShfl := by
  decide +kernel

/-- `vote.sync`. -/
def isVote : Op → Bool
  | .warp w => match w.kind with
    | .vote .. => true
    | _ => false
  | _ => false

/-- The single `vote.sync.any.pred` (PTX 878): a warp-wide any of the predicate that pc 576
(`setp.gt.f32 x, 6.0`) computes; pc 580 then negates the result. -/
def votes : List Nat := [578]

/-- `votes` are exactly the kernel's warp votes. -/
theorem votes_eq : votes = sites isVote := by
  decide +kernel

/-- `setmaxnreg`. -/
def isSetMaxReg : Op → Bool
  | .setMaxReg .. => true
  | _ => false

/-- The 3 `setmaxnreg` (PTX 272 `inc` to 224, 3630 `dec` to 72, 4824 `inc` to 208), the warp
role's register-budget changes. -/
def setMaxRegs : List Nat := [103, 1842, 2606]

/-- `setMaxRegs` are exactly the kernel's register-budget changes. -/
theorem setMaxRegs_eq : setMaxRegs = sites isSetMaxReg := by
  decide +kernel

/-- `trap`. -/
def isTrap : Op → Bool
  | .trap => true
  | _ => false

/-- The 2 `trap` (PTX 258 and 3700). pc 95 follows the `tcgen05.alloc` result check (pcs 91 to
94) and aborts the thread unless the allocation returned address 0; pc 1896 follows a
comparison of an index-derived value against 63. -/
def traps : List Nat := [95, 1896]

/-- `traps` are exactly the kernel's traps. -/
theorem traps_eq : traps = sites isTrap := by
  decide +kernel

/-- `exit` or `ret`. -/
def isTerminator : Op → Bool
  | .exit | .ret => true
  | _ => false

/-- The kernel's only terminator (pc 3611, PTX 6676) is `ret`; it contains no `exit`. -/
def exits : List Nat := [3611]

/-- `exits` are exactly the kernel's terminators. -/
theorem exits_eq : exits = sites isTerminator := by
  decide +kernel

/-! ## The parameter-pointer sites

The tensor-map object is `param_1`, a 1024-byte by-value parameter of 8 descriptors. pc 1 moves
its address into `%rd1` (register 2990); the four `cvta.param.u64` at pcs 21, 162, 1865 and 2255
convert it to a generic address (registers 3022, 3001, 3006 and 3052); six `add.s64` add the
descriptor offsets, and three `prefetch.tensormap` warm the Q, O and KV descriptors. The checks
below follow those registers through the decoded stream. -/

/-- The registers that hold the `param_1` address: the destinations of the four `cvta.param`
sites. -/
def param1AddressRegs : List Nat := [3022, 3001, 3006, 3052]

/-- `cvta.param.u64` of the register that pc 1 loaded `param_1` into. -/
def isParam1Cvta : Op → Bool
  | .addr (.cvta false .param 64 _ (.reg 2990)) => true
  | _ => false

/-- The 4 `cvta.param.u64` sites of `param_1` (PTX 70, 336, 3662, 4352). -/
def param1CvtaSites : List Nat := [21, 162, 1865, 2255]

/-- `param1CvtaSites` are exactly the kernel's `cvta.param` sites of register 2990. -/
theorem param1CvtaSites_eq : param1CvtaSites = sites isParam1Cvta := by
  decide +kernel

/-- An `add.s64` whose first source is a register that holds the `param_1` address. -/
def isParamOffsetAdd : Op → Bool
  | .int ⟨.add, .int .s 64, _, _, .reg r :: _⟩ => param1AddressRegs.contains r
  | _ => false

/-- The 6 `add.s64` sites that add a descriptor offset to the `param_1` address (PTX 71, 75,
79, 2114, 3709, 4353). -/
def paramAdds : List Nat := [22, 24, 26, 1197, 1902, 2256]

/-- `paramAdds` are exactly the kernel's `param_1` pointer-offset additions. -/
theorem paramAdds_eq : paramAdds = sites isParamOffsetAdd := by
  decide +kernel

/-- `prefetch.tensormap`. -/
def isTensorMapPrefetch : Op → Bool
  | .prefetchTensorMap .. => true
  | _ => false

/-- The 3 `prefetch.tensormap` (PTX 73, 77, 81), of the Q, O and KV descriptors. -/
def prefetchTensorMapSites : List Nat := [23, 25, 27]

/-- `prefetchTensorMapSites` are exactly the kernel's tensormap prefetches. -/
theorem prefetchTensorMapSites_eq : prefetchTensorMapSites = sites isTensorMapPrefetch := by
  decide +kernel

/-- The 9 sites of the parameter-pointer assumption, in source order: the six descriptor-offset
additions and the three tensormap prefetches. -/
def paramPointerSites : List Nat := [22, 23, 24, 25, 26, 27, 1197, 1902, 2256]

/-- `paramPointerSites` are exactly the kernel's parameter-pointer additions and prefetches. -/
theorem paramPointerSites_eq :
    paramPointerSites = sites (fun op => isParamOffsetAdd op || isTensorMapPrefetch op) := by
  decide +kernel

/-- The `param_1` by-value parameter object (`TmaParams`): the second of the two parameter
objects of `Decoded.metadata`. -/
def param1Object? : Option ParamObjectDecl :=
  match Decoded.metadata.paramObjects with
  | [_, obj] => some obj
  | _ => none

/-- pc 1 moves the address of the `param_1` object into register 2990, the register the four
`cvta.param` sites convert. The object is 1024 bytes; its name is the symbol of the decoded
instruction, so no string is written out here. -/
theorem param1_base :
    (match codeAt 1, param1Object? with
      | some ⟨none, .move m⟩, some obj =>
        m.dsts == [some 2990] && m.srcs == [.paramSym obj.name] && obj.count == 1024
      | _, _ => false) = true := by
  decide +kernel

/-- Each `cvta.param` site moves one of the four address registers to a fresh register. -/
theorem param1_cvtas :
    (match codeAt 21, codeAt 162, codeAt 1865, codeAt 2255 with
      | some ⟨none, .addr (.cvta false .param 64 d _)⟩,
        some ⟨none, .addr (.cvta false .param 64 d' _)⟩,
        some ⟨none, .addr (.cvta false .param 64 d'' _)⟩,
        some ⟨none, .addr (.cvta false .param 64 d''' _)⟩ =>
        d == 3022 && d' == 3001 && d'' == 3006 && d''' == 3052
      | _, _, _, _ => false) = true := by
  decide +kernel

/-- The six additions and the descriptor each forms: `+128` is the Q descriptor (pc 22 for the
prefetch, pc 1902 for the 4-D loads), `+512` the O descriptor (pc 24 for the prefetch, pc 1197
for the stores), `+768` the main KV descriptor (pc 26, for the prefetch) and, for the gather4
loads, the register pc 2248 selects between 768 and 896 (the extra KV descriptor). -/
theorem paramAdds_offsets :
    (match codeAt 22, codeAt 24, codeAt 26, codeAt 1197, codeAt 1902, codeAt 2256 with
      | some ⟨none, .int ⟨.add, _, _, [some 3019], [.reg 3022, .imm 128]⟩⟩,
        some ⟨none, .int ⟨.add, _, _, [some 3020], [.reg 3022, .imm 512]⟩⟩,
        some ⟨none, .int ⟨.add, _, _, [some 3021], [.reg 3022, .imm 768]⟩⟩,
        some ⟨none, .int ⟨.add, _, _, [some 3832], [.reg 3001, .imm 512]⟩⟩,
        some ⟨none, .int ⟨.add, _, _, [some 3058], [.reg 3006, .imm 128]⟩⟩,
        some ⟨none, .int ⟨.add, _, _, [some 3049], [.reg 3052, .reg 3051]⟩⟩ => true
      | _, _, _, _, _, _ => false) = true := by
  decide +kernel

/-- pc 2248 is `selp.b64 %rd62, 768, 896, %p52`: the KV descriptor offset is 768, or 896 when
the extra KV cache is enabled. -/
theorem paramKvOffsetSelector :
    (match codeAt 2248 with
      | some ⟨none, .int ⟨.selp, _, _, [some 3051], [.imm 768, .imm 896, .reg _]⟩⟩ => true
      | _ => false) = true := by
  decide +kernel

/-- The registers the three later additions write are the maps the tensor copies read:
pc 1902 writes the Q map 3058, pc 2256 the KV/extra-KV map 3049 and pc 1197 the O map 3832. -/
theorem paramAdds_write_maps :
    (match codeAt 1902, codeAt 2256, codeAt 1197 with
      | some ⟨none, .int ⟨.add, _, _, [some 3058], _⟩⟩,
        some ⟨none, .int ⟨.add, _, _, [some 3049], _⟩⟩,
        some ⟨none, .int ⟨.add, _, _, [some 3832], _⟩⟩ => true
      | _, _, _ => false) = true := by
  decide +kernel

/-- The three prefetch sites read the registers the first three additions write. -/
theorem prefetchTensorMapSites_read :
    (match codeAt 23, codeAt 25, codeAt 27 with
      | some ⟨none, .prefetchTensorMap true 64 (.reg 3019)⟩,
        some ⟨none, .prefetchTensorMap true 64 (.reg 3020)⟩,
        some ⟨none, .prefetchTensorMap true 64 (.reg 3021)⟩ => true
      | _, _, _ => false) = true := by
  decide +kernel

/-- Every 4-D load reads the Q map register 3058, the destination of pc 1902. -/
theorem cpTensorLoads_map :
    cpTensorLoads.all (fun pc => match codeAt pc with
      | some ⟨_, .cpTensor _ _ _ _ (.reg 3058) ..⟩ => true
      | _ => false) = true := by
  decide +kernel

/-- Every gather4 load reads the KV/extra-KV map register 3049, the destination of pc 2256. -/
theorem gather4Loads_map :
    gather4Loads.all (fun pc => match codeAt pc with
      | some ⟨_, .cpTensor _ _ _ _ (.reg 3049) ..⟩ => true
      | _ => false) = true := by
  decide +kernel

/-- Every store reads the O map register 3832, the destination of pc 1197. With
`paramAdds_offsets` and `paramAdds_write_maps` this pins the six additions to the four
descriptors: Q at `+128`, O at `+512`, KV at `+768` and extra KV at `+896`. -/
theorem tensorStores_map :
    tensorStores.all (fun pc => match codeAt pc with
      | some ⟨_, .cpTensorStore (.reg 3832) ..⟩ => true
      | _ => false) = true := by
  decide +kernel

end PTX.Kernels.FlashMlaSparseDecodeH64
