-- SPDX-License-Identifier: Apache-2.0
-- iface: TmemRow.Mma producer=B status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma

@[expose] public section

/-! # The MMA warp: Tensor Memory row

The MMA warp's code (pcs 1850–2161) has these `tcgen05` sites (checked on the code by
`mma_sites`): the fences `after_thread_sync` at 1934, 1986, 2015, 2110; the sixteen
`tcgen05.cp.cta_group::1.128x256b` copies of the query (1936–1980); the commits at 1982, 2105,
2148; the MMAs (2027–2103 for QK, 2117–2146 for PV). The row states the RECORDED events
(`Mma/Ev.lean`): a copy `.cp s` of shape `128x256b` without decompression, a commit `.commit s`
of group one, an MMA `.mma d s acc mask`, the fence. No paired Tensor Memory operation. The
copies' and MMAs' Tensor Memory operands are exact (`MmaTc`): the machine's value table
(`Mma/Machine.lean`) gives every address and descriptor register. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace TmemRow

/-- **Static check**: the `tcgen05` sites of pcs 1850–2161. -/
theorem mma_sites : regionOk kernel.code 1850 2162
    ([(1934, .fenceA), (1986, .fenceA), (2015, .fenceA), (2110, .fenceA), (1982, .commit),
      (2105, .commit), (2148, .commit)] ++
     ([1936, 1939, 1942, 1945, 1948, 1951, 1954, 1957, 1959, 1962, 1965, 1968, 1971, 1974, 1977,
       1980].map (·, Tag.cp)) ++
     ([2027, 2033, 2038, 2043, 2048, 2053, 2058, 2063, 2068, 2073, 2078, 2083, 2088, 2093, 2098,
       2103, 2117, 2122, 2126, 2130, 2134, 2138, 2142, 2146].map (·, Tag.mma))) = true := by
  decide +kernel

end TmemRow

namespace TmemRow

/-- The pc of copy `k` of the query (`k < 16`). -/
def cpPc (k : Nat) : Nat := if k < 8 then 1936 + 3 * k else 1935 + 3 * k
/-- The pc of QK MMA `k` (`k < 16`) and of PV MMA `k` (`k < 8`). -/
def qkPc (k : Nat) : Nat := if k = 0 then 2027 else 2028 + 5 * k
def pvPc (k : Nat) : Nat := if k = 0 then 2117 else 2118 + 4 * k

/-- The descriptor words of the QK MMAs (M 64, N 128) and of the PV MMAs (M 64, N 256). -/
abbrev qkIdesc : Nat := 69207184
abbrev pvIdesc : Nat := 71369872

/-- An MMA's operands beyond its D column: A at `aT` (none: shared memory), the `.ws`
`cta_group::1` `kind::f16` descriptor of the word `i`, and the low and high CTA of the issuing
CTA's group. -/
def MmaOps (L : Launch) (g : Nat) (s : TcMma.OperandSpec) (aT : Option Nat) (i : Nat) : Prop :=
  s.aTmem = aT ∧ TcMma.decode .one true .f16 i = some s.descriptor ∧
    ∃ ctas, L.ctaGroup (g / L.block) s.descriptor.group = some ctas ∧
      ctas.head? = some s.lowCta ∧ ctas.getLast? = some s.highCta

end TmemRow

/-- The `tcgen05` events of the MMA warp's thread `g`: the fence; copy `k` (`k < 16`, at
`cpPc k`) of shape `128x256b`, no decompression, to column `256 + 8 k` in the CTA's group; a
commit of group one; QK MMA `k` (`k < 16`, at `qkPc k`): D at column 400, A at `256 + 8 k`,
accumulating iff `k ≠ 0`; PV MMA `k` (`k < 8`, at `pvPc k`): D at column `128 (k % 2)`, A in
shared memory, accumulating from `k = 2` (the first two accumulate unless it is the first block).
Every MMA enables every output lane. -/
def TmemRow.MmaTc (L : Launch) (g : Nat) (e : Event) : Prop :=
  e.kind = .tc .fenceAfter ∨
    (∃ s k, k < 16 ∧ e.pc = TmemRow.cpPc k ∧ e.kind = .tc (.cp s) ∧ s.shape = .s128x256b ∧
      s.fmt = none ∧ s.address = 256 + 8 * k ∧ L.ctaGroup (g / L.block) .one = some s.ctas) ∨
    (∃ s, e.kind = .tc (.commit s) ∧ s.group = .one) ∨
    (∃ s k, k < 16 ∧ e.pc = TmemRow.qkPc k ∧ e.kind = .tc (.mma 400 s (k != 0) [0, 0, 0, 0]) ∧
      TmemRow.MmaOps L g s (some (256 + 8 * k)) TmemRow.qkIdesc) ∨
    ∃ s acc k, k < 8 ∧ e.pc = TmemRow.pvPc k ∧
      e.kind = .tc (.mma (128 * (k % 2)) s acc [0, 0, 0, 0]) ∧ (2 ≤ k → acc = true) ∧
      TmemRow.MmaOps L g s none TmemRow.pvIdesc

/-- **Row `TmemRow.Mma`**: a `tcgen05` event of the MMA warp is one of `MmaTc`. -/
def TmemRow.Mma (_P : Params) (L : Launch) (X : Execution) : Prop :=
  TmemRow.TcRow L X (MmaAt L) fun g e => TmemRow.MmaTc L g e

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
