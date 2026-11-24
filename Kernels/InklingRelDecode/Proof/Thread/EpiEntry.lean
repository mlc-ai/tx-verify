-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiAll
public import Kernels.InklingRelDecode.Proof.Thread.EpiValue

@[expose] public section

/-! # The epilogue as a code machine: entries, soundness and what it leaves to other layers

`code asms L g d0` is the epilogue from the state `d0`; `stepAt_all` is its obligation at every
state (`EpiAll`). The machine's entry is the poll of `o_final` at pc 2565 with the facts
`entryFacts pr sk` (`D.entry pr sk`; `D.start pr` for `num_iters >= 1`, `D.startSk pr` for
`num_iters < 1`): every thread polls, and `sk` (`%p173`) only decides, after the poll and the
local code of pcs 2567-2600, whether the thread loads (`sk = false`) or goes to the stores of the
zero pair (`sk = true`).

`sound` assembles `Code.Sound`: from the entry state the machine simulates the thread, given
that the thread reaches the entry (`hstart`, the previous region's obligation).

## What the previous region (the softmax loop) must provide

At pc 2560 (the first instruction after the loop) the registers `%p3`, `%p175`, `%r1`, `%r2`,
`%r3`, `%r17`, `%r25`, `%r30`, `%r35`, `%r36`, `%r37`, `%r72`, `%r149`, `%r163`, `%r1453`,
`%r1454`, `%rd8`, `%rd75`, `%rd76` (the registers live there), and from them the local code of
pcs 2560-2564 (the bridge's first part, `Br`) computes the machine's `Prm`:

* `Prm.p3`, `rv`, `tid`, `tm`, `w`, `c0`, `mb`, `a`, `b`, `c`, `dd`, `e`, `d0`, `ob`, `lb`, `l`
  are the values of `%p3`, `%p175`, `%r1`, `%r2`, `%r3`, `%r30`, `%r163`, `%r72`, `%r17`, `%r35`,
  `%r149`, `%r36`, `%rd8`, `%rd75`, `%rd76`, `%r1454` (`Prm.Ok`: the numbers are 32- or 64-bit
  integers, the warp index is below 4, the row index `(((a * b + c) + dd) * 12 + e)` is below
  `2^24` and `l`, `lse` are four-byte words);
* `Prm.lse` is the value of `%r63 = fma.rn.f32 %r37, %r1453, lg2.approx.ftz.f32(%r1454)`, the
  log-sum-exp the kernel stores for a non-empty row; `%r1299` (id 1760) is the word `0`;
* the thread reaches the entry state with `sk = (%p173 = (%r25 < 1))`.

The zero test `%p178` (`Prm.eq0`, `setp.equ.f32 %p178, %r1454, 0f0`) is computed by the epilogue
itself, after the poll (pc 2568). The bridge's first part needs a rule for
`lg2.approx.ftz.f32` (the kernel's `Assumptions.lg2Exact`) and for `fma` on the softmax state; it
is proved in `Br`.

## What the protocol layer discharges

* The zero test of the row sum does not fault (`Prm.setpOk`) and, for `num_iters >= 1`, the
  reciprocal of the selected value does not fault (`Prm.rcpOk`); otherwise `next` is `none`.
* The load's event returns `vals` with `vals.length = 64` (guaranteed by the template); which Tensor
  Memory cells they are, and that they were written by the MMA warp's `tcgen05.commit` before
  `o_final` completed, is the protocol layer's (the event `.tc (.ld a vals (.s16x32bx2 64))`).
* Each store event writes the bytes the table gives (`D.word`, `D.lseWord`) at the address the table
  gives (`Prm.lAddr`, `Prm.oAddr`); `word_fin` reads them as numbers (`EpiValue`). Disjointness of
  the writes from the inputs and across threads is `Pre.outputsApart` and the row/lane partition
  (`Prm.row`, `Prm.d0`), which the protocol layer proves from the launch. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- **The machine simulates the thread** from the entry state `d0`, given that the thread reaches
that state with its facts. -/
theorem sound (d0 : D) (hi : Inv d0) (hw : d0.pr.w = g % L.block / 32)
    (hstart : ∃ t, Relation.ReflTransGen (Tau kernel asms L g) {} t ∧
      At t d0.site.pc (facts d0)) : (code asms L g d0).Sound where
  start := by
    obtain ⟨t, hr, ht⟩ := hstart
    exact ⟨t, hr, ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩, hi, hw⟩
  steps := stepAt_all d0

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
