-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Export.Tmem
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.Reads
public import Kernels.InklingRelDecode.Proof.Top.Safe.Completed

@[expose] public section

/-! # ERR-TMEM-RACE (reads): Tensor Memory reads are ordered with the writes of their cells

`TcMma.ReadsUnsafe` by reader kinds (`Tmem.reads_safe`): an accumulator read of an MMA is a write of
the same cell, so it is ordered as the writes are (`Tmem.writes_safe`); a PV MMA's read of the
probabilities is ordered with the QK MMAs and probability stores of its buffer by the score and
probability handshakes (`Tmem.a_read_order`); the kernel has no `tcgen05.shift`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem Safe.noTmemReads (hp : Pre Q L m) {X : Execution} (base : Iface.BaseRead L X)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (_hu : ¬HasUb X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) :
    ¬ TcMma.ReadsUnsafe L X :=
  Tmem.reads_safe hp hX hf safe base rows init

end PTX.Kernels.InklingRelDecode.Proof.Top
