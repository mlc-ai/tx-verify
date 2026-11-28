-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Export.Tmem
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.QkStore
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PvStore

@[expose] public section

/-! # ERR-TMEM-RACE (two writes): Tensor Memory writes are ordered

`TcMma.WritesUnsafe` by writer kinds (`Tmem.writes_safe`): the MMAs of a cell are the CTA's one
elected lane's, pipelined in program order; the stores of a cell are one data thread's, pipelined in
program order; the score and accumulator columns are disjoint. What crosses roles is the order of a
QK MMA and a probability store of one score buffer (`Tmem.qk_store_order`) and of a PV MMA and a
rescale store (`Tmem.pv_store_order`), both from the score, probability and output handshakes. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem Safe.noTmemWrites (hp : Pre Q L m) {X : Execution} (base : Iface.BaseRead L X)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (_hu : ¬HasUb X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) :
    ¬ TcMma.WritesUnsafe L X :=
  Tmem.writes_safe hp hX hf base (Tmem.qk_store_order hp hX hf safe base rows init)
    (Tmem.pv_store_order hp hX hf safe base rows init)

end PTX.Kernels.InklingRelDecode.Proof.Top
