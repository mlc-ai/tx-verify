-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOTmemOrder
public import Kernels.InklingRelDecode.Proof.Protocol.SOHandoff
public import Kernels.InklingRelDecode.Proof.Interface.ProtocolThreads
public import Lemmas.Flow.AllocTmpl
public import Lemmas.Tmem.Alloc512

@[expose] public section

/-!
# The lifetime of the Tensor Memory allocation (obligation 7)

* **The allocation is at column 0** (`alloc_col_zero`): the address the common start's lane 0
  stores into `global_smem` after its `tcgen05.alloc` of 512 columns is the 32-bit value 0
  (`Consistent.alloc512_result`); with the premise that the allocation's request is recorded in its
  CTA's history and that history replays without a fault (`hnf`, from `¬ ResourceUnsafe`), the
  `col` of `DStart.shape_allocWr` is 0.
* **Every role's base is 0** (`ld0_tm_zero`): the load of the base word after `bar.sync 0` returns
  the bytes of that store (`BaseWordZero`: the reads-from premise of the base word, the
  `TmemAlloc.BaseRead` of FA4), so the machine state after it has `tm = 0`; `TmOk 0` holds, so
  every column formula of the roles (`SOTmemCols`) is a column of `[0, 512)` and every cell the
  semantics accepts (`resultCell`, `aCell`) is within the 512 columns.
* **Footprints of the softmax region's loads and stores** (`ldS_col`, `stP_col`): a thread of half
  `h` reads the score columns `[64 h, 64 h + 64)` of its buffer and stores the probabilities in
  `[32 h, 32 h + 32)`: **the two halves of a warp overlap** (`half_overlap`: the store of half 1
  covers columns the load of half 0 reads), which is why the S read must finish before the P store
  of the other half (`SOTmemOrder`, premise `PAliasSync`).
* **The MMAs are done before the deallocation** (`mma_done_before_dealloc`): from the epilogue's
  poll of `o_final` (`SOHandoff.f_doneBefore_at`) and the epilogue's causal chain to the
  deallocation (`bar.sync 0` of every thread before it).
* `TmemLife`: **the premises that remain**, each a named-barrier or reads-from fact with the row of
  the development notes that says what proves it: `alloc_before` (every access follows its CTA's
  allocation: `bar.sync 0` generation 0 after the alloc), `ldst_before_dealloc` (every `tcgen05.ld`
  and `tcgen05.st` is finished by its `wait` before the thread's `bar.sync 0` of the exit
  generation, which is before the deallocation), `dealloc_after_epilogue` (the deallocation follows
  every epilogue thread's `bar.sync 0` after its poll).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof

noncomputable section

/-! ### The allocation is at column 0 -/

/-! ### The softmax region's footprints -/

/-! ### The lifetime premises and the MMAs' completion -/

/-- **What remains of the lifetime of the allocation**, as named-barrier facts: `bar.sync 0` of the
common start (generation 0) orders the allocation before every thread's later events, and the
exit generation (`bar.sync 0` of every thread, after every `wait::ld` and `wait::st`) orders every
access's completion before the deallocation. -/
structure TmemLife (L : Launch) (X : Execution) : Prop where
  /-- Every MMA, `tcgen05.ld` and `tcgen05.st` of a thread of CTA `c` follows an allocation by
  lane 0 of warp 0 of the CTA, in causality. -/
  alloc_before : ∀ {e : EvId} {a : Nat} {vals : List Value} {sh : TcShape},
    (IsMma X e ∨ X.TLd e a vals sh ∨ X.TSt e a vals sh) →
      ∃ j pc grp dst n, X.get ((e.1 / L.block) * L.block, j) =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ ∧
      j + 1 < (X.tr ((e.1 / L.block) * L.block)).length ∧
      baseCausality L X ((e.1 / L.block) * L.block, j) e
  /-- Every `tcgen05.ld` (`tcgen05.st`) of a CTA is finished, by the thread's `wait::ld`
  (`wait::st`), before every deallocation of the CTA, in causality. -/
  ldst_before_dealloc : ∀ {e d : EvId} {a : Nat} {vals : List Value} {sh : TcShape} {pc : Nat}
      {grp : CtaGroup} {dst : Option Loc} {da n : Nat},
    X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc da n))⟩ →
      (d.1 / L.block) = (e.1 / L.block) →
      (X.TLd e a vals sh → WaitBefore L X .waitLd e d) ∧
      (X.TSt e a vals sh → WaitBefore L X .waitSt e d)
  /-- Every deallocation of a CTA follows, in causality, every poll of `o_final` of the CTA's
  epilogue threads (through the exit `bar.sync 0`). -/
  dealloc_after_epilogue : ∀ {d : EvId} {h j : Nat} {pc pc' p : Nat} {grp : CtaGroup}
      {dst : Option Loc} {da n : Nat} {acq : Bool} {sc : MbarScope} {c : Nat},
    X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc da n))⟩ → (h / L.block) = (d.1 / L.block) →
    X.get (h, j) = some ⟨pc', .wait (EvW.oFinal L c) p true acq sc⟩ →
      baseCausality L X (h, j) d

variable {L : Launch} {X : Execution} {c cm p0 : Nat} {K : Kernel} {A : List Assumption}
  {mem0 : Mem0}

/-- **Every MMA is done before every deallocation of its CTA**: the MMA is issued before `cm`'s
commit to `o_final` (all MMAs are), the epilogue's poll of `o_final` observes the commit, and the
poll is before the deallocation (`dealloc_after_epilogue`). -/
theorem mma_done_before_dealloc (hX : Consistent L K A mem0 X) (F : Facts L X c cm p0)
    (hone : ∀ {x : EvId}, IsMma X x → x.1 / L.block = c → x.1 = cm)
    (hcommit : ∀ {i pc : Nat} {sp : TcCommit.Spec},
      X.get (cm, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = EvW.oFinal L c →
        ((X.tr cm).take i).countP (commitsTo (EvW.oFinal L c)) = 0)
    (hbefore : ∀ {x : EvId}, IsMma X x → x.1 / L.block = c → ∀ {i pc : Nat} {sp : TcCommit.Spec},
      X.get (cm, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = EvW.oFinal L c → x.2 < i)
    {h j pc p : Nat} {sc : MbarScope} (hcta : SameCta L cm h)
    (he : X.get (h, j) = some ⟨pc, .wait (EvW.oFinal L c) p true true sc⟩) {x d : EvId}
    (hx : IsMma X x) (hxc : x.1 / L.block = c) (hbc : baseCausality L X (h, j) d) :
    DoneBefore L X x d :=
  f_doneBefore_at hX F hone hcommit hbefore hcta he hx hxc hbc

end
end PTX.Kernels.InklingRelDecode.Proof.SO
