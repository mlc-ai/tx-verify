-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.OutLoad

@[expose] public section

/-!
# What `result_goal` takes from the layers below

`Inputs Q L mem0 X` is the one structure of what the result layer has not proved for a consistent
complete execution `X`. Every field is a statement about abstract states of the thread machines
(`Interface.St`), events and `Spec`'s quantities; no program counter and no register number occurs.
The fields are of three kinds, and each says which layer has to supply it.

**Thread layer** (`smOb`, `premises`): the premises of `Interface.threadFacts`, which the result
layer uses through `ThreadFacts` (every global write is an epilogue store of the word and at the
footprint `Spec` gives; `Epi.Means`).

**The MMA data path** (`kvCopies`, `kvOrder`, `qTile`, `mmaWords`, `qkChain`, `pTile`, `oAcc`):
the premises of `Result/Mma*.lean`, with the probabilities and rescale factors of the softmax
fixed to `Out.pElemE` and `Out.alphaRow` (`OutProb.lean`): the bf16 words the softmax stored in
Tensor Memory are `Softmax.step`'s `p_k` on a visible key and `0` on a masked one, and the factor
applied to the O accumulator before block `b` is `Softmax.step`'s `alpha`. The softmax region proves
`pTile` and `oAcc` from its sites' event shapes and values (it reads the S tile through
`Mma.score_load`, which uses `qTile`, `qkChain`, `kvCopies`, `kvOrder`).

**The softmax region's last state** (`smExit`): the softmax state that goes straight into the
epilogue holds the launch's scale and the running maximum and sum of the row's blocks
(`Sm.Corr`, `Out.blocks0`). *Softmax region*: `SmBridge.corr_step`, one block at a time, and the
score stage's sites (`DComp.SmObligations.score`); the epilogue's registers are then the bridge's of
it (`OutOrigin.rowIn_of_smExit`), and whether the load is skipped follows (`OutOrigin.skip_of`).

**The `O` tile** (`oSource`): for a valid row whose epilogue loaded (the load event is an earlier
event of the thread, `OutOrigin.ld_event`), the last PV MMA of its CTA (block `num_iters - 1`, the
state of step 7 of iteration `num_iters`) is the read source of every cell the load reads, and the
epilogue's Tensor Memory base is the MMA warp's. *Protocol layer*: the `o_final` commit of the MMA
warp observed by the epilogue's poll (`SO`'s `o_final` objects), `Mma.MmaWords.tm` and the
allocation's base word (`SO.tm_ok_zero`) for `d.pr.tm = dm.tm`.

The stores' existence (`OutIssued.exists_oStore`, `exists_lseStore`), the epilogue's registers, the
skip, and the load event are proved (`OutIssued`, `OutOrigin`), not premises.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma PTX.TcMma

noncomputable section

/-- **What `result_goal` takes for one execution** (see the file header). -/
structure Inputs (Q : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop where
  -- Thread layer
  /-- The softmax region's obligations (`Interface.SmOb`). -/
  smOb : Interface.SmOb Q L mem0
  /-- The thread machines' premises (`Interface.Premises`). -/
  premises : Interface.Premises Q L X
  -- The MMA data path
  kvCopies : KvCopies Q L X
  kvOrder : KvOrder Q L X
  qTile : QTile Q L X
  mmaWords : MmaWords Q L X
  qkChain : QkChain Q L X
  /-- The probabilities in Tensor Memory are the softmax's `p_k` (`Out.pElemE`). -/
  pTile : PTile Q L X (pElemE Q L)
  /-- The factors applied to the O accumulator are the softmax's `alpha` (`Out.alphaRow`). -/
  oAcc : OAcc Q L X (alphaRow Q L)
  -- The softmax region's last state and the O tile
  /-- **The softmax state that goes straight into the epilogue** (a valid row) holds the launch's
  scale and the running maximum and sum of the row's blocks. -/
  smExit : ∀ {g k : Nat} {dsm : Sm.D} {d : Epi.D}, g < L.threads →
    Interface.St Q L X g k = some (some (.d (.sm dsm))) →
    Interface.St Q L X g (k + 1) = some (some (.d (.epi d))) → d.pr.rv = true →
    dsm.e.sc = Q.scale ∧ Sm.Corr (sl Q) (blocks0 Q (reqOf L g) (splitOf L g)
      (Epi.tokM (g % L.block)) (Epi.outHead L g)) dsm
  /-- **The epilogue's `O` words**: for the load of a valid row's epilogue, the last PV MMA of the
  CTA (the state of step 7 of iteration `num_iters`) is the read source of each of the 64 cells it
  reads; the epilogue's Tensor Memory base is the MMA warp's. -/
  oSource : ∀ {g k k0 pc : Nat} {d d0 : Epi.D}, g < L.threads →
    Interface.St Q L X g k = some (some (.d (.epi d))) → d.pr.rv = true → d.sk = false →
    Interface.St Q L X g k0 = some (some (.d (.epi d0))) → d0.site = .ld → d0.pr = d.pr →
    X.get (g, k0) = some ⟨pc, .tc (.ld d.pr.taddr d.o (.s16x32bx2 64))⟩ →
    ∃ (m : EvId) (pcm dst : Nat) (sp : TcMma.OperandSpec) (acc : Bool) (mask : List Nat)
      (dm : Mma.D) (P : Loader.Pro),
      m.1 < L.threads ∧ m.1 / L.block = g / L.block ∧
      X.get m = some ⟨pcm, .tc (.mma dst sp acc mask)⟩ ∧
      Interface.St Q L X m.1 m.2 = some (some (.w (.mma dm P))) ∧ dm.site = .pv 7 ∧
      dm.i = Q.numIters (reqOf L g) (splitOf L g) ∧ d.pr.tm = dm.tm ∧
      ∀ j < 64, ReadSource L X .ld m (g, k0) (tcDataCell L g (.s16x32bx2 64) d.pr.taddr j)

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Out
