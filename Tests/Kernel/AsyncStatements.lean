-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Correct
public import Lemmas.Order.OrderBaseCausality
public import Tests.Async.AsyncExecution
public import Tests.Memory.InitialMemory
public import Lemmas.Order.ObjectOrder
public import Lemmas.Tcgen05.TcCollExtend
public import Lemmas.Snoc.PlainAsyncExtend
public import Lemmas.Snoc.ObjectAppend

-- Proof-kernel audit for the new interfaces while old kernel proofs are migrated.
#print axioms PTX.Correct.exits
#print axioms PTX.terminates_of_count
#print axioms PTX.visible_write
#print axioms PTX.read_byte_of_latest
#print axioms PTX.pending_copy_read_race
#print axioms PTX.Tests.AsyncExecution.two_phase_tma_ok
#print axioms PTX.Tests.AsyncExecution.first_not_second_phase

#print axioms PTX.initial_reads_agree
#print axioms PTX.initial_choice_preserved
#print axioms PTX.Tests.InitialMemory.copy_rf

#print axioms PTX.ObjectCoherent.index_lt
#print axioms PTX.MBarrier.CheckedLog.at
#print axioms PTX.tmaOk_snoc_tc
#print axioms PTX.consistent_tccoll_snoc
#print axioms PTX.snoc_plain_orderOk
#print axioms PTX.consistent_snoc_plain
#print axioms PTX.MBarrier.UpdateBeforeWait.snoc_iff
#print axioms PTX.appendObject_baseCausality_iff

#print axioms PTX.modelCausality_async_trans
#print axioms PTX.AsyncChain.trans

open Lean Elab Command in
run_elab do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``PTX.AsyncChain.trans, ``PTX.modelCausality_async_trans] do
    for ax in ← collectAxioms name do
      unless ax ∈ allowed do throwError "{name} uses unexpected axiom {ax}"
