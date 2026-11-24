-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Proof.Epilogue.StoreOperands
public import Lemmas.Flow.Local
public import Lemmas.Flow.Run

@[expose] public section

/-! # The output warp's steps that the audits run

The events and the step rules of the output warp which the launch-word witness executes: the reads
of a request's endpoints (`endpointEvent`), the ready barrier (`readyLoc`), the tensor store
(`storeTemplate`), and that the assumptions leave the warp's region to the core rules
(`epilogue_out_all_eq_nil`). -/

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof

noncomputable section

/-- The ready barrier of an output stage. -/
def readyLoc (l : Launch) (g : Nat) (stage : Fin 2) : Loc :=
  ⟨.shared, g / l.block, l.sharedBase + (208 + 8 * stage.val)⟩

/-- Global access of a selected request endpoint. -/
def endpointAccess (p : Params) (row : Nat) : Acc :=
  { loc := globalLoc (p.cuQBase + 4 * row), size := 4 }

/-- The observed read of a selected request endpoint. -/
def endpointEvent (p : Params) (batch : Nat) (endpoint : Fin 2) : Event :=
  ⟨2953 + endpoint.val, .rd (endpointAccess p (batch + endpoint.val))
    ((b32 (p.qOffset (batch + endpoint.val))).toBytes.map some)⟩

/-- The scheduler and writeback region and the warp's three instructions at the common exit. -/
def EpiloguePc (pc : Nat) : Prop :=
  (2768 ≤ pc ∧ pc ≤ 3100) ∨ (7742 ≤ pc ∧ pc ≤ 7744) ∨ pc = 9205

private theorem slice_coreOps :
    ((kernel.code.drop 2768).take 333).all (fun i => Assumptions.coreOp i.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

private theorem slice_coreOp {pc : Nat} {ins : Instr} (hlo : 2768 ≤ pc) (hhi : pc ≤ 3100)
    (hc : kernel.code[pc]? = some ins) : Assumptions.coreOp ins.op = true := by
  have hi : ((kernel.code.drop 2768).take 333)[pc - 2768]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hlo]
    exact hc
  exact List.all_eq_true.mp slice_coreOps ins (List.mem_of_getElem? hi)

theorem epilogue_coreOpShared {pc : Nat} {ins : Instr}
    (hp : EpiloguePc pc) (hc : kernel.code[pc]? = some ins) : Assumptions.coreOp ins.op = true := by
  rcases hp with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | h
  · exact slice_coreOp hlo hhi hc
  · have hr : pc = 7742 ∨ pc = 7743 ∨ pc = 7744 := by omega
    rcases hr with rfl | rfl | rfl
    · rw [Flow.code_7742] at hc
      cases hc
      rfl
    · rw [Flow.code_7743] at hc
      cases hc
      rfl
    · rw [Flow.code_7744] at hc
      cases hc
      rfl
  · subst pc
    rw [Flow.code_9205] at hc
    cases hc
    rfl

theorem epilogue_off_exp2Shared {pc : Nat} (hp : EpiloguePc pc) :
    pc ∉ Assumptions.swExp2Sites := by
  unfold EpiloguePc at hp
  simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- Synchronization assumptions leave the output warp's event templates and local steps intact. -/
theorem epilogue_out_all_eq_nil {l : Launch} {g : Nat} {t : TState} (hp : EpiloguePc t.pc) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  have hload : t.pc ∉ Assumptions.tcLdDataflowSites := by
    unfold EpiloguePc at hp
    simp only [Assumptions.tcLdDataflowSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hstore : t.pc ∉ Assumptions.delayedTmemSites := by
    unfold EpiloguePc at hp
    simp only [Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  cases hc : kernel.code[t.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    exact Assumptions.out_all_eq_nil (epilogue_off_exp2Shared hp) hload hstore hc
      (epilogue_coreOpShared hp hc)

section
variable {p : Params} {l : Launch} {m : Mem0}

/-- Each output subbox issues through the ABI's rank-four O map once its operands are ready. -/
theorem storeTemplate (hpre : Pre p l m) (stage : Fin 2) (subbox : Fin 4) (g : Nat) (t : TState)
    (sl : Loc) (vs : List (BitVec 64)) (hpc : t.pc = storePc stage subbox) (hf : t.fault = none)
    (hptr : t.regs 7868 = some (.ptr 64 true (.param (param 10)) 0))
    (hcoords : (storeCoords stage subbox).mapM (readBits l g t 32) = .ok vs)
    (hshared : sharedEffAddr l g t false (stageSource stage subbox).1
      (stageSource stage subbox).2 = .ok sl) (h128 : sl.addr % 128 = 0)
    (hpolicy : cachePolicyRead l g t (some (.reg 7869)) = .ok ())
    (hOrigin : ∀ axis, 0 ≤ originOf vs axis)
    (hBox : TensorDescriptor.BoxAligned p.oMap (originOf vs)) :
    out kernel [] l g t = .ev (.tensorStore p.oMapAddress (storeSpec p sl vs) (next t)) := by
  have hTensor := outputMapOperand hpre g t (storeCoords stage subbox) hptr rfl
  have hCode : kernel.code[t.pc]? = some ⟨none, storeOp stage subbox⟩ := by
    rw [hpc, storeInstr]
  rw [PTX.Proof.out_event hf hCode rfl rfl]
  have hNonneg : ∀ axis : Fin 4, 0 ≤
      (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt := hOrigin
  have hAligned : requireBoxAligned p.oMap
      (fun axis => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt) = .ok () :=
    (requireBoxAligned_eq_ok _ _).2 hBox
  simp only [storeOp, eventTmpl, tensorStoreTmpl, tensorStoreSpec, hTensor, hcoords, hshared,
    h128, hpolicy, bind, Except.bind, pure, Except.pure, ofExec, Option.all_none, ↓reduceIte,
    TensorMode.transfer, TensorMode.rowCoordinates, hNonneg, forall_const, true_or, hAligned,
    storeSpec]
  rfl

end
end
end PTX.Kernels.TmlFa4Fwd.Epilogue
