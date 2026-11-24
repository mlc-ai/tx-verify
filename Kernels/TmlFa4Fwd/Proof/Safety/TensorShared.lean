-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.InputActualSources
public import Kernels.TmlFa4Fwd.Proof.MbarAddressClosure
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpStartup
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Proof.RoleDispatch
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Lemmas.Flow.TcTmpl
public import Lemmas.TensorStore.TensorStoreThread
import Kernels.TmlFa4Fwd.Proof.OutputStoreFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX

/-- Each actual O subbox is read only from the output staging area of its issuing CTA. -/
theorem actualTensorOutputSharedRange {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {s : TensorStore.Spec} (hi : X.TensorStoreIssue i addr s)
    (slot : TensorTransfer.Slot s.descriptor) :
    ∃ offset, 3072 ≤ offset ∧ offset < 134144 ∧
      s.sharedLoc slot = ⟨.shared, i.1 / l.block, l.sharedBase + offset⟩ := by
  obtain ⟨_, hDesc, stage, box, hBase⟩ := OutputWarp.storeBox hp hX hi
  rcases s with ⟨⟨outer, desc, origin, shared, rows⟩, reduce⟩
  simp only [Sigma.mk.injEq] at hDesc
  obtain ⟨rfl, hD⟩ := hDesc
  have hEq : desc = p.oMap := eq_of_heq hD
  subst desc
  change shared = Epilogue.sharedSlot l i.1 stage box at hBase
  subst shared
  let offset := 3072 + 65536 * stage.val + 16384 * box.val
  let base := l.sharedBase + offset
  have hPitch : TensorTile.count p.oMap.box 0 * p.oMap.format.bytes = 128 := by
    norm_num [Params.oMap, TensorTile.count, TensorTile.step, TensorDescriptor.Format.bytes]
  obtain ⟨k, hk, hAddr⟩ := tensorSharedBoxOffset (base := base) rfl hPitch
    slot.1.isLt slot.2.1.isLt slot.2.2.isLt
  have hRows : TensorTile.rows p.oMap.box = 128 := by
    norm_num [Params.oMap, TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step]
  rw [hRows] at hk
  have hs := stage.isLt
  have hb := box.isLt
  have hLower : 3072 ≤ offset + k := by dsimp [offset]; omega
  have hUpper : offset + k < 134144 := by dsimp [offset]; omega
  refine ⟨offset + k, hLower, hUpper, ?_⟩
  change Loc.mk .shared (i.1 / l.block)
    (TensorTile.sharedByte p.oMap.box p.oMap.format.bytes p.oMap.swizzle base slot.1.val
      slot.2.1.val slot.2.2.val) = _
  rw [hAddr]
  simp only [base, Nat.add_assoc]

/-- Every shared byte read by an actual O transfer is allocated at launch. -/
theorem actualTensorOutputSharedAllocated {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {s : TensorStore.Spec} (hi : X.TensorStoreIssue i addr s)
    (slot : TensorTransfer.Slot s.descriptor) : m (s.sharedLoc slot) ≠ none := by
  obtain ⟨offset, _, hRange, hLoc⟩ := actualTensorOutputSharedRange hp hX hi slot
  obtain ⟨_, he⟩ := hi
  have hG := PTX.Proof.event_thread_lt hX he
  have hBlock : 0 < l.block := by rw [hp.block]; decide
  have hCta := (Nat.div_lt_iff_lt_mul hBlock).2 (show i.1 < l.grid * l.block from hG)
  rw [hLoc]
  exact hp.shared.2.2 _ hCta _ (by omega)

end PTX.Kernels.TmlFa4Fwd.Safety
