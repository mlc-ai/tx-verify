-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.Placed
public import Kernels.InklingRelDecode.Proof.Safety.PlNoNc
public import Kernels.InklingRelDecode.Proof.Safety.Regions
public import Kernels.InklingRelDecode.Proof.Interface.ScRead
public import Kernels.InklingRelDecode.Proof.Interface.LockBar0
public import Kernels.InklingRelDecode.Proof.Safety.Tensor
public import Kernels.InklingRelDecode.Proof.Protocol.IpTmIssue
public import Kernels.InklingRelDecode.Proof.Progress.Static
public import Kernels.InklingRelDecode.Proof.Interface.FootCopy

@[expose] public section

/-!
# The asynchronous accesses to shared memory, by kind and region

`async_shared`: an asynchronous stage of a consistent execution that touches a shared byte is one
of three kinds, each in its own part of the issuing thread's CTA window:

* the A operand read of a QK MMA (`mmaRead false`), in the query tile `InQ`;
* the B operand read of a QK or PV MMA (`mmaRead true`), in the two rings
  `[sharedBase, sharedBase + 196608)`;
* the write stage of a tensor load, in the two rings.

So no asynchronous access touches the words above the query tile (`(num_pre, num_iters)`, the
scratch, the role table): `async_not_high`. The proof is the case split of `sharedPlaced_of`, with
the MMA's site kept (`mma_a_qk`: a PV MMA's A operand is in Tensor Memory).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (MmShape QkIssue PvIssue)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **Only a QK MMA has a shared A operand byte.** -/
theorem mma_a_qk {d : Mma.D} {pc c : Nat} {spec : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hsh : MmShape L g d ⟨pc, .tc (.mma c spec acc mask)⟩) {idx : Nat}
    {l : Loc} (hl : spec.byteLoc .a idx = some l) : ∃ j, d.site = .qk j := by
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site with
  | qk j => exact ⟨j, rfl⟩
  | pv j =>
    simp only [MmShape, PvIssue] at hsh
    obtain ⟨db, dsc, -, -, hev⟩ := hsh
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hev
    obtain ⟨-, rfl, rfl, -⟩ := hev
    rw [Ring.Foot.pv_a_none rfl] at hl
    cases hl
  | _ => simp [MmShape] at hsh

/-- **The class of an asynchronous access to a shared byte.** -/
theorem async_shared (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {i : EvId} {p : AsyncCopy.Part} {a : Acc} {w : Bool}
    {l : Loc} (hI : X.Intent (.async i p) a w) (hc : a.Covers l) (hsp : l.space = .shared) :
    i.1 < L.threads ∧ l.cta = i.1 / L.block ∧
    ((∃ idx d P, p = .mmaRead false idx ∧ w = false ∧
        St Q L X i.1 i.2 = some (some (.w (.mma d P))) ∧ (∃ j, d.site = .qk j) ∧ InQ L l) ∨
      (∃ idx d P, p = .mmaRead true idx ∧ w = false ∧
        St Q L X i.1 i.2 = some (some (.w (.mma d P))) ∧
        L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + 196608) ∨
      (∃ x y z, p = .write (.load x y z) ∧ w = true ∧
        L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + 196608)) := by
  have hsa : a.loc.space = .shared := hc.1.symm.trans hsp
  obtain ⟨hw, hfp⟩ := hI
  cases p with
  | mmaRead isB index =>
    obtain ⟨hsz, hmf⟩ := hfp
    rcases hmf with ⟨d, s, acc, mask, ⟨pc, he⟩, hb⟩ | ⟨c, k, cta, hcp, -⟩
    · have hg := Frame.lt_of_get hX he
      obtain ⟨dd, P, hσ, hsh⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he
        (.inl ⟨d, s, acc, mask, rfl⟩)
      obtain ⟨hB, hA⟩ := mma_foot hpre hsh
      obtain ⟨-, hc2, hlo, hhi⟩ := hc
      cases isB
      · obtain ⟨h1, h2, h3, h4⟩ := hA _ _ hb
        refine ⟨hg, hc2.trans h2, .inl ⟨index, dd, P, rfl, hw, hσ, mma_a_qk hsh hb, hsp, ?_, ?_⟩⟩
        · omega
        · omega
      · obtain ⟨h1, h2, h3, h4⟩ := hB _ _ hb
        refine ⟨hg, hc2.trans h2, .inr (.inl ⟨index, dd, P, rfl, hw, hσ, ?_, ?_⟩)⟩
        · omega
        · omega
    · exact absurd hcp (Tmem1.no_cp hX _ _)
  | readLoad x y k =>
    obtain ⟨s, addr, -, hloc, -⟩ := hfp
    have h := Proof2.sourceLoc_global hloc
    rw [h] at hsa
    exact absurd hsa (by simp)
  | readCopy =>
    rcases hfp with ⟨s, ⟨pc, he⟩, -⟩ | ⟨pc, he⟩
    · exact absurd he (Interface.no_copy hX)
    · exact absurd he (Progress.no_bulkPrefetch hX)
  | readStore x y k =>
    obtain ⟨s, addr, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (no_tensorStore hX)
  | readPrefetch x y k =>
    obtain ⟨s, addr, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (no_tensorPrefetch hX)
  | writeLoad x y k =>
    obtain ⟨s, addr, ⟨pc, hget⟩, hloc, hsz⟩ := hfp
    have hg := Frame.lt_of_get hX hget
    have hTT : TT Q L X i := fun h => hf.tracked i.1 (i.2 + 1) hg h
    obtain ⟨col, row, dst, bar, hk, hd1, hd2, -⟩ :=
      Interface.copy_spec_at hpre hX hf.sound hf.ldRng hg hget ⟨addr, s, rfl⟩ hTT
    simp only [Kind.tensorIssue.injEq] at hk
    obtain ⟨-, hspec⟩ := hk
    rw [hspec] at hloc
    obtain ⟨h1, h2, h3, h4⟩ := Ring.Foot.copy_foot Q (i.1 / L.block) col row dst bar hloc
    obtain ⟨-, hc2, hlo, hhi⟩ := hc
    refine ⟨hg, hc2.trans h2, .inr (.inr ⟨x, y, k, rfl, hw, ?_, ?_⟩)⟩
    · omega
    · omega
  | writeStore x y k =>
    obtain ⟨s, addr, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (no_tensorStore hX)
  | writeCta c =>
    obtain ⟨s, targets, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (Interface.no_clc hX)
  | writeCopy =>
    obtain ⟨s, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (Interface.no_copy hX)
  | writeElem j =>
    obtain ⟨s, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (Interface.no_copy hX)
  | oldStore x y k =>
    obtain ⟨s, r, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (no_tensorStore hX)
  | oldElem j =>
    obtain ⟨s, r, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (Interface.no_copy hX)
  | readCta c => exact hfp.elim
  | readElem j => exact hfp.elim
  | writePrefetch x y k => exact hfp.elim
  | oldCopy => exact hfp.elim
  | oldLoad x y k => exact hfp.elim
  | oldCta c => exact hfp.elim
  | oldPrefetch x y k => exact hfp.elim
  | notifyCopy => exact hfp.elim
  | notifyLoad => exact hfp.elim
  | notifyCta c => exact hfp.elim
  | readsDone => exact hfp.elim
  | fullDone => exact hfp.elim
  | resolve => exact hfp.elim
  | tcNotify r => exact hfp.elim
  | mmaDone => exact hfp.elim
  | arriveOn => exact hfp.elim

/-- **No asynchronous access touches a shared byte at or above the query tile's end** (the pair
`(num_pre, num_iters)`, the scratch words, the mbarriers, the role table). -/
theorem async_not_high (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {i : EvId} {p : AsyncCopy.Part} {a : Acc} {w : Bool}
    {l : Loc} (hI : X.Intent (.async i p) a w) (hc : a.Covers l) (hsp : l.space = .shared)
    (hl : L.sharedBase + 212992 ≤ l.addr) : False := by
  obtain ⟨-, -, h⟩ := async_shared hpre hX hf hI hc hsp
  rcases h with ⟨-, -, -, -, -, -, -, hq⟩ | ⟨-, -, -, -, -, -, -, h2⟩ | ⟨-, -, -, -, -, -, h2⟩
  · exact absurd hq.2.2 (by omega)
  · omega
  · omega

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
