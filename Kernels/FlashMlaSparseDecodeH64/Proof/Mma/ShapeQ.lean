-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Ev
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Lemmas.Flow.Step.TcCpWs
import Lemmas.Flow.Step.ShapeAsync
import Lemmas.Flow.TensorIssueCopy
import Lemmas.Flow.CommitSelf
import Lemmas.Tensor.LoadBox
import Lemmas.Flow.TensorLoadFacts
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid

@[expose] public section

/-! # The MMA warp's events by state: the election, the length reads and the query

One declaration per site family (`shape_open`, then the inversion lemma of its instruction). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_elect (d : D) (hs : d.site = .elect) : (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  rcases fires_elect_mask (readBits_of (rg 794)) hf with ⟨inst, ld, rfl⟩ | ⟨f, rfl⟩
  · exact .inl ⟨inst, ld, rfl⟩
  · exact .inr ⟨f, rfl⟩

theorem shapeAt_loadTopk (d : D) (hs : d.site = .loadTopk) : (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  exact fires_ncLoad_kind hf

theorem shapeAt_loadExtra (d : D) (hs : d.site = .loadExtra) :
    (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  exact fires_ncLoad_kind hf

theorem shapeAt_trap (d : D) (hs : d.site = .trap) : (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  simp only [eventTmpl, Fires] at hf
  exact ⟨_, congrArg Event.kind hf.1⟩

/-- A 32-bit destination register as a cluster shared address of the thread's CTA. -/
private theorem dst_loc {t : TState} {r : Nat} {x : BitVec 64} (hr : t.regs r = some (.bits 32 x)) :
    sharedEffAddr L g t true r 0 = .ok ⟨.shared, g / L.block, (truncBits 32 x).toNat⟩ := by
  simp [sharedEffAddr, readReg, hr, readBits, bind, Except.bind, pure, Except.pure, truncBits]

/-- The query tile's byte `n` as a 32-bit word. -/
private theorem qDst (hp : Pre P L m) {n : Int} (h0 : 0 ≤ n) (hn : n < 65536) :
    (truncBits 32 (Arith32.addi (sbw L) n)).toNat = L.sharedBase + n.toNat := by
  have h1 := hp.sharedBase
  have h3 := hp.sharedRange
  unfold sharedBytes at h3
  simp only [Arith32.addi, Arith32.r32, Arith32.i32, sbw, truncBits, BitVec.toNat_ofNat,
    BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

private theorem qDst0 (hp : Pre P L m) : (truncBits 32 (sbw L)).toNat = L.sharedBase + 0 := by
  have h1 := hp.sharedBase
  have h3 := hp.sharedRange
  unfold sharedBytes at h3
  simp only [sbw, truncBits, BitVec.toNat_ofNat]
  omega

/-- A query load: its issue on `bar_q_tma` of the query map's 8192-byte box to byte `c` of the
workspace, or undefined behaviour. -/
theorem qLoad_ev (hp : Pre P L m) {t : TState} {dst r0 : Nat} {pol : Option Opnd}
    {pc : Nat} {e : Event} {o : Option TState} {x : BitVec 64} {c k : Nat} (hk : k < 8)
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.cpTensor true false dst 0 (.reg 3058) [.reg r0, .reg 812, .reg 459, .reg 460] 811 0 none
        .tile pol)) e o)
    (hr0 : t.regs r0 = some (b32 (64 * k))) (hr1 : t.regs 812 = some (b32 0))
    (hr2 : t.regs 459 = some (b32 (ctaidX L g))) (hr3 : t.regs 460 = some (b32 (ctaidY L g)))
    (hm : t.regs 3058 = some (.bits 64 (BitVec.ofNat 64 (P.param1Base + 128))))
    (hb : t.regs 811 = some (.bits 32 (Arith32.addi (sbw L) 222776)))
    (hdr : t.regs dst = some (.bits 32 x)) (hx : (truncBits 32 x).toNat = L.sharedBase + c) :
    (∃ a s, e.kind = .tensorIssue a s ∧ s.mbar = smLoc L g (qTmaW L) 0 ∧
      TensorTransfer.bytes s.descriptor = 8192 ∧
      s.sharedBase = ⟨.shared, g / L.block, L.sharedBase + c⟩ ∧ QBox s.descriptor ∧
      (∃ b, L.paramObjects (param "1") = some (mapParam, b) ∧
        L.tensorMaps (b + 128) = some ⟨s.outer, s.descriptor⟩) ∧
      s.rows = none ∧ BoxOrigin s.origin [64 * k, 0, ctaidX L g, ctaidY L g]) ∨
      ∃ f, e.kind = .ub f := by
  by_cases hk : ∃ a s, e.kind = .tensorIssue a s
  · obtain ⟨a, s, hk⟩ := hk
    have hcp := fires_cpTensor_copy hf hk
    obtain ⟨hma, hmb, d, hd, -, hdesc, hrows⟩ := tensorLoadCopy_ok hcp
    have hlt := (ctaid_lt hp g)
    have hsq := hp.sqLt
    have hb4 := hp.bLt
    have hsb := TensorCopy.tensorLoadCopy_dst hcp
    rw [dst_loc hdr, hx] at hsb
    rw [tensorMapAddress_bits hm] at hma
    obtain rfl := (Except.ok.inj hma).symm
    have h64 : (BitVec.ofNat 64 (P.param1Base + 128)).toNat = P.param1Base + 128 := by
      have := hp.param1Range
      simp only [BitVec.toNat_ofNat]
      omega
    rw [h64] at hd
    simp only [TensorMode.transfer] at hdesc
    have hmap : L.tensorMaps (P.param1Base + 128) = some ⟨s.outer, s.descriptor⟩ := by
      rw [hd, ← hdesc]
    rw [hp.mapQBind] at hd
    have hq := Option.some.inj hd
    have hb' := congrArg (fun y : (n : Nat) × TensorDescriptor.Descriptor n =>
      (TensorTransfer.bytes y.2, TensorTile.count y.2.box 0, TensorTile.rows y.2.box,
        y.2.format.bytes, y.2.swizzle)) hq
    simp only [Prod.mk.injEq] at hb'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hb'
    rw [← hdesc] at h1 h2 h3 h4 h5
    refine .inl ⟨_, s, hk, ?_, ?_, (Except.ok.inj hsb).symm, ⟨?_, ?_, ?_, ?_⟩,
      ⟨⟨_, hp.param1Object, hmap⟩, hrows.mpr rfl, ?_⟩⟩
    · simp only [↓reduceIte] at hmb
      rw [mbarClusterLoc_bits hb (sbw_m8 hp (c := 222776) (by decide))] at hmb
      exact (Except.ok.inj hmb).symm
    · refine h1.symm.trans ?_
      simp [mapQ, encodeTiled, TensorTransfer.bytes, TensorTile.rows, TensorTile.rowsOf,
        TensorTile.count, TensorTile.step, TensorDescriptor.Format.bytes]
    · refine h2.symm.trans ?_
      simp [mapQ, encodeTiled, TensorTile.count, TensorTile.step]
    · refine h3.symm.trans ?_
      simp [mapQ, encodeTiled, TensorTile.rows, TensorTile.rowsOf, TensorTile.count,
        TensorTile.step]
    · refine h4.symm.trans ?_
      simp [mapQ, encodeTiled, TensorDescriptor.Format.bytes]
    · exact h5.symm
    · exact tensorLoadCopy_origin_regs hcp hr0 hr1 hr2 hr3 (by omega) (by omega) (by omega)
        (by omega)
  · refine .inr ?_
    rcases shape_cpTensor (P := fun e : Event =>
      (∃ a s, e.kind = .tensorIssue a s) ∨ ∃ f, e.kind = .ub f) hf
      (fun a s _ => .inl ⟨a, s, rfl⟩) (fun f => .inr ⟨f, rfl⟩) with h | h
    · exact absurd h hk
    · exact h

theorem shapeAt_qLoad (hp : Pre P L m) (d : D) (hs : ∃ k, d.site = .qLoad k) :
    (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  obtain ⟨k, hs⟩ := hs
  cases hs
  fin_cases k <;> shape_open
  · refine qLoad_ev hp ?_ hf ?_ (rg 812) (rg 459) (rg 460) (rg 3058) (rg 811) rg_ (qDst0 hp) <;>
      first | decide | exact rg_
  all_goals
    refine qLoad_ev hp ?_ hf ?_ (rg 812) (rg 459) (rg 460) (rg 3058) (rg 811) rg_
      (qDst hp (by decide) (by decide)) <;> first | decide | exact rg_

theorem shapeAt_qArrive (hp : Pre P L m) (d : D) (hs : d.site = .qArrive) :
    (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  exact shape_arrive
    (P := fun e : Event => e.kind = .arrive (smLoc L g (qTmaW L) 0) 65536 1 true .cta)
    hf (by rw [hpc]; decide) (readBits_of (rg 827)) rfl
    (mbarLoc_bits (rg 811) (sbw_m8 hp (c := 222776) (by decide))) rfl

theorem shapeAt_qWait (d : D) (hs : d.site = .qWait) : (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  exact fires_wait_reg (by rw [hpc]; decide) (rg 811) (rg 812) hf

theorem shapeAt_qCopyWait (d : D) (hs : d.site = .qCopyWait) :
    (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  exact fires_wait_reg (by rw [hpc]; decide) (rg 843) (rg 812) hf

theorem shapeAt_fence (d : D)
    (hs : d.site = .qFence ∨ d.site = .qCopyFence ∨ d.site = .kvFence ∨ d.site = .soFence) :
    (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  rcases hs with hs | hs | hs | hs <;> cases hs <;> shape_open <;>
    (simp only [eventTmpl, Fires] at hf; exact congrArg Event.kind hf.1)

theorem shapeAt_qCopy (d : D) (hs : ∃ k, d.site = .qCopy k) : (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  obtain ⟨k, hs⟩ := hs
  cases hs
  fin_cases k <;> shape_open <;> exact cp_ev hf rg_ rg_ rfl (by decide)

theorem shapeAt_qCopyCommit (d : D) (hs : d.site = .qCopyCommit) :
    (code P L g).ShapeAt (EvK L g) d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  exact fires_commit_self (rg 843) hf

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
