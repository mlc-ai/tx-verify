-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SxRingUse
public import Kernels.InklingRelDecode.Proof.Protocol.SxKRing

@[expose] public section

/-!
# The asynchronous accesses of the KV ring are ordered

`ring_async_ordered`: two conflicting asynchronous accesses of one byte of the rings
`[sharedBase, sharedBase + 196608)` are ordered in `modelCausality`. By `Safety.async_shared` such
an access is a tensor copy's write stage or an MMA's B operand read (an A operand read is in the
query tile):

* two reads do not conflict;
* a copy and a read: `copy_read_ordered` (`Ring.Kv.copy_read_order` on the byte's slot);
* two copies write bytes of one box of one slot (`copy_box`); of different uses they are ordered
  through a read of the earlier use (`Ring.Kv.copies_chain`, with the cover `kv_cover` of the MMA
  lane's reads of a released use); of the same use they are one stage (`hsame`, the premise
  `SameUseCopy`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sx
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Two write stages of tensor copies of one byte, on one slot in one use, are one stage. -/
def SameUseCopy (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {c t : Nat}, c < L.grid → t < 3 → ∀ {pArr : EvId} {pCp : Fin 8 → EvId},
    Lp.PreSlot Q L X c t pArr pCp → ∀ (cm : Nat) {i1 i2 : EvId} {x y z x' y' z' : Nat} {l : Loc},
    AsyncCovers X i1 (.write (.load x y z)) l → AsyncCovers X i2 (.write (.load x' y' z')) l →
    (∃ pc a sp, X.get i1 = some ⟨pc, .tensorIssue a sp⟩ ∧ sp.mbar = kvReady L c t) →
    (∃ pc a sp, X.get i2 = some ⟨pc, .tensorIssue a sp⟩ ∧ sp.mbar = kvReady L c t) →
    Ring.Kv.copyUse X (Lp.slotOf Q L X c t cm pArr pCp) i1 =
      Ring.Kv.copyUse X (Lp.slotOf Q L X c t cm pArr pCp) i2 →
    i1 = i2 ∧ x = x' ∧ y = y' ∧ z = z'

/-- The K or V region of slot `t` holds every byte of the slot's boxes. -/
theorem box_region {t isV slab hh : Nat} (hv : isV ≤ 1) (hs : slab ≤ 1) (hh1 : hh ≤ 1) {a : Nat}
    (hlo : boxBase L t isV slab hh ≤ a) (hhi : a < boxBase L t isV slab hh + 8192) :
    (L.sharedBase + 32768 * t ≤ a ∧ a < L.sharedBase + 32768 * t + 32768) ∨
      (L.sharedBase + 98304 + 32768 * t ≤ a ∧ a < L.sharedBase + 98304 + 32768 * t + 32768) := by
  unfold boxBase at hlo hhi
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with rfl | rfl
  · exact .inl ⟨by omega, by omega⟩
  · exact .inr ⟨by omega, by omega⟩

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hR : RoleReads L X) (hp : NumPreRead Q L X) (G : Sr.SrPkg L kernel asms mem0 X)
    (hMB : Mma.MmaBcast L X) (hpr : Lp.PreRing Q L X)
include hpre hX hf hR hp G hMB hpr

/-- **Two copies of one byte are ordered or one stage.** -/
theorem copies_ordered (hsame : SameUseCopy Q L X) {i1 i2 : EvId} {x y z x' y' z' : Nat} {l : Loc}
    (hw1 : AsyncCovers X i1 (.write (.load x y z)) l)
    (hw2 : AsyncCovers X i2 (.write (.load x' y' z')) l)
    (hne : (AsyncCopy.Ref.async i1 (.write (.load x y z)) : AsyncCopy.Ref) ≠
      .async i2 (.write (.load x' y' z'))) :
    modelCausality L X l (.async i1 (.write (.load x y z))) (.async i2 (.write (.load x' y' z')))
      ∨ modelCausality L X l (.async i2 (.write (.load x' y' z')))
        (.async i1 (.write (.load x y z))) := by
  obtain ⟨pc1, a1, sp1, he1, hl1⟩ := copy_write_at hw1
  obtain ⟨pc2, a2, sp2, he2, hl2⟩ := copy_write_at hw2
  obtain ⟨g1, k1⟩ := i1
  obtain ⟨g2, k2⟩ := i2
  obtain ⟨t1, ht1, v1, s1, h1, hv1, hs1, hh1, hm1, hb1⟩ := copy_box hpre hX hf he1
  obtain ⟨t2, ht2, v2, s2, h2, hv2, hs2, hh2, hm2, hb2⟩ := copy_box hpre hX hf he2
  obtain ⟨hsp, c1, lo1, hi1⟩ := hb1 x y z l hl1
  obtain ⟨-, c2, lo2, hi2⟩ := hb2 x' y' z' l hl2
  have hg1 : g1 < L.threads := Frame.lt_of_get hX he1
  have hg2 : g2 < L.threads := Frame.lt_of_get hX he2
  have hc12 : g1 / L.block = g2 / L.block := c1.symm.trans c2
  have htt : t1 = t2 := by unfold boxBase at lo1 hi1 lo2 hi2; omega
  subst htt
  have hc : g1 / L.block < L.grid := ProA.grid_lt hg1
  obtain ⟨pArr, pCp, hP⟩ := hpr (g1 / L.block) hc t1 ht1
  have H := Lp.slot_hyp hpre hX hf hR hp G hc ht1 hP
  set S := Lp.slotOf Q L X (g1 / L.block) t1 (G.cm (g1 / L.block)) pArr pCp with hS
  have hm1' : sp1.mbar = S.full := hm1
  have hm2' : sp2.mbar = S.full := by rw [hm2, ← hc12]; rfl
  have hreg := box_region hv1 hs1 hh1 lo1 hi1
  have hcov : ∀ {ga ka gb kb pca pcb aa ab xa ya za xb yb zb : Nat}
      {spa spb : TensorCopy.Spec},
      X.get (ga, ka) = some ⟨pca, .tensorIssue aa spa⟩ → spa.mbar = S.full →
      X.get (gb, kb) = some ⟨pcb, .tensorIssue ab spb⟩ → spb.mbar = S.full →
      AsyncCovers X (ga, ka) (.write (.load xa ya za)) l →
      AsyncCovers X (gb, kb) (.write (.load xb yb zb)) l →
      Ring.Kv.copyUse X S (ga, ka) < Ring.Kv.copyUse X S (gb, kb) →
      AsyncChain L X l ((ga, ka), .write (.load xa ya za)) ((gb, kb), .write (.load xb yb zb)) := by
    intro ga ka gb kb pca pcb aa ab xa ya za xb yb zb spa spb hea hma heb hmb hca hcb hlt
    refine Ring.Kv.copies_chain hX H hea hma heb hmb hlt hca hcb ?_
    intro jc pc sp hjc hmb' hcnt
    have hm' : sp.mbar = kvEmpty L (g1 / L.block) t1 := hmb'
    obtain ⟨kR, idx, -, hT, hcR, hpol, hcv, hpres⟩ :=
      Ring.Cover.kv_cover hpre hX hf hR hMB ht1 hjc hm' ⟨hsp, c1, hreg⟩
    refine ⟨kR, true, idx, hT, ?_, ?_, hcv, hpres⟩
    · unfold Ring.Kv.readUse
      exact hcR.trans hcnt
    · have : ((X.tr S.cm).take jc).countP (commitsTo (kvEmpty L (g1 / L.block) t1)) + 1 ≤
          okPolls (kvReady L (g1 / L.block) t1) ((X.tr S.cm).take kR) := hpol
      rw [← hcnt]
      exact this
  have hsc : SameCta L g1 g2 := ⟨hg1, hg2, hc12⟩
  rcases Nat.lt_trichotomy (Ring.Kv.copyUse X S (g1, k1)) (Ring.Kv.copyUse X S (g2, k2)) with
    hlt | heq | hgt
  · exact .inl ⟨.inl hsc, hcov he1 hm1' he2 hm2' hw1 hw2 hlt⟩
  · exfalso
    obtain ⟨hi, rfl, rfl, rfl⟩ := hsame hc ht1 hP (G.cm (g1 / L.block)) hw1 hw2
      ⟨pc1, a1, sp1, he1, hm1⟩ ⟨pc2, a2, sp2, he2, by rw [hm2, ← hc12]⟩ heq
    exact hne (by rw [hi])
  · exact .inr ⟨.inl ⟨hg2, hg1, hc12.symm⟩, hcov he2 hm2' he1 hm1' hw2 hw1 hgt⟩
/-- **Two conflicting asynchronous accesses of a byte of the rings are ordered.** -/
theorem ring_async_ordered (hsame : SameUseCopy Q L X) {i j : EvId} {p q : AsyncCopy.Part}
    {a b : Acc} {l : Loc} (hc : Conflict X (.async i p) (.async j q) a b) (ha : a.Covers l)
    (hb : b.Covers l) (hsp : l.space = .shared) (hhi : l.addr < L.sharedBase + 196608) :
    modelCausality L X l (.async i p) (.async j q) ∨
      modelCausality L X l (.async j q) (.async i p) := by
  obtain ⟨hne, we, wf, hie, hif, hw, -⟩ := hc
  have hca : AsyncCovers X i p l := ⟨a, we, hie, ha⟩
  have hcb : AsyncCovers X j q l := ⟨b, wf, hif, hb⟩
  obtain ⟨-, -, h1⟩ := Safety.async_shared hpre hX hf hie ha hsp
  obtain ⟨-, -, h2⟩ := Safety.async_shared hpre hX hf hif hb hsp
  rcases h1 with ⟨-, -, -, -, -, -, -, hq⟩ | ⟨idx, -, -, rfl, rfl, -⟩ | ⟨x, y, z, rfl, rfl, -⟩
  · exact absurd hq.2.1 (by omega)
  · rcases h2 with ⟨-, -, -, -, -, -, -, hq⟩ | ⟨idx', -, -, rfl, rfl, -⟩ | ⟨x', y', z', rfl, rfl, -⟩
    · exact absurd hq.2.1 (by omega)
    · exfalso
      rcases hw with h | h <;> cases h
    · exact (copy_read_ordered hpre hX hf hR hp G hMB hpr hcb hca).symm
  · rcases h2 with ⟨-, -, -, -, -, -, -, hq⟩ | ⟨idx', -, -, rfl, rfl, -⟩ | ⟨x', y', z', rfl, rfl, -⟩
    · exact absurd hq.2.1 (by omega)
    · exact copy_read_ordered hpre hX hf hR hp G hMB hpr hca hcb
    · exact copies_ordered hpre hX hf hR hp G hMB hpr hsame hca hcb hne

end
end PTX.Kernels.InklingRelDecode.Proof.Sx
