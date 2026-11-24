-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SxKvOrder

@[expose] public section

/-!
# The order of a copy of block `i` and an MMA of block `i` at a byte of its footprint

`kvOrderF` is `Sx.kvOrder_of` (`Result.Mma.KvOrder`) with the MMA's read replaced by its footprint
(`X.MmaFootprint`): the MMA need not have read its operands. This is the form
`OperandSourcesT` asks for, on maximal executions in which an MMA has been issued and not yet
started. The proof is `Sx.kvOrder_of`'s, which uses the read only for its footprint.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wz
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Sx
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The order of a copy and an MMA of one block at a byte of the MMA's footprint**, for every
consistent execution: the copy wrote the byte, it is before the MMA's read stage, and every other
write of the byte is the copy, before it, or after the read stage. -/
theorem kvOrderF (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (hR : RoleReads L X) (hE : Bar1Exits L X) (hp : NumPreRead Q L X)
    (hbox : Safety.BoxInBounds X) (G : Sr.SrPkg L kernel asms mem0 X) (hMB : Mma.MmaBcast L X)
    {m c : EvId} {d : Mma.D} {i : Nat} {o : TensorCopy.Observation} {a : Nat}
    {x y z : Nat} {l : Loc} {isB : Bool} {idx : Nat}
    (hm : Result.Mma.AtMma Q L X m d) (hmb : Result.Mma.MmaBlock d i)
    (hcb : Result.Mma.CopyBlock Q L X c i) (ho : X.tensor c = some o)
    (hTI : X.TensorIssue c a o.spec) (hw : TensorCopy.writeLoc o.spec x y z = some l)
    (hr : X.MmaFootprint m isB idx l) :
    (∃ b, TensorCopy.writeByte o x y z = some b) ∧
    modelCausality L X l (.async c (.write (.load x y z))) (.async m (.mmaRead isB idx)) ∧
    ∀ other fp bytes, X.MemWrites other fp bytes → fp.Covers l →
      other = .async c (.write (.load x y z)) ∨
      modelCausality L X l other (.async c (.write (.load x y z))) ∨
      modelCausality L X l (.async m (.mmaRead isB idx)) other := by
  obtain ⟨pcc, hec⟩ := hTI
  obtain ⟨gc, kc⟩ := c
  obtain ⟨gm, km⟩ := m
  obtain ⟨P, hσm⟩ := hm
  -- the copy's slot and box
  obtain ⟨t, ht, v1, s1, h1, hv1, hs1, hh1, hmt, hbx⟩ := copy_box hpre hX hf hec
  obtain ⟨hsp, hlc, lo1, hi1⟩ := hbx x y z l hw
  have hgc : gc < L.threads := Frame.lt_of_get hX hec
  have hc : gc / L.block < L.grid := ProA.grid_lt hgc
  have hcovC : AsyncCovers X (gc, kc) (.write (.load x y z)) l :=
    ⟨{ loc := l, size := 1 }, true, ⟨rfl, o.spec, a, ⟨pcc, hec⟩, hw, rfl⟩,
      ⟨rfl, rfl, le_refl _, Nat.lt_succ_self _⟩⟩
  have hmC : ∀ pc a' sp, X.get (gc, kc) = some ⟨pc, .tensorIssue a' sp⟩ →
      sp.mbar = kvReady L (gc / L.block) t := by
    intro pc a' sp he
    rw [hec] at he
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at he
    rw [← he.2.2]
    exact hmt
  -- the MMA's read
  have hIR : X.Intent (.async (gm, km) (.mmaRead isB idx)) { loc := l, size := 1 } false :=
    ⟨rfl, rfl, hr⟩
  have hcl1 : ({ loc := l, size := 1 } : Acc).Covers l := ⟨rfl, rfl, le_refl _, Nat.lt_succ_self _⟩
  have hcovR : AsyncCovers X (gm, km) (.mmaRead isB idx) l := ⟨_, false, hIR, hcl1⟩
  obtain ⟨hgm, hlm, hcls⟩ := Safety.async_shared hpre hX hf hIR hcl1 hsp
  have hB : isB = true := by
    rcases hcls with ⟨idx', -, -, he', -, -, -, hq⟩ | ⟨idx', -, -, he', -⟩ | ⟨x', y', z', he', -⟩
    · exfalso
      have := hq.2.1
      unfold boxBase at hi1
      omega
    · simp only [AsyncCopy.Part.mmaRead.injEq] at he'
      exact he'.1
    · cases he'
  subst hB
  obtain ⟨pcm, cm2, spec, acc, mask, hem, hbl⟩ := mma_read_at hX hcovR
  simp only [ite_true] at hbl
  have hkm : km < (X.tr gm).length := len_of_get hem
  have hcm : gm / L.block = gc / L.block := hlm.symm.trans hlc
  obtain ⟨pArr, pCp, hP⟩ := Lp.preRing_of hpre hX hf (gc / L.block) hc t ht
  have H := Lp.slot_hyp hpre hX hf hR hp G hc ht hP
  have hmt2 : gm = G.cm (gc / L.block) :=
    (G.lane (gc / L.block) hc).mma_thread (x := (gm, km)) ⟨cm2, spec, acc, mask, pcm, hem⟩ hcm
  -- the uses
  obtain ⟨hti, hcu⟩ := copy_use_block hpre hX hf hR hp ht hP (G.cm (gc / L.block)) hec hmt hcb
  have hru := read_use_block hpre hX hf hR hMB hkm hσm hmb
  obtain ⟨s, hs, -, -, hcnt, hreg⟩ := mma_b_slot hpre hX hf hR hMB hem hbl
  have hst : s = t := by
    unfold boxBase at lo1 hi1
    rcases hreg with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv1 with hv | hv <;> subst hv <;> omega
  subst hst
  rw [hcm, ← hti] at hru
  rw [hcm] at hcnt
  subst hmt2
  have hR' : X.TcAsync (G.cm (gc / L.block), km) := .inl ⟨cm2, spec, acc, mask, pcm, hem⟩
  have hcR : Ring.Kv.readUse X (Lp.slotOf Q L X (gc / L.block) s (G.cm (gc / L.block)) pArr pCp)
      (G.cm (gc / L.block), km) + 1 ≤
      okPolls (Lp.slotOf Q L X (gc / L.block) s (G.cm (gc / L.block)) pArr pCp).full
        ((X.tr (Lp.slotOf Q L X (gc / L.block) s (G.cm (gc / L.block)) pArr pCp).cm).take km) :=
    hcnt
  have hruse : Ring.Kv.readUse X (Lp.slotOf Q L X (gc / L.block) s (G.cm (gc / L.block)) pArr pCp)
      (G.cm (gc / L.block), km) = i / 3 := hru
  have hsc : SameCta L gc (G.cm (gc / L.block)) := ⟨hgc, hgm, hcm.symm⟩
  obtain ⟨h1, -⟩ := Ring.Kv.copy_read_order hX H hR' hcR hec hmt hcovC hcovR
  have hord : modelCausality L X l (.async (gc, kc) (.write (.load x y z)))
      (.async (G.cm (gc / L.block), km) (.mmaRead true idx)) :=
    ⟨.inl hsc, .direct (h1 (by rw [hcu]; exact hruse.symm.le))⟩
  refine ⟨?_, hord, ?_⟩
  · -- the byte is written
    obtain ⟨o', ho', hnot⟩ := tensor_notified_of_modelCausality hord
    rw [ho] at ho'
    cases ho'
    have hTT : TT Q L X (gc, kc) := fun h => hf.tracked gc (kc + 1) hgc h
    obtain ⟨col, row, dst, bar, hk, -, -, -⟩ :=
      Interface.copy_spec_at hpre hX hf.sound hf.ldRng hgc hec ⟨a, o.spec, rfl⟩ hTT
    simp only [Kind.tensorIssue.injEq] at hk
    obtain ⟨-, hspec⟩ := hk
    have hno := hbox hec
    rw [hspec] at hno hw
    obtain ⟨hx, hy, hz⟩ := TensorCopy.writeLoc_bounds hw
    simp [EvW.kvCopySpec, mapKv, TensorTile.count, TensorTile.step, TensorTile.rows,
      TensorTile.rowsOf, TensorDescriptor.Format.bytes] at hx hy hz
    obtain ⟨r, c', -, -, hrl⟩ := Result.Mma.kv_readLoc Q (gc / L.block) col row dst bar
      (by simpa [EvW.kvCopySpec] using hno) hx hy (Nat.lt_succ_of_le hz)
    rw [← hspec] at hrl
    exact writeByte_of_notified hX ho hnot hrl
  · -- every other write of the byte
    intro other fp bytes hmw hfc
    have hI := hmw.intent
    rcases other with ⟨g', k'⟩ | ⟨j, q⟩
    · obtain ⟨hg', hk', hc', -, -, hcl⟩ := ring_thread hpre hX hf hT hI hfc hsp
        (by unfold boxBase at hi1; omega)
      rcases hcl with ⟨-, ha', -⟩ | ⟨h, -⟩
      · obtain ⟨hc1, hn1⟩ := early_facts hX hf hk' (.inl ha')
        exact .inr (.inl ⟨hcovC, .inl (early_before_copy hpre hX hf.sound hT hf.tracked hE hR hk'
          hc1 hn1 hec (hlc.symm.trans hc') hg' hsp hc')⟩)
      · cases h
    · obtain ⟨hgj, hlj, hclj⟩ := Safety.async_shared hpre hX hf hI hfc hsp
      rcases hclj with ⟨-, -, -, -, h, -⟩ | ⟨-, -, -, -, h, -⟩ | ⟨x', y', z', rfl, -, -⟩
      · cases h
      · cases h
      have hcovO : AsyncCovers X j (.write (.load x' y' z')) l := ⟨fp, true, hI, hfc⟩
      obtain ⟨pcj, aj, spj, hej, hlj'⟩ := copy_write_at hcovO
      obtain ⟨tj, htj, vj, sj, hhj, hvj, hsj, hhj1, hmj, hbj⟩ := copy_box hpre hX hf hej
      obtain ⟨-, hlcj, loj, hij⟩ := hbj x' y' z' l hlj'
      have htt : tj = s := by unfold boxBase at loj hij lo1 hi1; omega
      subst htt
      have hcj : j.1 / L.block = gc / L.block := hlcj.symm.trans hlc
      have hmO : ∀ pc a' sp, X.get j = some ⟨pc, .tensorIssue a' sp⟩ →
          sp.mbar = kvReady L (gc / L.block) tj := by
        intro pc a' sp he
        rw [hej] at he
        simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at he
        rw [← he.2.2, hmj, hcj]
      rcases Nat.lt_trichotomy
          (Ring.Kv.copyUse X (Lp.slotOf Q L X (gc / L.block) tj (G.cm (gc / L.block)) pArr pCp) j)
          (i / 3) with hlt | heq | hgt
      · rw [← hcu] at hlt
        exact .inr (.inl (copies_lt hpre hX hf hR hp G hMB hc ht hP hcovO hcovC hmO hmC hlt))
      · rw [← hcu] at heq
        obtain ⟨rfl, rfl, rfl, rfl⟩ := copy_same_use hpre hX hf hR hp ht hP
          (G.cm (gc / L.block)) hcovO hcovC hmO hmC heq
        exact .inl rfl
      · obtain ⟨-, h2⟩ := Ring.Kv.copy_read_order hX H hR' hcR hej (by rw [hmj, hcj]; rfl)
          hcovO hcovR
        exact .inr (.inr ⟨.inl ⟨hgm, hgj, hcm.trans hcj.symm⟩,
          .direct (h2 (lt_of_eq_of_lt hruse hgt))⟩)

end
end PTX.Kernels.InklingRelDecode.Proof.Wz
