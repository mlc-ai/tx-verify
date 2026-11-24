-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.TcInstrValues

@[expose] public section

/-! # The element a loader's load copies

A loader's load of part `j` reads the A map for an A part and the B map for the B part
(`ThreadFacts.loader_block`); its box lies inside the map (`ThreadFacts.tensor_bounds`), so element
`(x, y)` of the box is the matrix element at the box's origin plus `(x, y)` (`copy_readLoc`), which
no write reaches, so the load copies its launch bytes (`copy_value`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX PTX.Flow TcMma TensorDescriptor

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A load copies its element's bytes.** Byte `z` a loader's load of part `j` writes at element
`(x, y)` of its box is byte `z` of the FP16 element of `A` (an A part) or `B` at the box's origin
plus `(x, y)`. -/
theorem copy_value (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {gw kw pcw alw : Nat} {o : TensorCopy.Observation} {lw : Loader.D}
    {bw : Fin 8} {jw : Fin 3} {x y z : Nat} {v : Byte} (hobs : X.tensor (gw, kw) = some o)
    (hget : X.get (gw, kw) = some ⟨pcw, .tensorIssue alw o.spec⟩)
    (hσ : Frame.stateAt (code L) X gw kw = some (some (.inr (.loader lw))))
    (hs : lw.site = .load bw jw)
    (hz : z < 2) (hw : TensorCopy.writeByte o x y z = some v) :
    v = (Value.float .f16 ((if jw.val < 2 then P.a else P.b) ((o.spec.origin 1).toNat + y)
      ((o.spec.origin 0).toNat + x))).byteAt z := by
  have hg := Frame.lt_of_get hX hget
  obtain ⟨l', b', j', hd', hs', -, ⟨base, cls, origin, hsp, hmap, -⟩, -, -⟩ :=
    ht.tensor_issue hg hget hσ rfl
  simp only [Sum.inr.injEq, Prologue.Role.loader.injEq] at hd'
  subst hd'
  rw [hs] at hs'
  simp only [Loader.Site.load.injEq] at hs'
  obtain ⟨rfl, rfl⟩ := hs'
  obtain ⟨-, -, -, -, -, -, -, horig, hpar⟩ := ht.loader_block hg hget hσ hs
  -- the matrix the load reads
  have hbase : base = if jw.val < 2 then P.aBase else P.bBase := by
    split_ifs at hpar ⊢ with hj
    · rw [hpre.paramA] at hpar
      obtain rfl : P.aMap = alw := (Prod.mk.inj (Option.some.inj hpar)).2
      rw [hpre.mapA] at hmap
      have h := congrArg (fun s : Σ n, Descriptor n => s.2.base) (Option.some.inj hmap)
      simpa [Fp16Gemm8192.mapA, encodeTiled] using h.symm
    · rw [hpre.paramB] at hpar
      obtain rfl : P.bMap = alw := (Prod.mk.inj (Option.some.inj hpar)).2
      rw [hpre.mapB] at hmap
      have h := congrArg (fun s : Σ n, Descriptor n => s.2.base) (Option.some.inj hmap)
      simpa [Fp16Gemm8192.mapA, Fp16Gemm8192.mapB, encodeTiled] using h.symm
  have hno := ht.tensor_bounds hg hget hσ rfl
  -- the origin is the loader's, nonnegative
  obtain ⟨n0, hn0⟩ : ∃ n0 : Nat, o.spec.origin 0 = n0 := by
    have h := horig 0
    simp only [Fin.val_zero, ↓reduceIte] at h
    exact ⟨_, h⟩
  obtain ⟨n1, hn1⟩ : ∃ n1 : Nat, o.spec.origin 1 = n1 := by
    have hout : o.spec.outer = 1 := by rw [hsp]; rfl
    have h := horig 1
    have h1 : (1 : Fin (o.spec.outer + 1)).val = 1 := by simp [hout]
    simp only [h1, one_ne_zero, ↓reduceIte] at h
    exact ⟨_, h⟩
  obtain ⟨addr, hTI⟩ := (hX.tensor (gw, kw) o hobs).1
  obtain ⟨⟨⟨outer, desc, org, sb, rows⟩, mbar, ca, grp⟩, eff⟩ := o
  simp only [stageCopy] at hsp
  cases hsp
  simp only at hno hn0 hn1 hw hTI hobs ⊢
  obtain ⟨hx, hy, -⟩ :=
    copy_slot (o := ⟨stageCopy (Fp16Gemm8192.mapA base cls) origin _ _ _ _ _, eff⟩)
    rfl hw
  obtain ⟨row, col, hr, hc, hre, hce, hrl⟩ := copy_readLoc (z := z) hno hx hy hz
  have hrow : (origin 1).toNat + y = row := by
    rw [hn1] at hre ⊢; simp only [Int.toNat_natCast]; omega
  have hcol : (origin 0).toNat + x = col := by
    rw [hn0] at hce ⊢; simp only [Int.toNat_natCast]; omega
  rw [hrow, hcol]
  -- no write reaches an input matrix byte
  have hn : ∀ w dst bytes, X.MemWrites w dst bytes →
    ¬ dst.Covers ((elementLoc base row col).at z) := by
    intro w dst bytes hwr hcov
    have hint := Execution.MemWrites.intent hwr
    rcases Memory.global_access hpre hX ht hint hcov (by simp [elementLoc, Loc.at]) with
      ⟨h, -⟩ | ⟨-, ⟨-, -, h1, h2⟩, -⟩
    · cases h
    · have hdA := hpre.outputDisjointA
      have hdB := hpre.outputDisjointB
      simp only [elementLoc, Loc.at, matrixBytes] at h1 h2 hdA hdB
      split_ifs at hbase <;> subst hbase <;> omega
  have hrl' := hrl (gw / L.block)
    (L.sharedBase + InputRing.stageOff (InputRing.slotOf bw).val jw.val)
    mbar true .two
  split_ifs at hbase ⊢ with hj
  · subst hbase
    exact tensor_writeByte_of_initial hX hobs hTI hrl' hw (hpre.inputA row hr col hc z hz) hn
  · subst hbase
    exact tensor_writeByte_of_initial hX hobs hTI hrl' hw (hpre.inputB row hr col hc z hz) hn

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
