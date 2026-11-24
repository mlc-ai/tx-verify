-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Ordered
public import Lemmas.Step.TensorDrain
public import Lemmas.Tensor.TensorAddress
public import Mathlib.Algebra.BigOperators.Fin
public import Kernels.Fp16Gemm8192.Proof.Safety.EventKinds

@[expose] public section

/-! # The global bytes the tensor loads read

A tensor load reads the A or B matrix through its map (`tensor_issue`): every global byte its
box covers is an element of that matrix, which the launch initializes. No write covers such a
byte: the threads write shared memory (`write_shared`), the tensor loads, the cancellation
responses and the shared staging of the TMA stores are shared, and the TMA stores write the
output matrix through the output map (`store_map`), disjoint from the inputs. So the tensor loads'
sources are fixed (`tensorSources`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

namespace InputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A byte an 8192 x 8192 FP16 map addresses is a byte of an element of its matrix. -/
theorem matrix_lookup {base bi bo : Nat} {sw : TensorSwizzle.Mode}
    {cls : TensorDescriptor.AllocationClass} {coord : Fin 2 → Int} {byte address : Nat}
    (h : TensorAddress.lookup
      (TensorDescriptor.geometry (encodeTiled .f16 base 8192 8192 16384 bi bo sw cls)) coord byte =
        some address) :
    ∃ row col, row < 8192 ∧ col < 8192 ∧ byte < 2 ∧
      (elementLoc base row col).at byte = ⟨.global, 0, address⟩ := by
  obtain ⟨hin, hbyte, ha⟩ := TensorAddress.lookup_some_iff _ _ _ _ |>.mp h
  have h0 := hin 0
  have h1 := hin 1
  norm_num [TensorAddress.InBounds, TensorDescriptor.geometry, encodeTiled,
    TensorDescriptor.Format.bytes] at h0 h1 hbyte
  refine ⟨(coord 1).toNat, (coord 0).toNat, by omega, by omega, by omega, ?_⟩
  have hadd : address = base + 2 * (8192 * (coord 1).toNat + (coord 0).toNat) + byte := by
    rw [ha]
    unfold TensorAddress.byteAddress
    rw [Fin.sum_univ_two]
    change base + ((coord 0).toNat * 2 + (coord 1).toNat * 16384) + byte =
      base + 2 * (8192 * (coord 1).toNat + (coord 0).toNat) + byte
    omega
  simp only [elementLoc, Loc.at]
  rw [hadd]

/-- A TMA store through the output map writes a byte of an element of the output matrix. -/
theorem store_writeLoc_d {s : TensorStore.Spec} {base : Nat}
    {cls : TensorDescriptor.AllocationClass}
    (hd : (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
      ⟨1, Fp16Gemm8192.mapD base cls⟩) {x y z : Nat} {l : Loc}
    (h : TensorStore.writeLoc s x y z = some l) :
    ∃ row col byte, row < 8192 ∧ col < 8192 ∧ byte < 2 ∧ l = (elementLoc base row col).at byte := by
  obtain ⟨⟨outer, desc, origin, sb, rows⟩, red⟩ := s
  simp only [Sigma.mk.injEq] at hd
  obtain ⟨rfl, hdesc⟩ := hd
  cases hdesc
  simp only [TensorStore.writeLoc, Option.bind_eq_some_iff, TensorStore.destination,
    Option.map_eq_some_iff] at h
  obtain ⟨slot, -, addr, hga, rfl⟩ := h
  obtain ⟨row, col, hr, hc, hb, he⟩ := matrix_lookup (base := base) (bi := 32) (bo := 128)
    (sw := .b64) (cls := cls) hga
  exact ⟨row, col, _, hr, hc, hb, he.symm⟩

/-- An output matrix byte is not an input matrix byte. -/
theorem output_ne_input (hpre : Pre P L mem0) {base : Nat} (hbase : base = P.aBase ∨ base = P.bBase)
    {row col byte row' col' byte' : Nat} (hr : row < 8192) (hc : col < 8192) (hb : byte < 2)
    (hr' : row' < 8192) (hc' : col' < 8192) (hb' : byte' < 2) :
    (elementLoc P.dBase row' col').at byte' ≠ (elementLoc base row col).at byte := by
  intro h
  simp only [elementLoc, Loc.at, Loc.mk.injEq, true_and] at h
  have hA := hpre.outputDisjointA
  have hB := hpre.outputDisjointB
  unfold matrixBytes at hA hB
  rcases hbase with rfl | rfl <;> omega

/-- A one-byte global location covered by an access is in the access's space. -/
theorem covers_space {a : Acc} {l : Loc} (h : a.Covers l) : l.space = a.loc.space := h.1

/-- **No write covers an input matrix byte.** The threads write shared memory, the tensor loads
and the cancellation responses write shared memory, and the TMA stores write the output matrix,
disjoint from the input matrices; the kernel issues no linear copy and no read-modify-write. -/
theorem input_no_writer (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {base row col byte : Nat} (hbase : base = P.aBase ∨ base = P.bBase)
    (hr : row < 8192) (hc : col < 8192) (hb : byte < 2) :
    ∀ w dst bytes, X.MemWrites w dst bytes → ¬ dst.Covers ((elementLoc base row col).at byte) := by
  intro w dst bytes hw hcov
  have hsp := covers_space hcov
  simp only [elementLoc, Loc.at] at hsp
  rcases w with e | ⟨j, p⟩
  · rcases hw with ⟨pc, he⟩ | ⟨old, pc, he⟩
    swap
    · exact Safety.no_rmw hX ht he
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    have := ht.write_shared hg he hσ rfl
    rw [this] at hsp
    cases hsp
  · cases p with
    | writeStore x y z =>
      obtain ⟨o, addr, b, -, ⟨pc, he⟩, hwl, -, hsz, -⟩ := hw
      have hg := Frame.lt_of_get hX he
      obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
      obtain ⟨hpar, hmap⟩ := ht.store_map hg he hσ rfl
      rw [hpre.paramD] at hpar
      obtain rfl : addr = P.dMap := (Prod.mk.inj (Option.some.inj hpar)).2.symm
      rw [hpre.mapD] at hmap
      have hdl := covers_one hsz hcov
      obtain ⟨row', col', byte', hr', hc', hb', hloc⟩ :=
        store_writeLoc_d (Option.some.inj hmap).symm hwl
      rw [hloc] at hdl
      exact output_ne_input hpre hbase hr hc hb hr' hc' hb' hdl.symm
    | writeLoad x y z =>
      obtain ⟨o, addr, b, -, ⟨pc, he⟩, hwl, -, -, -⟩ := hw
      have hg := Frame.lt_of_get hX he
      obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
      obtain ⟨-, -, -, -, -, -, -, hroute, -⟩ := ht.tensor_issue hg he hσ rfl
      have hshared : dst.loc.space = .shared := by
        simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at hwl
        obtain ⟨slot, -, hloc⟩ := hwl
        rw [← hloc]
        exact hroute.2.1
      rw [hshared] at hsp
      cases hsp
    | writeCta c =>
      obtain ⟨s, tg, ⟨pc, he⟩, -, -, -, -, rfl, -⟩ := hw
      have hg := Frame.lt_of_get hX he
      obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
      obtain ⟨bar, -, -, -, hresp, -⟩ := (ht.ring_event hg he hσ).clc s tg rfl
      rw [hresp] at hsp
      cases hsp
    | writeCopy =>
      obtain ⟨src, ⟨pc, he⟩, -⟩ := hw
      have hg := Frame.lt_of_get hX he
      obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
      exact (ht.ring_event hg he hσ).copy src rfl
    | writeElem k =>
      obtain ⟨src, ⟨pc, he⟩, -⟩ := hw
      have hg := Frame.lt_of_get hX he
      obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
      exact (ht.ring_event hg he hσ).copy src rfl
    | _ => exact hw.elim

/-- **The tensor loads' sources are fixed.** Each tensor load is routed, through a valid map of
the A or B matrix, and each global byte its box reads is an initialized byte of that matrix that no
write covers. -/
theorem tensorSources (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : TensorSources L mem0 X := by
  intro i addr s hi
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨-, b, j, -, -, -, ⟨base, cls, origin, hsp, hmap, hpar⟩, hroute, -⟩ :=
    ht.tensor_issue hg he hσ rfl
  have hbase : (base = P.aBase ∧ cls = P.aClass) ∨ (base = P.bBase ∧ cls = P.bClass) := by
    rcases hpar with h | h
    · rw [hpre.paramA] at h
      obtain rfl : addr = P.aMap := (Prod.mk.inj (Option.some.inj h)).2.symm
      rw [hpre.mapA] at hmap
      have hm := eq_of_heq (Sigma.mk.inj (Option.some.inj hmap)).2
      exact .inl ⟨(congrArg TensorDescriptor.Descriptor.base hm).symm,
        (congrArg TensorDescriptor.Descriptor.allocationClass hm).symm⟩
    · rw [hpre.paramB] at h
      obtain rfl : addr = P.bMap := (Prod.mk.inj (Option.some.inj h)).2.symm
      rw [hpre.mapB] at hmap
      have hm := eq_of_heq (Sigma.mk.inj (Option.some.inj hmap)).2
      exact .inr ⟨(congrArg TensorDescriptor.Descriptor.base hm).symm,
        (congrArg TensorDescriptor.Descriptor.allocationClass hm).symm⟩
  have hal : base % 16 = 0 := by
    rcases hbase with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hpre.inputAlignment.1
    · exact hpre.inputAlignment.2.1
  obtain ⟨mb, hmb⟩ : ∃ mb, s.mbar = mb := ⟨_, rfl⟩
  rw [hmb] at hsp
  subst hsp
  refine ⟨hroute, Fp16Gemm8192.mapA_valid hal, by
    change 0 < TensorTransfer.bytes (Fp16Gemm8192.mapA base cls)
    norm_num [TensorTransfer.bytes, Fp16Gemm8192.mapA, encodeTiled, TensorTile.count,
      TensorTile.step, TensorTile.rows, TensorTile.rowsOf, TensorDescriptor.Format.bytes], ?_⟩
  intro slot a hsrc
  have hga : (stageCopy (Fp16Gemm8192.mapA base cls) origin (g / L.block)
      (L.sharedBase + stageOff _ _) _ true .two).globalAddress slot = some a := by
    unfold TensorCopy.source at hsrc
    split at hsrc
    · rename_i a' h'
      cases hsrc
      exact h'
    · cases hsrc
  obtain ⟨row, col, hr, hc, hb, hel⟩ := matrix_lookup (base := base) (bi := 64) (bo := 128)
    (sw := .b128) (cls := cls) hga
  rw [← hel]
  rcases hbase with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact ⟨_, hpre.inputA row hr col hc _ hb, input_no_writer hpre hX ht (.inl rfl) hr hc hb⟩
  · exact ⟨_, hpre.inputB row hr col hc _ hb, input_no_writer hpre hX ht (.inr rfl) hr hc hb⟩

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
