-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Region.Base
public import Lemmas.Protocol.Region
public import Kernels.Fp16Gemm8192.Proof.Safety.EventKinds

@[expose] public section

/-! # The value of the Tensor Memory base word

A read of a CTA's base word comes after its CTA thread 0's write of the column its allocation
returned (`ThreadFacts.base_written`), and that write is the only one of the word (`base_access`).
So the read returns the write's bytes (`Hidden`, `RfWf`): the bytes of the allocation's column
(`baseValue`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

namespace TmemAlloc

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The base word holds the allocation's column** (`BaseValue`). -/
theorem baseValue (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : BaseValue L X := by
  intro g k pc a bs hrd hloc hsz
  have hg := Frame.lt_of_get hX hrd
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hrd (by simp)
  obtain ⟨r, rfl⟩ := ht.read_role hg hrd hσ rfl
  obtain ⟨pca, pcw, col, h20, h21, hcol, hhb⟩ := ht.base_written hg hrd hσ
  refine ⟨pca, pcw, col, h20, h21, hcol, ?_⟩
  obtain ⟨hlen, hbytes⟩ := hX.rf (.thread (g, k)) a bs (.inl ⟨pc, hrd⟩)
  have hblen : ((b32 col).toBytes.map some).length = 4 := by
    simp [b32, Value.toBytes, Value.bytes]
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 4
  · have hcov : ({ loc := ⟨.shared, g / L.block, L.sharedBase⟩, size := 4 } : Acc).Covers
        (a.loc.at j) := by
      rw [hloc]
      exact ⟨rfl, rfl, by simp [Loc.at], by simp [Loc.at]; omega⟩
    have hh := hX.hidden (.thread (g, k)) a bs j (.thread (g / L.block * L.block, 21))
      { loc := ⟨.shared, g / L.block, L.sharedBase⟩, size := 4 } (b32 col).toBytes (.inl ⟨pc, hrd⟩)
      (by omega) (.inl ⟨pcw, h21⟩) hcov (.direct (.inl hhb))
    have hb := hbytes j (by omega)
    revert hh hb
    cases hrf : X.rf (.thread (g, k)) j with
    | none => intro hh; exact hh.elim
    | some w' =>
      intro _ hb
      dsimp only at hb
      obtain ⟨a'', bs'', hw', hcov', hbj⟩ := hb
      have hw'' := hw'
      have hbase : Region.IsBase L (a.loc.at j) := by
        rw [hloc]
        exact ⟨rfl, by simp [Loc.at], by simp [Loc.at]; omega⟩
      rcases Region.regions hpre hX ht (Execution.MemWrites.intent hw') hcov' hbase.1 with
        ⟨hst, -⟩ | ⟨hst, -⟩ | ⟨hst, -⟩ | ⟨-, e', rfl⟩
      · exfalso
        obtain ⟨-, h1, -⟩ := hst
        obtain ⟨-, -, h2⟩ := hbase
        omega
      · exfalso
        obtain ⟨-, h1, -⟩ := hst
        obtain ⟨-, -, h2⟩ := hbase
        omega
      · exfalso
        obtain ⟨-, h1, -⟩ := hst
        obtain ⟨-, -, h2⟩ := hbase
        omega
      · obtain ⟨g', k'⟩ := e'
        obtain hw' | ⟨old, pcr, hr⟩ := hw''
        swap
        · exact (Safety.no_rmw hX ht hr).elim
        have hacc : X.Access (g', k') a'' true := .inr (.inl ⟨bs'', hw', rfl⟩)
        obtain ⟨hct, hcase⟩ := Region.base_access hX ht hacc hcov' hbase
        rcases hcase with ⟨-, h0, rfl, -⟩ | ⟨h, -⟩
        · have hlc : (a.loc.at j).cta = g / L.block := by rw [hloc]; rfl
          have hg' : g' = g / L.block * L.block := by
            have := Nat.div_add_mod g' L.block
            rw [h0] at this
            rw [← hct, hlc, Nat.add_zero, Nat.mul_comm] at this
            exact this.symm
          subst hg'
          obtain ⟨pcx, hx⟩ := hw'
          rw [h21] at hx
          simp only [Option.some.injEq, Event.mk.injEq, Kind.wr.injEq] at hx
          obtain ⟨-, rfl, rfl⟩ := hx
          have hjl : j < ((b32 col).toBytes).length := by
            simp [b32, Value.toBytes, Value.bytes]; omega
          rw [hbj, List.getElem?_map, List.getElem?_eq_getElem hjl]
          simp only [wbyte, Loc.at, hloc, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hjl,
            Option.map_some]
        · cases h
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

end TmemAlloc

end

end PTX.Kernels.Fp16Gemm8192.Proof
