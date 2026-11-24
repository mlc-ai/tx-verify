-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Protocol.Sync
public import Kernels.TcGemm.Proof.Protocol.Memory

@[expose] public section

/-! # `tc_gemm`: the address of the allocation

The first barrier publishes the allocated address: a thread that read `tslot` passed its first
barrier, so thread 0 arrived at it (`member_bar`), after its address store, which then happens
before the read (`sync0`). The store is the only write of `tslot` (`Wit.tslot_writer`), so the
read returns its bytes (`rd_val`): a word whose low 16 bits are the allocated column
(`rd_good`), which every thread keeps (`c_eq`). -/

namespace PTX.Kernels.TcGemm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}

section
variable (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre hX hW

/-- Once a thread has passed its first barrier, thread 0 has made its issue events. -/
theorem issued_of_passed {g : Nat} (hg : g < 128) (hm : hd g < m g) : 8 < m 0 := by
  have := hd_pos (g := g)
  have hb : X.IsBarrier (g, hd g - 1) 0 none Flow.bar_0 := by
    show X.get _ = _; rw [hW.get_of_lt hg (by omega), fullAt_bar0]; rfl
  have hl := hW.length g hg
  obtain ⟨j, pc, hb0, hord⟩ := member_bar hpre hX hW hb (by omega) (h := 0) (by decide)
  have kg := hW.barK (k := ((X.tr g).take (hd g - 1)).countP Execution.isBar) ⟨⟨0, _, hb⟩, rfl⟩
  have k0 := hW.barK (k := ((X.tr 0).take j).countP Execution.isBar) ⟨⟨0, _, hb0⟩, rfl⟩
  have := ldIdx_eq (g := g) (P g)
  have := tl_ge (g := g) (P g)
  have := ldIdx_eq (g := 0) (P 0)
  have := tl_ge (g := 0) (P 0)
  have h0 : hd 0 = 9 := rfl
  rcases kg.2.2 with ⟨-, h1⟩ | ⟨h1, -⟩ <;> rcases k0.2.2 with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> omega

/-- **The address read.** A thread that read the address read the bytes thread 0 stored. -/
theorem rd_val {g : Nat} (hg : g < 128) (hm : hd g < m g) :
    8 < m 0 ∧ (P g).rd = (b32 (P 0).col).toBytes.map some := by
  have hm0 := issued_of_passed hpre hX hW hg hm
  refine ⟨hm0, ?_⟩
  set S := L.sharedBase
  have hw : X.Writes (0, 1) { loc := tslot S, size := 4 } (b32 (P 0).col).toBytes :=
    ⟨Flow.tmemAlloc_0, by rw [hW.get_of_lt (by decide) (by omega), fullAt_head _ (by decide)]; rfl⟩
  have hr : X.Reads (g, hd g) { loc := tslot S, size := 4 } (P g).rd :=
    ⟨Flow.load_0, by rw [hW.get_of_lt hg hm, fullAt_rd]; rfl⟩
  have hl := hW.length g hg
  have h0 : hd 0 = 9 := rfl
  have hb4 : (b32 (P 0).col).toBytes.length = 4 := by simp [b32, Value.toBytes, Value.bytes]
  have hhb : baseCausality L X (0, 1) (g, hd g) :=
    sync0 hpre hX hW (by decide) hg (by decide) (by omega) le_rfl (by omega)
  obtain ⟨hlen4, hsrc⟩ := hX.rf (.thread (g, hd g)) _ _ (.inl hr)
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 4
  swap
  · rw [List.getElem?_eq_none (by simp at hlen4; omega),
      List.getElem?_eq_none (by simp [hb4]; omega)]
  have hs := hsrc k hk
  have hcov : Acc.Covers { loc := tslot S, size := 4 }
      (({ loc := tslot S, size := 4 } : Acc).loc.at k) := Acc.covers_at hk
  cases hrf : X.rf (.thread (g, hd g)) k with
  | none =>
    have := hX.hidden (.thread (g, hd g)) _ _ k (.thread (0, 1)) _ _
      (.inl hr) hk (.inl hw) hcov (.direct (.inl hhb))
    rw [hrf] at this; exact this.elim
  | some w =>
    rw [hrf] at hs
    obtain ⟨a', bs', hw', hcov', hbyte⟩ := hs
    obtain ⟨rfl, rfl, rfl⟩ := hW.tslot_writer hw' hk hcov'
    rw [hbyte, List.getElem?_map, List.getElem?_eq_getElem (by omega)]
    simp [wbyte, Loc.at, tslot]

/-- A thread that read the address read a word whose low 16 bits are the column. -/
theorem rd_good {g : Nat} (hg : g < 128) (hm : hd g < m g) :
    rdCol (P g).rd = some (P 0).col := by
  obtain ⟨-, hrd⟩ := rd_val hpre hX hW hg hm
  have hc := hW.col 0
  rw [hrd, rdCol, rebuild_scalar (by simp [b32, Value.bytes]) rfl]
  simp only [wordOf, Option.map_some, Option.some.injEq, b32]
  rw [mask16, BitVec.toNat_and]
  have h1 : (truncBits 32 (BitVec.ofNat 64 (P 0).col)).toNat = (P 0).col := by
    simp [truncBits]; omega
  have h2 : (truncBits 32 (BitVec.ofInt 64 65535)).toNat = 2 ^ 16 - 1 := by decide
  rw [h1, h2, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

/-- The column every thread keeps is the allocated one. -/
theorem c_eq {g : Nat} (hg : g < 128) (hm : hd g + 1 < m g) : (P g).c = (P 0).col := by
  have h1 := hW.good g hg hm
  rw [rd_good hpre hX hW hg (by omega)] at h1
  exact (Option.some.inj h1).symm

/-- No thread stops right after the read. -/
theorem rd_ok {g : Nat} (hg : g < 128) (hm : hd g < m g) : rdCol (P g).rd ≠ none := by
  rw [rd_good hpre hX hW hg hm]; simp

end

end

end PTX.Kernels.TcGemm.Proof
