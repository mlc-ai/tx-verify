-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaWarpStartup
public import Kernels.TmlFa4Fwd.Proof.MmaGeometry
public import Lemmas.Flow.Join

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- Eight Q descriptor registers, one for each fragment in a stage. -/
def qDescriptorFacts (l : Launch) (stage : Fin 2) : List (Nat × Value) :=
  (List.finRange 8).map fun step =>
    (9624 + step.val, b64 (sharedDescriptorWord (qStart l stage + qkFragment step) 16))

private theorem packWord {lo : Nat} (hl : lo < 2 ^ 32) :
    joinValue (b32 lo) (Value.bits (64 / 2) (truncBits (64 / 2) (BitVec.ofInt 64 1073758272))) =
      b64 (lo + 2 ^ 32 * 1073758272) := by
  have hh : truncBits (64 / 2) (BitVec.ofInt 64 1073758272) = BitVec.ofNat 64 1073758272 := rfl
  rw [hh]
  unfold b32 b64
  rw [Nat.mul_comm (2 ^ 32) 1073758272]
  exact join_bits32 rfl rfl hl (by decide)

private theorem packWordOffset {lo off : Nat} {imm : Int} (he : imm = (off : Int))
    (hl : lo + off < 2 ^ 32) :
    joinValue (Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 lo) +
      truncBits 32 (BitVec.ofInt 64 imm))))
      (Value.bits (64 / 2) (truncBits (64 / 2) (BitVec.ofInt 64 1073758272))) =
        b64 (lo + off + 2 ^ 32 * 1073758272) := by
  rw [he, BitVec.ofInt_natCast, truncBits_ofNat (by omega : lo < 2 ^ 32) (by decide),
    truncBits_ofNat (by omega : off < 2 ^ 32) (by decide),
    ← BitVec.ofNat_add, truncBits_ofNat hl (by decide)]
  exact packWord hl

private theorem startupPack {l : Launch} {g lo : Nat} (hLow : lo + 1030 < 2 ^ 32) :
    Seg kernel [] l g 17 1917 [(2450, b32 lo)] 1934
      [(9624, b64 (lo + 2 ^ 32 * 0x40004040)),
       (9625, b64 (lo + 2 + 2 ^ 32 * 0x40004040)),
       (9626, b64 (lo + 4 + 2 ^ 32 * 0x40004040)),
       (9627, b64 (lo + 6 + 2 ^ 32 * 0x40004040)),
       (9628, b64 (lo + 1024 + 2 ^ 32 * 0x40004040)),
       (9629, b64 (lo + 1026 + 2 ^ 32 * 0x40004040)),
       (9630, b64 (lo + 1028 + 2 ^ 32 * 0x40004040)),
       (9631, b64 (lo + 1030 + 2 ^ 32 * 0x40004040)),
       (9632, b32 0x8200490), (9633, b32 0x8210490)] := by
  have h0 := packWord (lo := lo) (by omega)
  have h2 := packWordOffset (lo := lo) (off := 2) (imm := 2) rfl (by omega)
  have h4 := packWordOffset (lo := lo) (off := 4) (imm := 4) rfl (by omega)
  have h6 := packWordOffset (lo := lo) (off := 6) (imm := 6) rfl (by omega)
  have h1024 := packWordOffset (lo := lo) (off := 1024) (imm := 1024) rfl (by omega)
  have h1026 := packWordOffset (lo := lo) (off := 1026) (imm := 1026) rfl (by omega)
  have h1028 := packWordOffset (lo := lo) (off := 1028) (imm := 1028) rfl (by omega)
  have h1030 := packWordOffset (lo := lo) (off := 1030) (imm := 1030) rfl (by omega)
  intro t ht
  seg_fp ht using
    (try simp only [h0, h2, h4, h6, h1024, h1026, h1028, h1030]
     try rfl)

private theorem packedQWord (l : Launch) (j : Fin 8) :
    sharedDescriptorWord (qStart l 1 + qkFragment j) 16 =
      startupQLow l + qkFragment j / 16 + 2 ^ 32 * 0x40004040 := by
  unfold sharedDescriptorWord startupQLow qStart
  have hStep : qkFragment j % 16 = 0 := by fin_cases j <;> decide
  have hStage : (1 : Fin 2).val = 1 := rfl
  rw [hStage]
  omega

/-- The decoded local segment computes the first Q descriptors and lane index. -/
theorem startupQRegistersCore {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) :
    Seg kernel [] l g 18 1917 [(2450, b32 (startupQLow l))] 1935
      ((1180, b32 (laneOf l g)) :: (9632, b32 0x8200490) :: (9633, b32 0x8210490) ::
        qDescriptorFacts l 1) := by
  have hShared := hp.shared.2.1
  have hLo : startupQLow l + 1030 < 2 ^ 32 := by unfold startupQLow; omega
  intro t ht
  obtain ⟨u, hr, hu⟩ := startupPack hLo t ht
  have hStep : Seg kernel [] l g 1 1934 [] 1935 [(1180, b32 (laneOf l g))] := by
    intro v hv
    have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
    seg_fp hv using simp only [b32,
      truncBits_ofNat (show laneOf l g < 2 ^ 32 by omega) (by decide)]
  obtain ⟨v, hWord, hv⟩ := hStep u (hu.mono (by trivial))
  have hRun := run_comp hr hWord
  have hQ : Holds u.regs ((9632, b32 0x8200490) :: (9633, b32 0x8210490) ::
      qDescriptorFacts l 1) := by
    simp only [qDescriptorFacts, packedQWord, List.finRange_succ, List.finRange_zero,
      List.map_cons, List.map_nil, Fin.val_zero, Fin.val_succ]
    exact ⟨hu.2.2.2.2.2.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hu.2.2.2.2.1, hu.2.2.2.2.2.1, hu.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.1,
      hu.2.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.2.2.1,
      hu.2.2.2.2.2.2.2.2.2.2.2.1, trivial⟩
  let regs := [9632, 9633, 9624, 9625, 9626, 9627, 9628, 9629, 9630, 9631]
  have hFacts : ∀ pair ∈ (9632, b32 0x8200490) :: (9633, b32 0x8210490) ::
      qDescriptorFacts l 1, pair.1 ∈ regs := by
    intro pair hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | rfl | hm
    · exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
    · obtain ⟨step, _, rfl⟩ := List.mem_map.mp hm
      change 9624 + step.val ∈ regs
      fin_cases step <;> decide
  have hReads : ∀ r ∈ regs, v.regs r = u.regs r := fun r hr =>
    Epilogue.schedulerLocalFrame (lo := 1934) (len := 1) (by
      set_option maxRecDepth 100000 in kernel_rfl) rfl hWord hu.1.ge (by rw [hu.1]) hr
  exact ⟨_, hRun, hv.mono
    ⟨hv.2.2.2.2.1, Epilogue.holdsSchedulerFrame hQ hReads hFacts⟩⟩

/-- The local query setup also keeps the MMA role register used by later trace cuts. -/
theorem startupQueryBankWithRole {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) :
    Seg kernel Assumptions.all l g 18 1917 [(2450, b32 (startupQLow l)), (1062, b32 12)] 1935
      ((1062, b32 12) :: (9632, b32 0x8200490) :: qDescriptorFacts l 1) := by
  intro t ht
  obtain ⟨u, hRun, hu⟩ := startupQRegistersCore hp g t (ht.mono ⟨ht.2.2.2.2.1, trivial⟩)
  have hRole : u.regs 1062 = t.regs 1062 :=
    schedulerLocalFrame (lo := 1917) (len := 18) (regs := [1062]) (by
      set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hRun ht.1.ge (by rw [ht.1]) (by decide)
  exact ⟨u, localRun (by decide) (by decide) ht.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hRun,
    hu.mono ⟨hRole.trans ht.2.2.2.2.2.1, hu.2.2.2.2.2.1, hu.2.2.2.2.2.2.2⟩⟩

end PTX.Kernels.TmlFa4Fwd.Mma
