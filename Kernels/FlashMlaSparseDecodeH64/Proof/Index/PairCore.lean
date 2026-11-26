-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Blocks
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexAddr
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LaunchReads

@[expose] public section

/-! # The index warp's pair loads: the cores of their address

The state-level cores of `Index/Export/Addr.lean`, which need no `Follow`: from the index state at
a pair load (its site, element, the counters' invariant `Ctr` with the block `i`, the lane's length
words) the load's access is word `64 b + 2 lane + el` of the lane's row, below the array's length
(`main_pair_core`, `extra_pair_core`). The machine's no-stop obligation uses them before `Follow`
exists. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch}  {m : Mem0}

private theorem site_pc {s : IxSite} (h : s.pc = 2403 ∨ s.pc = 2429 ∨ s.pc = 2501 ∨ s.pc = 2517) :
    s = .pre ∨ s = .pf ∨ s = .xpre ∨ s = .xpf := by
  cases s <;> simp [IxSite.pc] at h ⊢

theorem pair_nc_at {pc el : Nat} {x : BitVec 64} {a : Acc} {bs : List (Option Byte)}
    (h : Index.NcAt x el ⟨pc, .nc a bs⟩) :
    a.loc = (⟨.global, 0, (truncBits 64 x + BitVec.ofInt 64 0).toNat⟩ : Loc).at (4 * el) ∧
      a.size = 4 := by
  rcases h with ⟨a', bs', hk, hloc, hsz⟩ | ⟨f, hk⟩
  · dsimp only at hk
    obtain ⟨rfl, rfl⟩ := Kind.nc.inj hk
    exact ⟨hloc, hsz⟩
  · cases hk

/-- **The main index array's pair load** (pcs `2403`, `2429`) at a state with block `i` reads word
`64 b + 2 lane + el` of the lane's row, below `topk`. -/
theorem main_pair_core (hp : Pre P L m) {g pc i : Nat} {a : Acc} {bs : List (Option Byte)}
    {d : Index.D} (hpcd : d.site.pc = pc) (hEv : Index.EvK P L g d ⟨pc, .nc a bs⟩)
    (hel : d.el < 2) (hct : Index.Ctr P L g d.site d.c i)
    (h0 : d.c.l0 = lenWA P L (g / L.block)) (hpc : pc = 2403 ∨ pc = 2429) :
    ∃ b : Nat, d.el < 2 ∧ (pc = 2403 → b = 0) ∧ (pc = 2429 → b = i + 1) ∧
      64 * b + 2 * (tidOf L g % 32) + d.el < P.topk ∧ a.size = 4 ∧
      a.loc = ⟨.global, 0, P.indicesBase + 4 * ((ctaidY L g * P.s_q + ctaidX L g) * P.topk +
        (64 * b + 2 * (tidOf L g % 32) + d.el))⟩ := by
  obtain ⟨site, el, ac, c⟩ := d
  have hl := Nat.mod_lt (tidOf L g) (show 0 < 32 by norm_num)
  obtain ⟨hwa, -, -, hle, -⟩ := len_words hp (g / L.block)
  have hk := hp.topkDiv64
  have hkp := hp.topkPos
  have hM : Index.nMain c.l0 = numOrigBlocks (P.topkLen (rowOf L (g / L.block))) := by
    rw [h0, hwa]; exact Index.nMain_val (by have := hp.topkAdd63Lt; omega)
  have hM64 := Index.blocks_main_le hle hk hkp
  have hrow : (ctaidY L g * P.s_q + ctaidX L g) * P.topk =
      ctaidX L g * P.topk + ctaidY L g * (P.s_q * P.topk) := by ring
  have hS := site_pc (s := site) (by rw [hpcd]; omega)
  dsimp only at hpcd hel hct hM
  dsimp only
  rcases hS with rfl | rfl | rfl | rfl
  · obtain ⟨hloc, hsz⟩ := pair_nc_at hEv
    have hv := ixA_main_lt hp g (j := 2 * (tidOf L g % 32)) (by omega)
    rw [ixAddr0_val hp g, ixA_addr (by omega)] at hloc
    refine ⟨0, hel, fun _ => rfl, fun h => by simp [IxSite.pc] at hpcd; omega, by omega, hsz,
      ?_⟩
    rw [hloc]
    simp only [Loc.at, Loc.mk.injEq, true_and]
    omega
  · obtain ⟨hloc, hsz⟩ := pair_nc_at hEv
    obtain ⟨⟨-, -, -, -, hap⟩, hnm⟩ := hct
    have hmn : Index.nMin c.l0 c.l1 ≤ Index.nMain c.l0 := Nat.min_le_left _ _
    have hv := ixA_main_lt hp g (j := 64 * (i + 1) + 2 * (tidOf L g % 32)) (by omega)
    rw [hap, ixApB_val hp g, ixAddr0_val hp g, BitVec.ofNat_add_ofNat] at hloc
    rw [ixA_addr (by omega)] at hloc
    refine ⟨i + 1, hel, fun h => by simp [IxSite.pc] at hpcd; omega, fun _ => by omega,
      by omega, hsz, ?_⟩
    rw [hloc]
    simp only [Loc.at, Loc.mk.injEq, true_and]
    omega
  all_goals simp [IxSite.pc] at hpcd; omega

/-- **The extra index array's pair load** (pcs `2501`, `2517`) at a state with block `i` reads word
`64 b + 2 lane + el` of the lane's row, below `extra_topk`. -/
theorem extra_pair_core (hp : Pre P L m) {g pc i : Nat} {a : Acc} {bs : List (Option Byte)}
    {d : Index.D} (hpcd : d.site.pc = pc) (hEv : Index.EvK P L g d ⟨pc, .nc a bs⟩)
    (hel : d.el < 2) (hct : Index.Ctr P L g d.site d.c i)
    (h0 : d.c.l0 = lenWA P L (g / L.block)) (h1 : d.c.l1 = lenWB P L (g / L.block))
    (hpc : pc = 2501 ∨ pc = 2517) :
    ∃ b : Nat, d.el < 2 ∧ (pc = 2501 → b = 0) ∧
      (pc = 2517 → b + numOrigBlocks (P.topkLen (ctaidY L g)) = i + 1) ∧
      64 * b + 2 * (tidOf L g % 32) + d.el < P.extra_topk ∧ a.size = 4 ∧
      a.loc = ⟨.global, 0, P.extraIndicesBase + 4 * ((ctaidY L g * P.s_q + ctaidX L g) *
        P.extra_topk + (64 * b + 2 * (tidOf L g % 32) + d.el))⟩ := by
  obtain ⟨site, el, ac, c⟩ := d
  have hl := Nat.mod_lt (tidOf L g) (show 0 < 32 by norm_num)
  obtain ⟨hwa, hwb, hr, hle, hle2⟩ := len_words hp (g / L.block)
  rw [rowOf_cta] at hwa hwb hr hle hle2
  have hk := hp.extraDiv64
  have hM : Index.nMain c.l0 = numOrigBlocks (P.topkLen (ctaidY L g)) := by
    rw [h0, hwa]; exact Index.nMain_val (by have := hp.topkAdd63Lt; omega)
  have hR : roundsOf c.l0 c.l1 =
      totalBlocks (P.topkLen (ctaidY L g)) (P.extraTopkLen (ctaidY L g)) := by
    rw [h0, h1, hwa, hwb]; exact rounds_val hr
  have hB64 := Index.blocks_extra_le (a := P.topkLen (ctaidY L g)) hle2 hk
  have hrlt := Index.rounds_lt c.l0 c.l1
  have hrow : (ctaidY L g * P.s_q + ctaidX L g) * P.extra_topk =
      ctaidX L g * P.extra_topk + ctaidY L g * (P.s_q * P.extra_topk) := by ring
  have hS := site_pc (s := site) (by rw [hpcd]; omega)
  dsimp only at hpcd hel hct hM hR
  dsimp only
  rcases hS with rfl | rfl | rfl | rfl
  · simp [IxSite.pc] at hpcd; omega
  · simp [IxSite.pc] at hpcd; omega
  · obtain ⟨hMR, hi, -⟩ := hct
    have hx : 0 < P.extra_topk := by
      simp only [totalBlocks, numOrigBlocks, origPadded, ceilToMultiple, topkBlock] at hR hM
      omega
    obtain ⟨hloc, hsz⟩ := pair_nc_at hEv
    have hv := ixA_extra_lt hp g hx (j := 2 * (tidOf L g % 32)) (by omega)
    rw [ixAddr1_val hp g hx, ixA_addr (by omega)] at hloc
    refine ⟨0, hel, fun _ => rfl, fun h => by simp [IxSite.pc] at hpcd; omega, by omega, hsz,
      ?_⟩
    rw [hloc]
    simp only [Loc.at, Loc.mk.injEq, true_and]
    omega
  · obtain ⟨⟨hMR, h1', h2', -, -, hxa⟩, hnm⟩ := hct
    have hx : 0 < P.extra_topk := by
      simp only [totalBlocks, numOrigBlocks, origPadded, ceilToMultiple, topkBlock] at hR hM
      omega
    obtain ⟨hloc, hsz⟩ := pair_nc_at hEv
    have hxe : ((ixXa0 L g).toNat + 64 * (i - Index.nMain c.l0)) % 2 ^ 32 =
        tidOf L g % 32 * 2 + 64 * (i + 1 - Index.nMain c.l0) := by
      rw [ixXa0_val hp g, toNat_W (by omega)]
      omega
    have hv := ixA_extra_lt hp g hx
      (j := 64 * (i + 1 - Index.nMain c.l0) + 2 * (tidOf L g % 32)) (by omega)
    rw [hxa, hxe, ixXad_val hp g hx (by omega)] at hloc
    rw [ixA_addr (by omega)] at hloc
    refine ⟨i + 1 - Index.nMain c.l0, hel, fun h => by simp [IxSite.pc] at hpcd; omega,
      fun _ => by omega, by omega, hsz, ?_⟩
    rw [hloc]
    simp only [Loc.at, Loc.mk.injEq, true_and]
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
