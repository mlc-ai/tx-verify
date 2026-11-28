-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.Base
public import Lemmas.Flow.Step.GenericShared
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Stage
public import Lemmas.Flow.PointerReg
public import Lemmas.Flow.Step.SiteShape
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamSteps
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part001
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part002

@[expose] public section

/-! # The staging pointers (pcs 104–145)

The eight generic staging pointers are formed exactly: the row words (pcs 104–109, 111–112,
`seg_ctl`), the `cvta.shared` of the base word (pc 110, `exec_cvtaShared_or`), the pointer
additions (pc 113 by a register, pcs 114, 118, …, 142 by an immediate, `exec_add_sharedPtr*`),
and per chunk the SW128 swizzle's shift, mask and xor read through `Assumptions.sharedBits`
(evaluated, normalized by `stage_bits`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Flow PTX.Proof PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

/-- The control facts at `pc` of the fields of `d`. -/
noncomputable abbrev vF (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) (pc : Nat) (d : D) :
    List (Nat × Value) :=
  factsFrom (ctlLive pc) (valueOf P L g w d)

set_option hygiene false in
/-- One pointer addition of the immediate `k` at `pc` (code lemma `c`) from register `r`. -/
macro "st_add " c:term:max r:term:max k:term:max : tactic => `(tactic| (
  refine SegU.set_live (live := ctlLive) (val := valueOf P L g w d) (d := $r) $c rfl
    (by decide +kernel)
    (by decide +kernel) fun t ht => .inl ?_
  obtain ⟨hpc, -, -, -, hR⟩ := ht
  refine exec_add_sharedPtr (k := $k) (regs_of_factsFrom hR (by decide +kernel))
    (.inr rfl) (by omega) (by decide) (by decide)
    (fun a ha => asms_localRule_int (by rw [hpc]; decide) (by rw [hpc]; decide)
      (by rw [hpc]; decide) (Assumptions.peerPackRule_of_none (by rw [hpc]; rfl)) a ha)))

/-- The swizzle's tag keeps every register but the xor's destination. -/
theorem st_keep_ne {t u : TState} {i : IntInstr} {r d : Nat} (hi : i.dsts = [some d])
    (hr : r ≠ d) : (Assumptions.keepSwizzleTag t i u).regs r = u.regs r := by
  unfold Assumptions.keepSwizzleTag
  split <;> try rfl
  rename_i dst _ _ _ _ hd _
  obtain rfl : dst = d := by rw [hi] at hd; cases hd; rfl
  split <;> try rfl
  simp only [setReg, Function.update_apply, hr, ↓reduceIte]

set_option hygiene false in
/-- Chunk `k`'s shift, mask and xor into the staging register `r` (three instructions read
through `Assumptions.sharedBits`; `h` bounds the chunk's byte). -/
macro "st_swz " h:term:max r:term:max k:term:max : tactic => `(tactic| (
  try dsimp only [code, facts, Site.pc]
  seg_ctl rulesFrame, KernelHavoc.hooks_ok using
    (try (rw [st_keep_ne rfl (by omega)]; simp only [Function.update_apply]
          split_ifs <;> first | rfl | (exfalso; omega)))
    (try (nf_simp
          rw [show valueOf P L g w d $r = shP L g (stW L g $k) from rfl, st_norm $h]
          dsimp only [shP, stW, stM]
          rw [stage_xor $h]))))

/-- **The staging stretch** (pcs 104–145): from the facts after `setmaxnreg` to the facts at
pc 146, the eight staging pointers among them. -/
theorem stageSeg (hp : Pre P L m) (d : D) :
    SegU kernel Assumptions.all L g 104 (vF P L g w 103 d) 146 (vF P L g w 146 d) := by
  have hs := sharedBase_lt hp
  have hq := stQuad_lt L g
  refine SegU.comp (b := 110) (G := vF P L g w 110 d) (by w0_seg) ?_
  refine SegU.comp (SegU.set_live (live := ctlLive) (val := valueOf P L g w d) (d := 3111)
    Flow.code_110 rfl
    (by decide +kernel) (by decide +kernel) fun t ht => ?_) ?_
  · obtain ⟨hpc, -, -, -, hR⟩ := ht
    have hr := regs_of_factsFrom hR (r := 3110) (by decide +kernel)
    change t.regs 3110 = some (.bits 64 (zext (sbw L))) at hr
    rw [zext_sbw hp] at hr
    exact exec_cvtaShared_or hr (by omega) (localRule_none_addr t _)
      noSegments.segFreePc
  refine SegU.comp (b := 113) (G := vF P L g w 113 d) (by w0_seg) ?_
  refine SegU.comp (SegU.set_live (live := ctlLive) (val := valueOf P L g w d) (d := 3113)
    Flow.code_113 rfl
    (by decide +kernel) (by decide +kernel) fun t ht => .inl ?_) ?_
  · obtain ⟨hpc, -, -, -, hR⟩ := ht
    have hq' := regs_of_factsFrom hR (r := 3112) (by decide +kernel)
    change t.regs 3112 = some (.bits 64 (stQuad L g)) at hq'
    have hq'' : t.regs 3112 = some (.bits 64 (BitVec.ofNat 64 (stQuad L g).toNat)) := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hq'
    exact exec_add_sharedPtr_reg (regs_of_factsFrom hR (r := 3111) (by decide +kernel))
      hq'' (.inr rfl) (by omega) (by omega) rfl (by decide)
      (fun a ha => asms_localRule_int (by rw [hpc]; decide) (by rw [hpc]; decide)
        (by rw [hpc]; decide) (Assumptions.peerPackRule_of_none (by rw [hpc]; rfl)) a ha)
      noSegments.segFreePc
  refine SegU.comp (b := 115) (G := vF P L g w 115 d) (by st_add Flow.code_114 3114 65536) ?_
  refine SegU.comp (b := 118) (G := vF P L g w 118 d)
    (by st_swz (stP_lt hp g (k := 0) (by decide)) 2992 0) ?_
  refine SegU.comp (b := 119) (G := vF P L g w 119 d)
    (by st_add Flow.code_118 3117 65552) ?_
  refine SegU.comp (b := 122) (G := vF P L g w 122 d)
    (by st_swz (stP_lt hp g (k := 1) (by decide)) 2993 1) ?_
  refine SegU.comp (b := 123) (G := vF P L g w 123 d)
    (by st_add Flow.code_122 3120 65568) ?_
  refine SegU.comp (b := 126) (G := vF P L g w 126 d)
    (by st_swz (stP_lt hp g (k := 2) (by decide)) 2994 2) ?_
  refine SegU.comp (b := 127) (G := vF P L g w 127 d)
    (by st_add Flow.code_126 3123 65584) ?_
  refine SegU.comp (b := 130) (G := vF P L g w 130 d)
    (by st_swz (stP_lt hp g (k := 3) (by decide)) 2995 3) ?_
  refine SegU.comp (b := 131) (G := vF P L g w 131 d)
    (by st_add Flow.code_130 3126 65600) ?_
  refine SegU.comp (b := 134) (G := vF P L g w 134 d)
    (by st_swz (stP_lt hp g (k := 4) (by decide)) 2996 4) ?_
  refine SegU.comp (b := 135) (G := vF P L g w 135 d)
    (by st_add Flow.code_134 3129 65616) ?_
  refine SegU.comp (b := 138) (G := vF P L g w 138 d)
    (by st_swz (stP_lt hp g (k := 5) (by decide)) 2997 5) ?_
  refine SegU.comp (b := 139) (G := vF P L g w 139 d)
    (by st_add Flow.code_138 3132 65632) ?_
  refine SegU.comp (b := 142) (G := vF P L g w 142 d)
    (by st_swz (stP_lt hp g (k := 6) (by decide)) 2998 6) ?_
  refine SegU.comp (b := 143) (G := vF P L g w 143 d)
    (by st_add Flow.code_142 3135 65648) ?_
  st_swz (stP_lt hp g (k := 7) (by decide)) 2999 7

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
