-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.OperandWords
import Kernels.InklingRelDecode.Gen.StepMma01
import Kernels.InklingRelDecode.Gen.StepMma02
import Lemmas.Flow.TcMmaTs
import Lemmas.Flow.Step.TcFields
import Lemmas.Cluster.Unit

@[expose] public section

/-! # The MMA issues are not undefined behaviour

At an MMA site whose registers hold the table's values the template is an MMA event: the
descriptors decode (low words below `2^15`, the V operand's bit 26 set), the instruction
descriptors decode as `kind::f16` with `cta_group::1`, the four lane masks are zero, and the
A address of a PV MMA stays in its column field. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

variable {Q : Params} {L : Launch} {m : Mem0} {g i : Nat} {regs : Nat → Value} {w v : Value}
  {t : TState} {ins : Instr}

/-- Every `cta_group::1` descriptor has an operand specification in a launch of one-CTA
clusters. -/
theorem operands_one_cta (hp : Pre Q L m) (hg : g < L.threads) (dsc : TcMma.Descriptor)
    (da db : TcShared.Descriptor) (hd : dsc.group = .one) :
    ∃ spec, TcMma.makeOperands L (g / L.block) dsc da db = some spec := by
  have hs : ∀ k, (L.clusterPlaces k).shape = ⟨1, 1, 1⟩ := by
    intro k
    rw [hp.clusterPlaces, hp.clusterNctaid]
    rfl
  have cta : g / L.block < L.grid := by
    rw [Launch.threads, hp.block] at hg
    rw [hp.block]
    omega
  have hc : g / L.block < L.nclusters := hp.nclusters ▸ cta
  refine ⟨⟨dsc, da, db, g / L.block, g / L.block, none, {}⟩, ?_⟩
  rw [TcMma.makeOperands, hd, Launch.ctaGroup_one, Launch.rankOfCta_unit hs hc,
    Launch.peerCta_unit hs hc cta]
  rfl

private theorem desc_decode {lo : Nat} (hlo : lo < 2 ^ 31) (h15 : lo / 2 ^ 15 % 2 = 0) :
    ∃ d, TcShared.decode (lo + descHi * 2 ^ 32) = some d :=
  sharedDecode_some (sw := .b128) hlo h15 (by decide) (by decide) (by decide) rfl

private theorem vdesc_decode {lo : Nat} (hlo : lo < 2 ^ 15) :
    ∃ d, TcShared.decode (lo + 2 ^ 26 + descHi * 2 ^ 32) = some d :=
  desc_decode (lo := lo + 2 ^ 26) (by omega) (by omega)

private theorem reg {d : D} {r} (ht : (code L g regs w).AtD d t) (key : r ∈ Flow.live d.site.pc) :
    t.regs r = some (valueOf L regs w d r) := by
  obtain ⟨_, _, _, _, holds⟩ := ht
  exact holds_mem holds (mem_factsFrom key)

private theorem zero_masks (t : TState) : masks.mapM (readBits L g t 32) = .ok [0, 0, 0, 0] := rfl

/-- **A QK issue is not undefined behaviour.** -/
theorem qk_issue_ok (hp : Pre Q L m) (hg : g < L.threads) (hw : w = b32 0) (j : Fin 8)
    (ht : (code L g regs w).AtD ⟨.qk j, i, v⟩ t) (hc : kernel.code[qkPc j]? = some ins)
    (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  obtain rfl := Option.some.inj (hc.symm.trans (qcode j))
  have keys : ∀ j : Fin 8, let live := Flow.live (qkPc j)
      2027 + 2 * j.val ∈ live ∧ 2028 + 2 * j.val ∈ live ∧ 548 ∈ live ∧ 547 ∈ live ∧
        (if j.val = 0 then 9 else 11) ∈ live := by decide +kernel
  obtain ⟨kA, kB, kI, kD, kE⟩ := keys j
  have hA := reg ht kA
  have hB := reg ht kB
  have hI := reg ht kI
  have hD := reg ht kD
  have hE := reg ht kE
  have vals (j : Fin 8) : let val := valueOf L regs w ⟨.qk j, i, v⟩
      val (2027 + 2 * j.val) = desc (qWord L j) ∧ val (2028 + 2 * j.val) = desc (kWord L i j) := by
    fin_cases j <;> exact ⟨rfl, rfl⟩
  rw [(vals j).1] at hA
  rw [(vals j).2] at hB
  change t.regs 548 = some (b32 qkIdesc) at hI
  have enable : valueOf L regs w ⟨.qk j, i, v⟩ (if j.val = 0 then 9 else 11)
      = .pred (decide (j.val ≠ 0)) := by
    fin_cases j <;> rfl
  rw [enable] at hE
  have small : 128 * (i % 2) < 2 ^ 32 := by have := Nat.mod_lt i (show 0 < 2 by decide); omega
  have hq : valueOf L regs w ⟨.qk j, i, v⟩ 547 = b32 ((0 + 128 * (i % 2)) % 2 ^ 32) := by
    subst hw; rfl
  rw [hq, Nat.zero_add, Nat.mod_eq_of_lt small] at hD
  have room := hp.sharedRange
  change L.sharedBase + 213340 ≤ 2 ^ 18 at room
  have jq := j.isLt
  have qa : qWord L j < 2 ^ 15 := by dsimp [qWord, qLo]; omega
  have kb : kWord L i j < 2 ^ 15 := by dsimp [kWord, kLo]; omega
  obtain ⟨da, hda⟩ := desc_decode (lo := qWord L j) (by omega) (by omega)
  obtain ⟨db, hdb⟩ := desc_decode (lo := kWord L i j) (by omega) (by omega)
  obtain ⟨dsc, hdi, hgr⟩ : ∃ dsc, TcMma.decode .one false .f16 qkIdesc = some dsc ∧
      dsc.group = .one := ⟨_, rfl, rfl⟩
  obtain ⟨spec, hs⟩ := operands_one_cta hp hg dsc da db hgr
  have ht' := tc_mma_en (L := L) (mask := masks) (ms := [0, 0, 0, 0]) hg hD small
    hA (by unfold descHi; omega) hB (by unfold descHi; omega) hI (by decide) (zero_masks t)
    rfl (mmaEnable_of hE) hda hdb hdi hs
  simp only [eventTmpl]
  unfold qOp
  rw [ht']
  nofun

/-- **A PV issue is not undefined behaviour.** -/
theorem pv_issue_ok (hp : Pre Q L m) (hg : g < L.threads) (hw : w = b32 0) (j : Fin 8)
    (ht : (code L g regs w).AtD ⟨.pv j, i, v⟩ t) (hc : kernel.code[pvPc j]? = some ins)
    (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  obtain rfl := Option.some.inj (hc.symm.trans (vcode j))
  have keys : ∀ j : Fin 8, let live := Flow.live (pvPc j)
      564 ∈ live ∧ 565 ∈ live ∧ 566 ∈ live ∧ 2044 + j.val ∈ live ∧
        (if j.val = 0 then 14 else 16) ∈ live := by decide +kernel
  obtain ⟨kD, kA, kI, kB, kE⟩ := keys j
  have hD := reg ht kD
  have hA := reg ht kA
  have hI := reg ht kI
  have hB := reg ht kB
  have hE := reg ht kE
  have val (j : Fin 8) : valueOf L regs w ⟨.pv j, i, v⟩ (2044 + j.val) = vdesc (vWord L i j) := by
    fin_cases j <;> rfl
  rw [val] at hB
  change t.regs 566 = some (b32 pvIdesc) at hI
  have enable : valueOf L regs w ⟨.pv j, i, v⟩ (if j.val = 0 then 14 else 16)
      = .pred (if j.val = 0 then decide (i ≠ 1) else true) := by
    fin_cases j <;> rfl
  rw [enable] at hE
  have small : 128 * ((i - 1) % 2) < 2 ^ 32 := by
    have := Nat.mod_lt (i - 1) (show 0 < 2 by decide); omega
  have hq : valueOf L regs w ⟨.pv j, i, v⟩ 564 = b32 ((0 + 256) % 2 ^ 32) := by subst hw; rfl
  have ha : valueOf L regs w ⟨.pv j, i, v⟩ 565 = b32 ((0 + 128 * ((i - 1) % 2)) % 2 ^ 32) := by
    subst hw; rfl
  rw [hq] at hD
  rw [ha, Nat.zero_add, Nat.mod_eq_of_lt small] at hA
  have room := hp.sharedRange
  change L.sharedBase + 213340 ≤ 2 ^ 18 at room
  have jq := j.isLt
  have vb : vWord L i j < 2 ^ 15 := by dsimp [vWord, vLo]; omega
  obtain ⟨db, hdb⟩ := vdesc_decode vb
  obtain ⟨dsc, hdi, hgr, htr⟩ : ∃ dsc, TcMma.decode .one false .f16 pvIdesc = some dsc ∧
      dsc.group = .one ∧ dsc.transposeA = false := ⟨_, rfl, rfl, rfl⟩
  obtain ⟨spec, hs⟩ := operands_one_cta hp hg dsc db db hgr
  have off : tmemOffset (128 * ((i - 1) % 2)) (8 * j.val : Nat) =
      .ok (128 * ((i - 1) % 2) + 8 * j.val) := by
    apply tmemOffset_of
    have := Nat.mod_lt (i - 1) (show 0 < 2 by decide)
    omega
  have ht' := tc_mmaTs (L := L) (mask := masks) (ms := [0, 0, 0, 0]) hg
    (hD.trans (by rfl)) (by decide) hA small (by exact_mod_cast off) hB
    (by unfold descHi; omega) hI (by decide) (zero_masks t) rfl (mmaEnable_of hE) hdb hdi htr hs
  simp only [eventTmpl]
  unfold vOp
  rw [ht']
  nofun

end PTX.Kernels.InklingRelDecode.Proof.Mma
