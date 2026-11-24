-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Open
import Kernels.TmlFa4Fwd.Proof.Softmax.Align
import Lemmas.Flow.TmplOkMore
import Lemmas.Flow.UbFreeStore
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A data store without undefined behaviour

A Tensor Memory store (`tcSt_site`) and a shared store of one word (`st_site`) fire no undefined
behaviour at a state whose facts name the address and four-byte source values. The addresses: the
P stores' columns are in the warp's lane chunk (`tmP_ok`), the statistics address is 4-aligned
(`statA_al`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ori)
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 add32 andi shl)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A `tcgen05.st` of sixteen four-byte registers at a supported address. -/
theorem tcSt_site (hp : Pre p L m) (d : D) {pc ta : Nat} (rs : List Nat) {ss : List Opnd}
    {a : BitVec 64} (hpc : d.site.pc = pc)
    (hc : kernel.code[pc]? = some { guard := none, op := .tcSt ta ss .s32x32b })
    (hss : ss = rs.map Opnd.reg)
    (hl : (ta :: rs).all ((liveD (livePc d)).contains ·) = true)
    (hta : valueOfD p L g d ta = .bits 32 a) (ha : a.toNat < 2 ^ 32)
    (hs : tcDataAddressOk L g .s32x32b a.toNat = true) (hn : rs.length = 16)
    (hb : ∀ r ∈ rs, (valueOfD p L g d r).bytes = 4) : (codeD p L g).ShapeAt NoUb d := by
  subst hpc hss
  intro t ins e o hat hi hc' hf f hk
  have h := fires_ub hf hk
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  have hF := hat.2.2.2.2
  simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hl
  have hr : t.regs ta = some (b32 a.toNat) := by
    rw [regs_of_factsFrom hF hl.1, hta]
    simp only [b32, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨vals, hm, h4⟩ := mapM_regs_ok (L := L) (g := g) (t := t) (ss := rs.map Opnd.reg)
    fun i hi => by
      have hi' : i < rs.length := by simpa using hi
      have hx : rs[i] ∈ rs := List.getElem_mem hi'
      exact ⟨rs[i], _, by simp [List.getElem?_eq_getElem hi'],
        regs_of_factsFrom hF (hl.2 _ hx), hb _ hx⟩
  exact tcSt_ok (by rw [hp.block]) (by simp [TcShape.countOk, TcShape.regs, hn]) hr ha hs hm h4 f h

/-- A shared store of one four-byte register at a 4-aligned address. -/
theorem st_site (d : D) {pc base r : Nat} {off : Int} {a : BitVec 64}
    (hpc : d.site.pc = pc)
    (hc : kernel.code[pc]? =
      some { guard := none,
             op := .mem { kind := .store, space := some (.shared .cta), sem := .weak,
                          elem := .int .b 32, addr := ⟨.reg base 32, off⟩, srcs := [.reg r] } })
    (hmid : ∀ k acc, ¬ d.site.midOk k acc)
    (hl : [base, r].all ((liveD (livePc d)).contains ·) = true)
    (hbase : valueOfD p L g d base = .bits 32 a) (ha : (a.toNat + (off % 4).toNat) % 4 = 0)
    (hb : (valueOfD p L g d r).bytes = 4) : (codeD p L g).ShapeAt NoUb d := by
  subst hpc
  intro t ins e o hat hi hc' hf f hk
  have h := fires_ub hf hk
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  have hF := hat.2.2.2.2
  have hk0 : d.k = 0 := by
    rcases hi with hi | hi
    · exact hi.1
    · exact absurd hi (hmid _ _)
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, List.contains_iff_mem] at hl
  exact st_word_ok ((regs_of_factsFrom hF hl.1).trans (congrArg some hbase)) ha
    (hat.2.1.trans (congrArg Fin.val hk0)) (regs_of_factsFrom hF hl.2.1) hb f h

set_option maxRecDepth 100000 in
private theorem tmP_lanes : ∀ i < 512, laneOkI i (ori (tmI i) 80).toNat = true ∧
    laneOkI i (ori (tmI i) 112).toNat = true := by
  decide +kernel

/-- The P stores' Tensor Memory addresses are in the warp's lane chunk. -/
theorem tmP_ok (hp : Pre p L m) :
    tcDataAddressOk L g .s32x32b (ori (tmS L g) 64).toNat = true ∧
    tcDataAddressOk L g .s32x32b (ori (tmS L g) 80).toNat = true ∧
    tcDataAddressOk L g .s32x32b (ori (tmS L g) 96).toNat = true ∧
    tcDataAddressOk L g .s32x32b (ori (tmS L g) 112).toNat = true := by
  have hi : g % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have h := tm_ok (g := g) hp
  have h' := tmP_lanes _ hi
  refine ⟨h.2.2.1, ?_, h.2.2.2, ?_⟩
  · simp only [tcAddr_eq, tmS, stg, warpW, tidW_eq hp]; exact h'.1
  · simp only [tcAddr_eq, tmS, stg, warpW, tidW_eq hp]; exact h'.2

/-- The stage's statistics address is 4-aligned. -/
theorem statA_al (hp : Pre p L m) : (statA L g).toNat % 4 = 0 := by
  have hs := hp.shared.1
  simp only [statA, add32, shl, r32, i32, Mma.sbW]
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by decide))]
  rw [show (truncBits 32 (BitVec.ofInt 64 2)).toNat = 2 by decide]
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
