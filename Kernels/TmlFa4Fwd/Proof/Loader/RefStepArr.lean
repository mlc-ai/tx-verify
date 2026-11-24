-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.RefBase
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's reference invariant across the packets' copy arrivals

A packet's copy arrival publishes its packet `j` on the full barrier of slot `j mod 3`
(`counts_publish`). It ends a half block: after the first block's K packet the lane waits for the
V slot (warp 15) or loads the first Q and Bias groups (warp 14, which keeps the first Bias parity
1 until the fourth group clears it); after the first block's V packet the warm rounds start at
packet 2 (with both Bias parities those of the first block), or, with fewer than two blocks, the
steady rounds, the last Bias group or the second pass; after a warm or steady round's K packet the
lane waits for the V slot (warp 14 loads the round's Bias groups first); after its V packet the
next round starts two packets on, or the rounds end (`k` and `A` both the next packet). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 addi add32 shl)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (sbW)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat}

/-- The full barrier of a packet's copy arrival: the slot of its packet. -/
theorem arrive_loc (hp : Pre p L m) {per : Per} {b : Bool} {v : V} {kk : Fin 2} {k A : Nat}
    (hJ : RefRing p L g w ⟨.arrive per b, v, kk⟩ k A) :
    smLoc L g (rv p L g w ⟨.arrive per b, v, kk⟩ (arrRegs (pk per b)).1) (arrRegs (pk per b)).2 =
      bl L g (32 + 8 * (pkOf per b k % 3)) := by
  cases per <;> cases b
  · exact (smLoc_sb hp 32 (by norm_num)).trans rfl
  · exact (smLoc_sb hp 40 (by norm_num)).trans rfl
  · exact (congrArg (smLoc L g · 32) (by
      show add32 (sbW L) (shl v.slot 3) = _
      rw [hJ.2.1.1.1])).trans (smLoc_full hp k)
  · exact (congrArg (smLoc L g · 32) (by
      show add32 (sbW L) (shl (nslot v.slot) 3) = _
      rw [(slotIs_next hJ.2.1.1).1])).trans (smLoc_full hp (k + 1))
  · exact (congrArg (smLoc L g · 32) (by
      show add32 (sbW L) (shl v.slot 3) = _
      rw [hJ.2.1.1])).trans (smLoc_full hp k)
  · exact (congrArg (smLoc L g · 32) (by
      show add32 (sbW L) (shl (nslot v.slot) 3) = _
      rw [(slotIs_next hJ.2.1).1])).trans (smLoc_full hp (k + 1))

theorem r32_i32_0 : (r32 (i32 0)).toNat = 0 := by decide

/-- The first Bias parity at the start of the warm rounds. -/
theorem bq_warm0 {x : BitVec 64} (h : x = BitVec.ofNat 64 (if w = 14 then 0 else 1)) :
    x = BitVec.ofNat 64 (if w = 14 then ((r32 (i32 0)).toNat + 0) % 2 else 1) := by
  rw [h, r32_i32_0]

/-- The Bias parity after a warm round. -/
theorem bq_round {x rnd : BitVec 64}
    (h : x = BitVec.ofNat 64 (if w = 14 then ((r32 rnd).toNat + 1) % 2 else 1)) :
    x = BitVec.ofNat 64 (if w = 14 then ((r32 (addi rnd 1)).toNat + 0) % 2 else 1) := by
  rw [h]; simp only [Nat.add_zero, rnd_succ_mod2]

set_option hygiene false in
/-- Unfold the successor of an arrival and split it into its branches. -/
macro "arr_split" : tactic => `(tactic| (
  simp only [succ, afterArrive, afterPrime, afterWarm, afterTail, warmEnd, steadyEnd, pgEnter,
    passStart, D.mk', D.ite, D.iteS, Option.some.injEq] at hn
  subst hn
  try split_ifs))

set_option hygiene false in
/-- Close the ring conjuncts of an arrival's successor. -/
macro "arr_ring" : tactic => `(tactic| (
  try simp only [refRing_iff, RingWords, SlotIs, ringCls,
    Site.isTma, Epilogue.Scan.late, Fin.isValue,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, imp_false, not_false_eq_true,
    true_and, and_true, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceLT, decide_true,
    decide_false, reduceCtorEq, false_implies, forall_const, Nat.le_add_left, le_refl,
    Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Bool.or_eq_false_iff,
    Bool.not_eq_false', Bool.and_eq_true] at hJ ⊢
  all_goals first
    | exact hJ
    | decide
    | (have h14 := w15_of hw ‹not14 w = true›; simp only [h14, ↓reduceIte]; decide)
    | exact ⟨w14_of hw (by simpa using ‹¬not14 w = true›), by decide⟩
    | exact ⟨w14_of hw (by simpa using ‹¬not14 w = true›), hJ⟩
    | (have hc := ‹¬(not14 w || _) = true›
       simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hc
       first
         | exact ⟨w14_of hw hc.1, by decide⟩
         | exact ⟨w14_of hw hc.1, slotIs_roundV (v := v) (j := k) hJ.1.1⟩
         | exact ⟨w14_of hw hc.1, slotIs_roundV (v := v) (j := k) hJ.1⟩
         | exact ⟨w14_of hw hc.1, by decide, by omega⟩
         | exact ⟨w14_of hw hc.1, slotIs_roundV (v := v) (j := k) hJ.1.1, by omega⟩
         | exact ⟨w14_of hw hc.1, slotIs_roundV (v := v) (j := k) hJ.1, by omega⟩)
    | exact ⟨by decide, bq_warm0 hJ⟩
    | exact ⟨by decide, rfl, bq_warm0 hJ⟩
    | (have h14 := w15_of hw ‹not14 w = true›
       exact ⟨hJ.1, hJ.2.1, by rw [hJ.2.2]; simp only [h14, ↓reduceIte]⟩)
    | exact ⟨slotIs_roundV (v := v) (j := k) hJ.1.1, hJ.2.1, bq_round hJ.2.2⟩
    | exact slotIs_roundV (v := v) (j := k) hJ.1.1
    | exact slotIs_roundV (v := v) (j := k) hJ.1
    | exact ⟨⟨slotIs_roundV (v := v) (j := k) hJ.1.1, by omega⟩, hJ.2.1, bq_round hJ.2.2⟩
    | exact ⟨slotIs_roundV (v := v) (j := k) hJ.1.1, by omega⟩
    | exact ⟨slotIs_roundV (v := v) (j := k) hJ.1, by omega⟩
    | exact ⟨by decide, by omega⟩
    | exact ⟨⟨by decide, by omega⟩, bq_warm0 hJ⟩))

set_option hygiene false in
/-- The tag of an arrival's edge: the full barrier of the last committed packet's slot. -/
macro "arr_tag" : tactic => `(tactic|
  (simp only [tag, Tag.cnt, hc0, reduceCtorEq, ↓reduceIte, Nat.add_sub_cancel]; done))

set_option hygiene false in
/-- The step of the arrival of one packet kind. -/
macro "arr_step " per:term:max b:term:max : tactic => `(tactic| (
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev] at hev
  rw [arrive_loc hp hJ] at hev
  have hcls := cls_async (L := L) (g := g) hev
  have hc0 : n .commit = pkOf $per $b k + 1 := by simpa [arrAt, inPkt] using hC.commit
  have hP : ∀ {d'' : D} {k' A' : Nat}, arrAt d''.site k' A' = pkOf $per $b k + 1 →
      inPkt d''.site = (0, 0) →
      (∀ o ∈ lstOffs, lstAt d''.site k' A' o = lstAt (Site.arrive $per $b) k A o) →
      RefCounts L g w (d'', Code.bump (cls L g) n e) k' A' :=
    fun h1 h3 h6 => counts_other hC (by simp [cls, hev]) (fun _ => by simp [cls, hev])
      (by rw [h1, h3]; simp [arrAt, inPkt]) h6
  get_k2
  arr_split
  all_goals first
    | exact ⟨⟨k, A, by arr_ring, hP rfl rfl (by lst_tac)⟩, by move_with (by arr_tag)⟩
    | exact ⟨⟨k + 2, k + 2, by arr_ring, hP rfl rfl (by lst_tac)⟩, by move_with (by arr_tag)⟩
    | exact ⟨⟨2, 2, by arr_ring, hP rfl rfl (by lst_tac)⟩, by move_with (by arr_tag)⟩))

set_option maxHeartbeats 8000000 in
private theorem step_arrive_prime_false (hp : Pre p L m) (hw : w = 14 ∨ w = 15) :
    StepRef p L g w (.arrive .prime false) := by
  arr_step .prime false

set_option maxHeartbeats 8000000 in
private theorem step_arrive_prime_true (hp : Pre p L m) (hw : w = 14 ∨ w = 15) :
    StepRef p L g w (.arrive .prime true) := by
  arr_step .prime true

set_option maxHeartbeats 8000000 in
private theorem step_arrive_warm_false (hp : Pre p L m) (hw : w = 14 ∨ w = 15) :
    StepRef p L g w (.arrive .warm false) := by
  arr_step .warm false

set_option maxHeartbeats 8000000 in
private theorem step_arrive_warm_true (hp : Pre p L m) (hw : w = 14 ∨ w = 15) :
    StepRef p L g w (.arrive .warm true) := by
  arr_step .warm true

set_option maxHeartbeats 8000000 in
private theorem step_arrive_steady_false (hp : Pre p L m) (_hw : w = 14 ∨ w = 15) :
    StepRef p L g w (.arrive .steady false) := by
  arr_step .steady false

set_option maxHeartbeats 8000000 in
private theorem step_arrive_steady_true (hp : Pre p L m) (_hw : w = 14 ∨ w = 15) :
    StepRef p L g w (.arrive .steady true) := by
  arr_step .steady true

theorem step_arrive (hp : Pre p L m) (hw : w = 14 ∨ w = 15) (per : Per) (b : Bool) :
    StepRef p L g w (.arrive per b) :=
  match per, b with
  | .prime, false => step_arrive_prime_false hp hw
  | .prime, true => step_arrive_prime_true hp hw
  | .warm, false => step_arrive_warm_false hp hw
  | .warm, true => step_arrive_warm_true hp hw
  | .steady, false => step_arrive_steady_false hp hw
  | .steady, true => step_arrive_steady_true hp hw
end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
