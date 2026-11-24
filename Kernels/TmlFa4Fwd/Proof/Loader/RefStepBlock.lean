-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.RefBase
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's reference invariant across the page and pointer rounds and the slot waits

The page rounds' global reads and local stores and the pointer rounds' local loads and stores are
counted by no class and keep the site's class and the ring words; the end of a page loop enters
the slot wait, the end of a pointer loop the packet. A successful slot wait polls the empty
barrier of its packet's slot `j mod 3` (`slot_loc`, from the ring words of the warm and steady
rounds, `SlotIs`), the packet after the lane's commits. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (addi add32 shl i32)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (sbW)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat}

set_option maxHeartbeats 4000000 in
theorem step_pgLd (per : Per) (it : Fin 2) : StepRef p L g w (.pgLd per it) := by
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev] at hev
  rcases hev with ⟨_, hk⟩ | ⟨f, hk⟩
  swap; exact absurd hk (hub f)
  have hq := cls_rd (L := L) (g := g) hk
  cases per <;> sc_split
  all_goals sc_close

set_option hygiene false in
/-- Close a local store's step: the store's location, the counts and the ring conjuncts. -/
macro "store_close" : tactic => `(tactic| (
  have hcls := cls_store hk (lacc_loc hp (by decide) _)
  first
    | exact ⟨⟨k, A, by ring_tac, counts_store hC hk (lacc_loc hp (by decide) _) rfl (by lst_tac)⟩,
        by move_tac⟩
    | (get_k2
       exact ⟨⟨k, A, by ring_tac, counts_store hC hk (lacc_loc hp (by decide) _) rfl
         (by lst_tac)⟩, by move_tac⟩)))

set_option maxHeartbeats 4000000 in
theorem step_pgSt (hp : Pre p L m) (per : Per) (it : Fin 2) : StepRef p L g w (.pgSt per it) := by
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev] at hev
  rcases hev with ⟨_, _, hk⟩ | ⟨f, hk⟩
  swap; exact absurd hk (hub f)
  have hx : rv p L g w ⟨.pgSt per it, v, kk⟩ (pgStA per) =
      add64 (BitVec.ofNat 64 (L.localBase + 96)) (wideU4 (i32 ((it.val : Nat) : Int))) := by
    cases per <;> rfl
  rw [hx, wideU4_fin, add64_ofNat, Nat.add_assoc] at hk
  cases per <;> fin_cases it <;> sc_split
  all_goals store_close

set_option maxHeartbeats 4000000 in
theorem step_rwSt (hp : Pre p L m) (per : Per) (it : Fin 2) : StepRef p L g w (.rwSt per it) := by
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev] at hev
  rcases hev with ⟨_, _, hk⟩ | ⟨f, hk⟩
  swap; exact absurd hk (hub f)
  have hx : rv p L g w ⟨.rwSt per it, v, kk⟩ (rwStA per) =
      add64 (BitVec.ofNat 64 (L.localBase + 64)) (wideU4 (i32 ((it.val : Nat) : Int))) := by
    cases per <;> rfl
  rw [hx, wideU4_fin, add64_ofNat, Nat.add_assoc] at hk
  cases per <;> fin_cases it <;> sc_split
  all_goals store_close

set_option maxHeartbeats 4000000 in
theorem step_ptP (per : Per) (b : Bool) (it : Fin 2) : StepRef p L g w (.ptP per b it) := by
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev] at hev
  obtain ⟨_, hk⟩ := hev
  have hq := cls_rd (L := L) (g := g) hk
  cases per <;> cases b <;> sc_split
  all_goals sc_close

set_option maxHeartbeats 4000000 in
theorem step_ptR (per : Per) (b : Bool) (it : Fin 2) : StepRef p L g w (.ptR per b it) := by
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev] at hev
  obtain ⟨_, hk⟩ := hev
  have hq := cls_rd (L := L) (g := g) hk
  cases per <;> cases b <;> sc_split
  all_goals sc_close

set_option maxHeartbeats 4000000 in
theorem step_ptS (hp : Pre p L m) (per : Per) (b : Bool) (it : Fin 2) :
    StepRef p L g w (.ptS per b it) := by
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev] at hev
  rcases hev with ⟨_, _, hk⟩ | ⟨f, hk⟩
  swap; exact absurd hk (hub f)
  have hx : rv p L g w ⟨.ptS per b it, v, kk⟩ (ptRegs (pk per b)).u =
      add64 (BitVec.ofNat 64 (L.localBase + ptOff per b))
        (shl64 (m64 ((it.val : Nat) : Int)) 3) := by
    cases per <;> cases b <;> rfl
  rw [hx, shl64_fin3, add64_ofNat, Nat.add_assoc] at hk
  cases per <;> cases b <;> fin_cases it <;> simp only [ptOff] at hk <;> sc_split
  all_goals store_close

/-- The empty barrier of a slot wait: the slot of its packet. -/
theorem slot_loc (hp : Pre p L m) {per : Per} {b : Bool} {v : V} {kk : Fin 2} {k A : Nat}
    (hJ : RefRing p L g w ⟨.slot per b, v, kk⟩ k A) :
    smLoc L g (rv p L g w ⟨.slot per b, v, kk⟩ (waitRegs (.slot per b)).1) 0 =
      bl L g (56 + 8 * (pkOf per b k % 3)) := by
  cases per <;> cases b
  · exact (smLoc_addi hp 56 (by norm_num)).trans rfl
  · exact (smLoc_addi hp 64 (by norm_num)).trans rfl
  · exact (congrArg (smLoc L g · 0) (by
      show addi (add32 (sbW L) (shl v.slot 3)) 56 = _
      rw [hJ.2.1.1.1])).trans (smLoc_empty hp k)
  · exact (congrArg (smLoc L g · 0) (by
      show addi (add32 (sbW L) (shl (nslot v.slot) 3)) 56 = _
      rw [(slotIs_next hJ.2.1.1).1])).trans (smLoc_empty hp (k + 1))
  · exact (congrArg (smLoc L g · 0) (by
      show addi (add32 (sbW L) (shl v.slot 3)) 56 = _
      rw [hJ.2.1.1])).trans (smLoc_empty hp k)
  · exact (congrArg (smLoc L g · 0) (by
      show addi (add32 (sbW L) (shl (nslot v.slot) 3)) 56 = _
      rw [(slotIs_next hJ.2.1).1])).trans (smLoc_empty hp (k + 1))

set_option maxHeartbeats 4000000 in
theorem step_slot (hp : Pre p L m) (per : Per) (b : Bool) : StepRef p L g w (.slot per b) := by
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev] at hev
  obtain ⟨ok, hk⟩ := hev
  rw [slot_loc hp hJ] at hk
  simp only [succ, hk] at hn
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
    subst hn
    have hcls := cls_none (cls_waitF (L := L) (g := g) hk)
    exact ⟨⟨k, A, hJ, counts_quiet hC (cls_waitF hk) rfl⟩, by move_tac⟩
  · simp only [↓reduceIte, Option.some.injEq, D.mk'] at hn
    subst hn
    have hcls := cls_wait (L := L) (g := g) hk
    have hc0 : n .commit = pkOf per b k := by simpa [arrAt, inPkt] using hC.commit
    refine ⟨⟨k, A, refRing_congr hJ (by cases per <;> cases b <;> rfl) rfl rfl rfl rfl rfl rfl,
      counts_other hC (by simp [cls, hk]) (fun _ => by simp [cls, hk]) rfl⟩, ?_⟩
    move_with (by simp only [tag, Tag.cnt, hc0, reduceCtorEq, ↓reduceIte, Nat.add_zero])

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
