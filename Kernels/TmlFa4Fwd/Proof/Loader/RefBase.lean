-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Ref
public import Kernels.TmlFa4Fwd.Proof.Loader.RefRows
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Facts for the loader's reference invariant across a step

The ring words of packet `j` (`slot_next`, `par_next`: the next slot and parity, as the code's
`nslot` and `npar` compute them), the barrier locations of the ring's polls and arrivals and of
the TMA groups (`smLoc` of the shared base plus a multiple of 8), and how a step moves the counts
(`counts_frame`: an event counted by no class the invariant names; `counts_acquire`: a successful
poll of a ring slot's empty barrier; `counts_publish`: a packet's copy arrival). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 addi add32 shl xor32 sel scmpi)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (sbW)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat}

/-! ### Ring words -/

theorem mod3_cases (j : Nat) : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega

theorem nslot_mod (j : Nat) :
    nslot (BitVec.ofNat 64 (j % 3)) = BitVec.ofNat 64 ((j + 1) % 3) := by
  rcases mod3_cases j with h | h | h <;>
    rw [h, show (j + 1) % 3 = (j % 3 + 1) % 3 by omega, h] <;> decide

theorem npar_mod (j : Nat) :
    npar (BitVec.ofNat 64 (j % 3)) (BitVec.ofNat 64 ((j / 3 + 1) % 2)) =
      BitVec.ofNat 64 (((j + 1) / 3 + 1) % 2) := by
  have h2 : (j / 3 + 1) % 2 = 0 ∨ (j / 3 + 1) % 2 = 1 := by omega
  rcases mod3_cases j with h | h | h
  · rw [h, show ((j + 1) / 3 + 1) % 2 = (j / 3 + 1) % 2 by omega]
    rcases h2 with h2 | h2 <;> rw [h2] <;> decide
  · rw [h, show ((j + 1) / 3 + 1) % 2 = (j / 3 + 1) % 2 by omega]
    rcases h2 with h2 | h2 <;> rw [h2] <;> decide
  · rw [h, show ((j + 1) / 3 + 1) % 2 = ((j / 3 + 1) % 2 + 1) % 2 by omega]
    rcases h2 with h2 | h2 <;> rw [h2] <;> decide

/-- The slot and parity of the next packet. -/
theorem slotIs_next {v : V} {j : Nat} (h : SlotIs v j) :
    nslot v.slot = BitVec.ofNat 64 ((j + 1) % 3) ∧
      npar v.slot v.par = BitVec.ofNat 64 (((j + 1) / 3 + 1) % 2) := by
  obtain ⟨hs, hp⟩ := h
  rw [hs, hp]
  exact ⟨nslot_mod j, npar_mod j⟩

/-- The ring words after a round: two packets on. -/
theorem slotIs_roundV {v : V} {j : Nat} (h : SlotIs v j) : SlotIs (roundV v) (j + 2) := by
  obtain ⟨h1, h2⟩ := slotIs_next h
  show nslot (nslot v.slot) = _ ∧ npar (nslot v.slot) (npar v.slot v.par) = _
  rw [h1, h2, nslot_mod (j + 1), npar_mod (j + 1)]
  exact ⟨rfl, rfl⟩

/-- The round counter's parity after a round. -/
theorem rnd_succ_mod2 (x : BitVec 64) :
    (r32 (addi x 1)).toNat % 2 = ((r32 x).toNat + 1) % 2 := by
  simp only [addi, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]
  omega

/-! ### Barrier locations -/

theorem sb_lt (hp : Pre p L m) : L.sharedBase < 2 ^ 18 := by
  have := hp.shared.2.1; omega

theorem smLoc_addi (hp : Pre p L m) (o : Nat) (ho : o < 2 ^ 20) :
    smLoc L g (addi (sbW L) o) 0 = bl L g o := by
  have := sb_lt hp
  simp only [smLoc, bl, addi, r32, i32, sbW, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt, Loc.mk.injEq, true_and]
  omega

theorem smLoc_sb (hp : Pre p L m) (o : Nat) (ho : o < 2 ^ 20) :
    smLoc L g (sbW L) o = bl L g o := by
  have := sb_lt hp
  simp only [smLoc, bl, sbW, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt,
    Loc.mk.injEq, true_and]
  omega

theorem slotBase_toNat (hp : Pre p L m) (j : Nat) :
    (add32 (sbW L) (shl (BitVec.ofNat 64 (j % 3)) 3)).toNat = L.sharedBase + 8 * (j % 3) := by
  have := sb_lt hp
  rcases mod3_cases j with h | h | h <;> rw [h] <;>
    simp [add32, shl, r32, i32, sbW, truncBits] <;> omega

/-- The empty barrier of the slot of packet `j`. -/
theorem smLoc_empty (hp : Pre p L m) (j : Nat) :
    smLoc L g (addi (add32 (sbW L) (shl (BitVec.ofNat 64 (j % 3)) 3)) 56) 0 =
      bl L g (56 + 8 * (j % 3)) := by
  have := sb_lt hp
  have h := slotBase_toNat (L := L) hp j
  generalize add32 (sbW L) (shl (BitVec.ofNat 64 (j % 3)) 3) = x at h ⊢
  simp only [smLoc, bl, addi, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt, Loc.mk.injEq, true_and, h]
  omega

/-- The full barrier of the slot of packet `j`. -/
theorem smLoc_full (hp : Pre p L m) (j : Nat) :
    smLoc L g (add32 (sbW L) (shl (BitVec.ofNat 64 (j % 3)) 3)) 32 = bl L g (32 + 8 * (j % 3)) := by
  have := sb_lt hp
  have h := slotBase_toNat (L := L) hp j
  generalize add32 (sbW L) (shl (BitVec.ofNat 64 (j % 3)) 3) = x at h ⊢
  simp only [smLoc, bl, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt, Loc.mk.injEq, true_and, h]
  omega

theorem bl_inj {o o' : Nat} : bl L g o = bl L g o' ↔ o = o' := by
  simp [bl]

/-! ### Event classes -/

theorem cls_rd {e : Event} {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .rd a bs)
    (c : Cnt) : cls L g c e = false := by
  cases c <;> simp [cls, hk]
theorem cls_shfl {e : Event} {md a b c' r ok} (hk : e.kind = .shfl md a b c' r ok) (c : Cnt) :
    cls L g c e = false := by
  cases c <;> simp [cls, hk]
theorem cls_vote {e : Event} {mk a b} (hk : e.kind = .vote mk a b) (c : Cnt) :
    cls L g c e = false := by
  cases c <;> simp [cls, hk]
theorem cls_setmax {e : Event} {a b c'} (hk : e.kind = .setMaxReg a b c') (c : Cnt) :
    cls L g c e = false := by
  cases c <;> simp [cls, hk]
theorem cls_waitF {e : Event} {l par a sc} (hk : e.kind = .wait l par false a sc) (c : Cnt) :
    cls L g c e = false := by
  cases c <;> simp [cls, hk]
theorem cls_lost {e : Event} {mk inst ld} (hk : e.kind = .elect mk inst ld)
    (hl : ¬ laneOf L g = ld) (c : Cnt) : cls L g c e = false := by
  cases c <;> simp [cls, hk]
  intro _ h; exact hl h.symm

/-! ### Counts across a step -/

/-- The local-store counts of a successor: the same position in the same block (`rfl`), or the
start of the next block after the last packet of the current one. -/
macro "lst_tac" : tactic => `(tactic| first
  | (intro _ _; rfl)
  | (simp only [lstOffs, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
       and_true]
     refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
     simp (config := { decide := true }) [lstAt, lstPos, lstCum, lstSeq, lstEnd, List.take,
       List.count_cons] <;>
     omega))

/-- The `2 ≤ k` of a warm or steady state. -/
theorem k2_of {s : Site} {v : V} {kk : Fin 2} {k A : Nat}
    (hJ : RefRing p L g w ⟨s, v, kk⟩ k A) (hc : ringCls s = .later ∨ ∃ f, ringCls s = .warm f) :
    2 ≤ k := by
  obtain ⟨-, h⟩ := hJ
  rcases hc with hc | ⟨f, hc⟩ <;> simp only [hc] at h
  · exact h.2
  · exact h.1.2

set_option hygiene false in
/-- The `2 ≤ k` of the state `hJ` is about, when it is a warm or steady state. -/
macro "get_k2" : tactic => `(tactic| first
  | have hk2 : 2 ≤ k := k2_of hJ (.inl rfl)
  | have hk2 : 2 ≤ k := k2_of hJ (.inr ⟨false, rfl⟩)
  | have hk2 : 2 ≤ k := k2_of hJ (.inr ⟨true, rfl⟩)
  | skip)

/-- **The count fields after a step** whose commits and local stores follow the closed forms. -/
theorem counts_of {d d' : D} {n : Cnt → Nat} {e : Event} {k A k' A' : Nat}
    (hC : RefCounts L g w (d, n) k A)
    (hc : arrAt d'.site k' A' + (inPkt d'.site).2 =
      arrAt d.site k A + (inPkt d.site).2 + if cls L g .commit e then 1 else 0)
    (hl : ∀ o ∈ lstOffs, lstAt d'.site k' A' o =
      lstAt d.site k A o + if cls L g (.lst o) e then 1 else 0) :
    RefCounts L g w (d', Code.bump (cls L g) n e) k' A' :=
  ⟨by have := hC.commit; simp only at this; simp only [Code.bump]; rw [this, hc], fun o ho => by
    have := hC.lst o ho; simp only at this; simp only [Code.bump]; rw [this, hl o ho]⟩

/-- An event that is neither a commit nor a local store, at successor positions with the same
closed forms. -/
theorem counts_other {d d' : D} {n : Cnt → Nat} {e : Event} {k A k' A' : Nat}
    (hC : RefCounts L g w (d, n) k A) (hc : cls L g .commit e = false)
    (hs : ∀ o, cls L g (.lst o) e = false)
    (h2 : arrAt d'.site k' A' + (inPkt d'.site).2 = arrAt d.site k A + (inPkt d.site).2)
    (h6 : ∀ o ∈ lstOffs, lstAt d'.site k' A' o = lstAt d.site k A o := by lst_tac) :
    RefCounts L g w (d', Code.bump (cls L g) n e) k' A' :=
  counts_of hC (by rw [hc, h2]; rfl) (fun o ho => by rw [hs o, h6 o ho]; rfl)

/-- An event counted by no class. -/
theorem counts_quiet {d d' : D} {n : Cnt → Nat} {e : Event} {k A k' A' : Nat}
    (hC : RefCounts L g w (d, n) k A) (hq : ∀ c, cls L g c e = false)
    (h2 : arrAt d'.site k' A' + (inPkt d'.site).2 = arrAt d.site k A + (inPkt d.site).2)
    (h6 : ∀ o ∈ lstOffs, lstAt d'.site k' A' o = lstAt d.site k A o := by lst_tac) :
    RefCounts L g w (d', Code.bump (cls L g) n e) k' A' :=
  counts_other hC (hq _) (fun _ => hq _) h2 h6

/-- **A local store at offset `o0`** adds one to the stores at `o0`. -/
theorem counts_store {d d' : D} {n : Cnt → Nat} {e : Event} {k A k' A' o0 : Nat} {a : Acc}
    {bs : List Byte} (hC : RefCounts L g w (d, n) k A) (hk : e.kind = .wr a bs)
    (hloc : a.loc = ⟨.local, g, L.localBase + o0⟩)
    (h2 : arrAt d'.site k' A' + (inPkt d'.site).2 = arrAt d.site k A + (inPkt d.site).2)
    (hg : ∀ o ∈ lstOffs, lstAt d'.site k' A' o = lstAt d.site k A o + if o0 = o then 1 else 0) :
    RefCounts L g w (d', Code.bump (cls L g) n e) k' A' :=
  counts_of hC (by rw [h2]; simp [cls, hk]) (fun o ho => by rw [hg o ho]; simp [cls, hk, hloc])

/-- The location of a local access at `L.localBase + o`. -/
theorem lacc_loc (hp : Pre p L m) {o : Nat} (ho : o < 128) (sz : Nat) :
    (lacc g (BitVec.ofNat 64 (L.localBase + o)) 0 sz 0).loc = ⟨.local, g, L.localBase + o⟩ := by
  have := hp.localMemory.2.1
  simp only [lacc, Loc.at, wrapAddr, truncBits, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ofInt, Nat.mul_zero, Nat.add_zero, Loc.mk.injEq, true_and]
  omega

/-! ### Steps -/

/-- The obligation of the steps from the states at site `s`: under the reference invariant, a
step on an event of the state's shape that is not undefined behaviour leads to a state satisfying
it (`w` is 14 or 15). -/
def StepRef (p : Params) (L : Launch) (g w : Nat) (s : Site) : Prop :=
  ∀ (v : V) (kk : Fin 2) (n : Cnt → Nat) (e : Event) (d' : D) (k A : Nat),
    RefRing p L g w ⟨s, v, kk⟩ k A → RefCounts L g w (⟨s, v, kk⟩, n) k A →
    Ev p L g w ⟨s, v, kk⟩ e → (∀ f, e.kind ≠ .ub f) →
    succ p L g w ⟨s, v, kk⟩ e = some (some d') → Post p L g w (⟨s, v, kk⟩, n) e d'


/-- The warp from the code's test of warp 14. -/
theorem w14_of {w : Nat} (hw : w = 14 ∨ w = 15) (h : not14 w = false) : w = 14 := by
  rcases hw with rfl | rfl
  · rfl
  · exact absurd h (by decide)
theorem w15_of {w : Nat} (hw : w = 14 ∨ w = 15) (h : not14 w = true) : w ≠ 14 := by
  rcases hw with rfl | rfl
  · exact absurd h (by decide)
  · decide

set_option hygiene false in
/-- The ring conjuncts at a successor: unfold the classes and close by the old conjuncts. -/
macro "ring_tac" : tactic => `(tactic| (
  try simp only [refRing_iff, RingWords, SlotIs, ringCls,
    Site.isTma, Epilogue.Scan.late, D.mk', Fin.isValue,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, imp_false, not_false_eq_true,
    true_and, and_true, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceLT, decide_true,
    decide_false, reduceCtorEq, false_implies, forall_const, Nat.le_add_left, le_refl,
    Fin.coe_ofNat_eq_mod,
    Nat.reduceMod] at hJ ⊢
  all_goals first
    | trivial
    | exact hJ
    | (constructor <;> decide)
    | decide))

set_option hygiene false in
/-- Unfold a step at a site with literal fields and split it into its branches, each with its
successor substituted; a conditional successor (`D.ite`, `D.iteS`) is split by `ref_ite`,
without deciding its condition. -/
macro "sc_split" : tactic => `(tactic| (
  simp only [succ, hk, word32, scAt, D.mk', afterTotal, loopHead, scanExit,
    passStart, afterTiles, pgEnter, pkStart, drain0, Fin.isValue, reduceCtorEq, ↓reduceIte,
    Fin.val_zero, Fin.val_one, Nat.one_ne_zero, Bool.false_eq_true] at hn
  repeat' (first
    | (cases hn; done)
    | (simp only [Option.some.injEq, Option.map_some, Option.map_none, reduceCtorEq] at hn
       subst hn)
    | split at hn)
  all_goals repeat' (first | apply post_ite | apply post_iteS)))

set_option hygiene false in
/-- Close a branch of a step counted by no class (`hq`), whose successor keeps `k` and `A` or
enters the drain from the first pass (`A = 0`). -/
macro "sc_close" : tactic => `(tactic| (
  have hcls := cls_none hq
  first
    | exact ⟨⟨k, A, by ring_tac, counts_quiet hC hq rfl⟩, by move_tac⟩
    | exact ⟨⟨k, 0, by ring_tac, counts_quiet hC hq rfl⟩, by move_tac⟩))

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
