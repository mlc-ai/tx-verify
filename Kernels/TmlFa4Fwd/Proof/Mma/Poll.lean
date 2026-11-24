-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Ref
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The barrier and the parity of the MMA warp's polls -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Progress
open PTX PTX.Proof PTX.Flow MBarrier
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (bl RefQ RefCounts LoopRegs acqAt ringAcq ringCount pq
  iw)

noncomputable section
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-! ### The barrier and parity of each poll -/

/-- The poll sites of the MMA warp. -/
def isPoll : Mma.Site → Bool
  | .wt _ | .mw _ _ => true
  | _ => false

/-- The barrier offset a poll site polls with `r` rounds done. -/
def pollO (r : Nat) : Mma.Site → Nat
  | .wt k => [0, 32, 8, 32 + 8 * ((2 * r + 1) % 3), 96, 32 + 8 * ((2 * r + 2) % 3), 104,
      32 + 8 * ((2 * r + 1) % 3), 96, 104].getD k.val 0
  | .mw b _ => if b.val % 2 = 0 then 112 else 120
  | _ => 0

/-- The poll's producer is the loader (Q stages and the K/V ring), else a softmax warp. -/
def fromLoader (o : Nat) : Bool := o < 96

theorem trunc_iw {n : Nat} (h : n < 2) : (truncBits 32 (iw n)).toNat % 2 = n := by
  interval_cases n <;> decide

theorem trunc_i0 : (truncBits 32 (Arith32.i32 0)).toNat % 2 = 0 := by decide

/-- The ring's count at slot `n mod 3` is `n / 3`. -/
theorem ringCount_mod (n : Nat) : ringCount n (n % 3) = n / 3 := by
  simp only [ringCount]
  omega

/-- The barrier a poll site's instruction addresses and the parity bit of its parity register,
as the shape table gives them. -/
def pollLoc (L : Launch) (g : Nat) (d : Mma.D) : Loc :=
  match d.site with
  | .wt k => smLoc L g (Mma.wtOp L d.v k).1 0
  | .mw b _ => smLoc L g (Mma.mwOp L b) 0
  | _ => bl L g 0

def pollPar (L : Launch) (d : Mma.D) : Nat :=
  match d.site with
  | .wt k => (truncBits 32 (Mma.wtOp L d.v k).2).toNat % 2
  | .mw _ _ => (truncBits 32 d.v.pp).toNat % 2
  | _ => 0

set_option maxHeartbeats 4000000 in
/-- **The barrier and parity of a poll**: a poll site addresses the barrier `pollO r s` with
the parity of the successful polls the counts record. -/
theorem par_eq (hp : Pre p L m) {d : Mma.D} {n : Mma.Cnt → Nat} {r : Nat} {w : Bool}
    (hQ : RefQ p L g d.site.ord d.v n r w) (hs : isPoll d.site = true) :
    pollLoc L g d = bl L g (pollO r d.site) ∧
      pollPar L d % 2 = n (.acquire (bl L g (pollO r d.site))) % 2 := by
  obtain ⟨site, v⟩ := d
  have hacq := hQ.acq
  cases site <;> simp only [isPoll, reduceCtorEq, Bool.false_eq_true] at hs
  case wt k =>
    simp only [pollLoc, pollPar, Nat.mod_mod]
    · fin_cases k
      all_goals simp only [Mma.wtOp, pollO, Mma.Site.ord, Fin.isValue, Fin.coe_ofNat_eq_mod,
        Nat.reduceMod, List.getD_cons_succ, List.getD_cons_zero, Fin.reduceFinMk, Fin.val_mk]
        at hacq hQ ⊢
      all_goals rw [hacq]
      · have hr := hQ.pre (by decide); subst hr
        exact ⟨Mma.smLoc_sbW hp 0 (by decide) (by decide), by rw [trunc_i0]; simp [acqAt, pq]⟩
      · have hr := hQ.pre (by decide); subst hr
        exact ⟨Mma.smLoc_addi hp 32 (by decide) (by decide),
          by rw [trunc_i0]; simp [acqAt, pq, ringAcq, ringCount]⟩
      · have hr := hQ.pre (by decide); subst hr
        exact ⟨Mma.smLoc_addi hp 8 (by decide) (by decide), by rw [trunc_i0]; simp [acqAt, pq]⟩
      · obtain ⟨hsl, hkv, -, -⟩ := hQ.regs (by decide)
        rw [hsl, hkv, Mma.smLoc_slot hp (Nat.mod_lt _ (by decide)),
          trunc_iw (Nat.mod_lt _ (by decide))]
        refine ⟨rfl, ?_⟩
        have h1 : ringAcq 20 r = 2 * r + 1 := by simp [ringAcq, pq]; omega
        simp only [acqAt, h1]
        have hs3 := Nat.mod_lt (2 * r + 1) (show 0 < 3 by decide)
        have hring := ringCount_mod (2 * r + 1)
        revert hring
        generalize (2 * r + 1) % 3 = s at hs3 ⊢
        intro hring
        interval_cases s <;> simp_all
      · obtain ⟨-, -, hpp, -⟩ := hQ.regs (by decide)
        rw [hpp, trunc_iw (Nat.mod_lt _ (by decide)),
          Mma.smLoc_addi hp 96 (by decide) (by decide)]
        exact ⟨rfl, by simp [acqAt, pq]⟩
      · have hR := hQ.regs (by decide)
        obtain ⟨hsl, hkv⟩ := Mma.slot1_eq hR
        rw [hsl, hkv, Mma.smLoc_slot hp (Nat.mod_lt _ (by decide)),
          trunc_iw (Nat.mod_lt _ (by decide))]
        refine ⟨rfl, ?_⟩
        have h1 : ringAcq 29 r = 2 * r + 2 := by simp [ringAcq, pq]; omega
        simp only [acqAt, h1]
        have hs3 := Nat.mod_lt (2 * r + 2) (show 0 < 3 by decide)
        have hring := ringCount_mod (2 * r + 2)
        revert hring
        generalize (2 * r + 2) % 3 = s at hs3 ⊢
        intro hring
        interval_cases s <;> simp_all
      · obtain ⟨-, -, hpp, -⟩ := hQ.regs (by decide)
        rw [hpp, trunc_iw (Nat.mod_lt _ (by decide)),
          Mma.smLoc_addi hp 104 (by decide) (by decide)]
        exact ⟨rfl, by simp [acqAt, pq]⟩
      · obtain ⟨hsl, hkv, -, -⟩ := hQ.regs (by decide)
        rw [hsl, hkv, Mma.smLoc_slot hp (Nat.mod_lt _ (by decide)),
          trunc_iw (Nat.mod_lt _ (by decide))]
        refine ⟨rfl, ?_⟩
        have h1 : ringAcq 64 r = 2 * r + 1 := by simp [ringAcq, pq]; omega
        simp only [acqAt, h1]
        have hs3 := Nat.mod_lt (2 * r + 1) (show 0 < 3 by decide)
        have hring := ringCount_mod (2 * r + 1)
        revert hring
        generalize (2 * r + 1) % 3 = s at hs3 ⊢
        intro hring
        interval_cases s <;> simp_all
      · obtain ⟨-, -, hpp, -⟩ := hQ.regs (by decide)
        rw [hpp, trunc_iw (Nat.mod_lt _ (by decide)),
          Mma.smLoc_addi hp 96 (by decide) (by decide)]
        exact ⟨rfl, by simp [acqAt, pq]⟩
      · obtain ⟨-, -, hpp, -⟩ := hQ.regs (by decide)
        rw [hpp, trunc_iw (Nat.mod_lt _ (by decide)),
          Mma.smLoc_addi hp 104 (by decide) (by decide)]
        exact ⟨rfl, by simp [acqAt, pq]⟩
  case mw b ld =>
    simp only [pollLoc, pollPar, Nat.mod_mod]
    · rw [Mma.mw_loc hp]
      fin_cases b <;> simp only [Mma.Site.ord, Fin.isValue, Fin.reduceFinMk, Fin.val_mk,
        List.getD_cons_succ, List.getD_cons_zero] at hacq hQ ⊢ <;>
        obtain ⟨-, -, hpp, -⟩ := hQ.regs (by decide) <;>
        rw [hpp, trunc_iw (Nat.mod_lt _ (by decide)), hacq] <;>
        exact ⟨by simp [pollO], by simp [pollO, acqAt, pq]⟩

theorem pollO_al (r : Nat) (s : Mma.Site) : pollO r s % 8 = 0 := by
  cases s <;> simp only [pollO]
  case wt k => fin_cases k <;> simp
  case mw b ld => split <;> rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Progress
