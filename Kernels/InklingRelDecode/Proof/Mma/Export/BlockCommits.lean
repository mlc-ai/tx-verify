-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.RankOrder
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.History
import Kernels.InklingRelDecode.Proof.Mma.Machine
import Kernels.InklingRelDecode.Proof.Common.BaseWord
import Kernels.InklingRelDecode.Proof.Mma.OperandWords
public import Kernels.InklingRelDecode.Proof.Lib.MmaPcs

/-! # The block of a QK or PV issue

A QK issue of block `b` follows `b + 1` ready polls and `b - 1` PV polls and writes the score
buffer `b % 2`; a PV issue of block `b - 1` follows `b` PV polls and writes the accumulator. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Flow PTX.Frame

private def qkLits : List Nat := [2483,2486,2488,2490,2492,2494,2496,2498]

private def pvLits : List Nat := [2530,2533,2535,2537,2539,2541,2543,2545]

private theorem qk_site (s : Site) (hit : s.pc ∈ qkLits) : ∃ j, s = .qk j := by
  cases s <;> first | exact ⟨_,rfl⟩ | exact absurd hit (by decide +kernel) |
    (rename_i j; fin_cases j <;> exact absurd hit (by decide +kernel))

private theorem pv_site (s : Site) (hit : s.pc ∈ pvLits) : ∃ j, s = .pv j := by
  cases s <;> first | exact ⟨_,rfl⟩ | exact absurd hit (by decide +kernel) |
    (rename_i j; fin_cases j <;> exact absurd hit (by decide +kernel))

/-- **A QK issue**: of block `b`, writing the score buffer of its parity. -/
public theorem qk_block {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    (qk : ∃ j : Fin 8, pc = Lib.qkIssue j) :
    ∃ b, dst = 128*(b%2) ∧ pollRound 2462 ((X.tr g).take k) = b+1 ∧
      pollRound 2510 ((X.tr g).take k) = b-1 ∧ g%L.block/32 = 7 ∧
      ∀ j : Fin 8, pc = Lib.qkIssue j → acc = decide (j.val ≠ 0) ∧
        s.a = ⟨((L.sharedBase + 196608) / 16 + (2 * (j.val % 4) + 512 * (j.val / 4))) * 16, 0,
          1024, 0, false, false, .b128⟩ ∧
        s.b = ⟨((L.sharedBase + 32768 * (b % 3)) / 16 + (2 * (j.val % 4) + 1024 * (j.val / 4))) *
          16, 0, 1024, 0, false, false, .b128⟩ := by
  have lits : pc ∈ qkLits := by
    obtain ⟨j,rfl⟩ := qk
    fin_cases j <;> decide
  have range : ∀ p ∈ qkLits, 2422 < p ∧ p < 2557 := by decide +kernel
  obtain ⟨w,x,r,d,n,hs,pcs⟩ := mma_state hp hX hf he (fun _ => nofun)
    (range _ lits).1 (range _ lits).2
  have tab := reached_table hf (lt_of_get hX he) (noUbBefore_of_get hX he) hs
  obtain ⟨warp,ref,hq,hp',-⟩ := tab.2
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have zero : w = PTX.Proof.b32 0 :=
    recorded_zero hp hX base hk (noUbBefore_of_get hX he) hs
  obtain ⟨t,ins,o,ht,_,hc,ff⟩ := fired_siteU (fun g hg => thread_sound hp hg) hX he hs
    (fun _ => nofun)
  change pc = d.site.pc at pcs
  subst pcs
  obtain ⟨st,i,v⟩ := d
  obtain ⟨jj,rfl⟩ := qk_site st lits
  obtain ⟨dstEq,-,hacc⟩ := q_dst zero jj ht hc ff
  have qr := (fcount hs (.poll 2462)).symm.trans hq
  have pr := (fcount hs (.poll 2510)).symm.trans hp'
  change pollRound 2462 _ = i+1 at qr
  change pollRound 2510 _ = i-1 at pr
  refine ⟨i,dstEq,qr,pr,warp,fun j hj => ?_⟩
  have same : ∀ j jj : Fin 8, Lib.qkIssue j = qkPc jj → j = jj := by decide
  obtain rfl := same j jj hj.symm
  obtain ⟨-, -, ha, hb, -⟩ := q_operands hp j ht hc ff
  exact ⟨hacc, ha, hb⟩

private theorem pv_block' {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    (pv : ∃ j : Fin 8, pc = Lib.pvIssue j) :
    ∃ b, dst = 256 ∧ pollRound 2510 ((X.tr g).take k) = b ∧ 1 ≤ b ∧
      pollRound 2462 ((X.tr g).take k) ≤ b+1 ∧
      (∃ j : Fin 8, s.aTmem = some (128*((b-1)%2)+8*j.val)) ∧ g%L.block/32 = 7 ∧
      (∀ j : Fin 8, pc = Lib.pvIssue j → acc = decide (j.val ≠ 0 ∨ 2 ≤ b)) ∧
      (∀ j : Fin 8, pc = Lib.pvIssue j → s.aTmem = some (128 * ((b - 1) % 2) + 8 * j.val)) ∧
      ∀ j : Fin 8, pc = Lib.pvIssue j →
        s.b = ⟨((L.sharedBase + 98304 + 32768 * ((b - 1) % 3)) / 16 + 128 * j.val) * 16, 16384,
          1024, 0, false, false, .b128⟩ := by
  have lits : pc ∈ pvLits := by
    obtain ⟨j,rfl⟩ := pv
    fin_cases j <;> decide
  have range : ∀ p ∈ pvLits, 2422 < p ∧ p < 2557 := by decide +kernel
  obtain ⟨w,x,r,d,n,hs,pcs⟩ := mma_state hp hX hf he (fun _ => nofun)
    (range _ lits).1 (range _ lits).2
  have tab := reached_table hf (lt_of_get hX he) (noUbBefore_of_get hX he) hs
  obtain ⟨warp,ref,hq,hp',-⟩ := tab.2
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have zero : w = PTX.Proof.b32 0 :=
    recorded_zero hp hX base hk (noUbBefore_of_get hX he) hs
  obtain ⟨t,ins,o,ht,_,hc,ff⟩ := fired_siteU (fun g hg => thread_sound hp hg) hX he hs
    (fun _ => nofun)
  change pc = d.site.pc at pcs
  subst pcs
  obtain ⟨st,i,v⟩ := d
  obtain ⟨jj,rfl⟩ := pv_site st lits
  obtain ⟨dstEq,aEq,-,hacc⟩ := v_dst zero jj ht hc ff
  have loop : Mma.Inv ⟨.pv jj,i,v⟩ := tab.1.1
  have pr := (fcount hs (.poll 2510)).symm.trans hp'
  change pollRound 2510 _ = i at pr
  have qr := (fcount hs (.poll 2462)).symm.trans hq
  change pollRound 2462 _ = min (i+1) (low v) at qr
  change 0 < i ∧ _ at loop
  obtain ⟨-, -, -, hb, -⟩ := v_operands hp jj ht hc ff
  have same : ∀ j jj : Fin 8, Lib.pvIssue j = pvPc jj → j = jj := by decide
  refine ⟨i,dstEq,pr,loop.1,by omega,⟨jj,aEq⟩,warp,fun j hj => ?_,fun j hj => ?_,
    fun j hj => ?_⟩
  · obtain rfl := same j jj hj.symm
    have := loop.1
    by_cases h0 : j.val = 0
    · simp only [h0, ↓reduceIte] at hacc
      rw [hacc]
      simp only [h0, ne_eq, not_true_eq_false, false_or]
      by_cases h1 : i = 1 <;> simp [h1]; omega
    · simp only [h0, ↓reduceIte] at hacc
      simp [hacc, h0]
  · obtain rfl := same j jj hj.symm
    simpa using aEq
  · obtain rfl := same j jj hj.symm
    exact hb


/-- **A PV issue**: of block `b - 1`, writing the accumulator. -/
public theorem pv_block {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    (pv : ∃ j : Fin 8, pc = Lib.pvIssue j) :
    ∃ b, dst = 256 ∧ pollRound 2510 ((X.tr g).take k) = b ∧ 1 ≤ b ∧
      pollRound 2462 ((X.tr g).take k) ≤ b+1 ∧
      (∃ j : Fin 8, s.aTmem = some (128*((b-1)%2)+8*j.val)) ∧ g%L.block/32 = 7 ∧
      ∀ j : Fin 8, pc = Lib.pvIssue j → acc = true → 1 ≤ j.val ∨ 2 ≤ b := by
  obtain ⟨b, d, p, o, r, a, w, h, -, -⟩ := pv_block' hp hX hf base he pv
  refine ⟨b, d, p, o, r, a, w, fun j hj ha => ?_⟩
  have := h j hj
  rw [ha] at this
  have h2 := (by simpa using this.symm : ¬ j = 0 ∨ 2 ≤ b)
  rcases h2 with h2 | h2
  · left
    have := Fin.val_ne_of_ne h2
    simp at this
    omega
  · exact .inr h2

/-- **The accumulate flag of a PV issue**: step `0` of ordinal `1` overwrites, every other step
accumulates. -/
public theorem pv_acc {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    (pv : ∃ j : Fin 8, pc = Lib.pvIssue j) :
    ∃ b, pollRound 2510 ((X.tr g).take k) = b ∧
      (∀ j : Fin 8, pc = Lib.pvIssue j → acc = decide (j.val ≠ 0 ∨ 2 ≤ b)) ∧
      ∀ j : Fin 8, pc = Lib.pvIssue j → s.aTmem = some (128 * ((b - 1) % 2) + 8 * j.val) := by
  obtain ⟨b, -, p, -, -, -, -, h, hA, -⟩ := pv_block' hp hX hf base he pv
  exact ⟨b, p, h, hA⟩

/-- **The V operand of a PV issue** of block `b - 1`: the descriptor of its step, in the V tile
of the slot `(b - 1) % 3`. -/
public theorem pv_desc {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    (pv : ∃ j : Fin 8, pc = Lib.pvIssue j) :
    ∃ b, pollRound 2510 ((X.tr g).take k) = b ∧ ∀ j : Fin 8, pc = Lib.pvIssue j →
      s.b = ⟨((L.sharedBase + 98304 + 32768 * ((b - 1) % 3)) / 16 + 128 * j.val) * 16, 16384,
        1024, 0, false, false, .b128⟩ := by
  obtain ⟨b, -, p, -, -, -, -, -, -, d⟩ := pv_block' hp hX hf base he pv
  exact ⟨b, p, d⟩

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
