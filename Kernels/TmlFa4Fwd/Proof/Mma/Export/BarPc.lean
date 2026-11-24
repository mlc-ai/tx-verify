-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Entry
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Place
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Mma.Open
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2First
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.AllocBefore
import Lemmas.Kernel.Safety.Schedule
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The positions of the MMA warp's barrier events

No step leads to the first rendezvous `bar1` (`Mma.succ_b1`), so a lane meets it once, and its
barrier events are the startup's, `bar1`, then `bar2` (`mma_bar_pc`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The site is the first rendezvous. -/
def Mma.isB1 : Mma.Site → Bool
  | .bar1 => true
  | _ => false

theorem Mma.b1_wtNext : ∀ k, Mma.isB1 (Mma.wtNext k) = false := by decide
theorem Mma.b1_shNext : ∀ k, Mma.isB1 (Mma.shNext k) = false := by decide
theorem Mma.b1_qkDone : ∀ k, Mma.isB1 (Mma.qkDone k) = false := by decide
theorem Mma.b1_pvDone : ∀ k, Mma.isB1 (Mma.pvDone k) = false := by decide

theorem Mma.b1_passStart (late : Bool) (d : Mma.D) :
    Mma.isB1 (Mma.passStart p L g late d).site = false := by
  cases late <;> simp only [Mma.passStart] <;> split_ifs <;> rfl

theorem Mma.b1_ceNext (d : Mma.D) (c : Fin 12) :
    Mma.isB1 (Mma.ceNext p L g d c).site = false := by
  fin_cases c <;> simp only [Mma.ceNext, Mma.enterLoop, Mma.loopEnd, Mma.b1_passStart] <;>
    (try split) <;> rfl

theorem Mma.b1_afterTotal (k : Epilogue.Scan) (d : Mma.D) (x : BitVec 64) :
    Mma.isB1 (Mma.afterTotal p L g k d x).site = false := by
  cases k <;> simp only [Mma.afterTotal, Mma.scanExit, Mma.loopHead] <;> split_ifs <;> rfl

theorem Mma.b1_afterTiles {d d' : Mma.D} {x : BitVec 64}
    (h : Mma.afterTiles p L g d x = some d') : Mma.isB1 d'.site = false := by
  dsimp only [Mma.afterTiles] at h
  split_ifs at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

set_option maxHeartbeats 8000000 in
/-- **No step leads to the first rendezvous.** -/
theorem Mma.succ_b1 {d d' : Mma.D} {e : Event}
    (h : Mma.succ p L g d e = some (some d')) : Mma.isB1 d'.site = false := by
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Mma.succ, Mma.word32] at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; done)
    | (simp only [Option.some.injEq, reduceCtorEq] at h; subst h; rfl)
    | (simp only [Option.some.injEq] at h; subst h; rw [Mma.b1_afterTotal])
    | (simp only [Option.map_eq_some_iff, Option.some.injEq] at h
       obtain ⟨d0, h0, rfl⟩ := h
       rw [Mma.b1_afterTiles h0])
    | (simp only [Option.some.injEq, reduceCtorEq] at h; subst h
       simp only [Mma.scAt, Mma.afterTiles, Mma.afterTotal,
         Mma.b1_wtNext, Mma.b1_shNext, Mma.b1_qkDone, Mma.b1_pvDone, Mma.b1_ceNext,
         Mma.b1_passStart]
       try simp only [Mma.isB1]
       repeat' split
       all_goals first | rfl | (simp_all; done))

/-- A step from a role state leads to a role state off the first rendezvous. -/
private theorem step_b1 {i : Nat} {d : Mma.D} {n : Cls → Nat} {σ : (thread p L g).D}
    (hi : i + 1 ≤ (X.tr g).length)
    (h0 : Frame.stateAt (thread p L) X g i = some (some (Mma.minj p L g d n)))
    (h : Frame.stateAt (thread p L) X g (i + 1) = some (some σ)) :
    ∃ d1 n1, σ = Mma.minj p L g d1 n1 ∧ Mma.isB1 d1.site = false := by
  rw [Frame.stateAt_succ (List.getElem?_eq_getElem (by omega)), h0] at h
  obtain ⟨x, n1⟩ := σ
  obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L g) h
  simp only [glued, Code.glue, frag, Mma.M, Mma.G, Mma.code] at h1
  rcases hsu : Mma.succ p L g d _ with _ | _ | d1 <;> rw [hsu] at h1 <;>
    simp only [Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq] at h1
  subst h1
  exact ⟨d1, n1, rfl, Mma.succ_b1 hsu⟩

/-- **No role state precedes a state at the first rendezvous.** -/
theorem mma_bar1_first {k j : Nat} {d d' : Mma.D} {n n' : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (Mma.minj p L g d n)))
    (hs : d.site = .bar1) (hj : j < k) (hk : k ≤ (X.tr g).length) :
    Frame.stateAt (thread p L) X g j ≠ some (some (Mma.minj p L g d' n')) := by
  intro hσ'
  have key : ∀ i, j < i → i ≤ (X.tr g).length → ∀ σ,
      Frame.stateAt (thread p L) X g i = some (some σ) →
      ∃ d1 n1, σ = Mma.minj p L g d1 n1 ∧ Mma.isB1 d1.site = false := by
    intro i hji
    induction i, hji using Nat.le_induction with
    | base =>
      intro hi σ hσi
      exact step_b1 hi hσ' hσi
    | succ i _ ih =>
      intro hi σ hσi
      rcases h0 : Frame.stateAt (thread p L) X g i with _ | _ | σ0
      · rw [Frame.stateAt_succ (List.getElem?_eq_getElem (by omega)), h0] at hσi
        cases hσi
      · rw [Frame.stateAt_succ (List.getElem?_eq_getElem (by omega)), h0] at hσi
        cases hσi
      · obtain ⟨d1, n1, rfl, -⟩ := ih (by omega) σ0 h0
        exact step_b1 hi h0 hσi
  obtain ⟨d1, n1, he, hb⟩ := key k hj hk _ hσ
  simp only [Mma.minj, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at he
  obtain ⟨he, -⟩ := he
  cases he
  rw [hs] at hb
  cases hb

/-- A lane of the MMA warp's barrier events: the startup's, `bar1`, then `bar2`. -/
theorem mma_bar_pc (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 12) {k pc id : Nat} {cnt : Option Nat}
    {mode : BarMode} (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) :
    pc = mmaPc (((X.tr g).take k).countP Execution.isBar) := by
  have hg := Frame.lt_of_get hX he
  rcases Mma.open_ev hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, n, hσ, -, hJ, -, hev⟩ | ⟨s, n, -, -, -, hev⟩ | ⟨d, n, hσ, -, -, -, hev⟩
  · rw [start_bar_pc hp hX he hσ hJ hev, start_bar_ord hp hX hFw hg he hσ]
    rfl
  · exfalso
    rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  have hpc : pc = d.site.pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hσ
      (fun f h => by cases h)
  have hkl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  -- an earlier barrier-2 event has an earlier barrier event, and is the role's
  have two : ∀ {j pcj : Nat} {c : Option Nat} {md : BarMode}, j < k →
      X.get (g, j) = some ⟨pcj, .bar 2 c md⟩ → 2 ≤ ((X.tr g).take k).countP Execution.isBar := by
    intro j pcj c md hj hgj
    have hsj := bar_sched hp hX hFw hg hgj
    have h1 : ((X.tr g).take j).countP Execution.isBar ≠ 0 := by
      intro h
      rw [h, schedB_zero] at hsj
      cases hsj
    have h2 := Frame.countP_take_lt_countP (P := Execution.isBar) (es := (X.tr g).take k)
      (i := j) (by rw [List.getElem?_take, ite_eq_left hj]; exact hgj) rfl
    rw [List.take_take, Nat.min_eq_left hj.le] at h2
    omega
  have hge : 1 ≤ ((X.tr g).take k).countP Execution.isBar := by
    rw [← cls_bar (L := L) (g := g), count hσ]
    exact bar_count hp hX hFw hg k _ (Frame.noUbBefore_of_get hX he) hσ
  by_cases hb1 : d.site = .bar1
  · have h1 : ((X.tr g).take k).countP Execution.isBar = 1 := by
      by_contra hne
      obtain ⟨j, ev, hjg, hjb, hjc⟩ := MbarRing.Slot.exists_nth_countP Execution.isBar
        (show 1 + 1 ≤ ((X.tr g).take k).countP Execution.isBar by omega)
      have hjk : j < k := by
        have := (List.getElem?_eq_some_iff.mp hjg).1
        simp only [List.length_take] at this
        omega
      rw [List.take_take, Nat.min_eq_left hjk.le] at hjc
      have hgj : X.get (g, j) = some ev := by
        change (X.tr g)[j]? = _
        rw [← hjg, List.getElem?_take, ite_eq_left hjk]
      obtain ⟨pcj, kj⟩ := ev
      cases kj <;> simp [Execution.isBar] at hjb
      have hsj := bar_sched hp hX hFw hg hgj
      rw [hjc, schedB_one] at hsj
      simp only [Prod.mk.injEq] at hsj
      obtain ⟨rfl, -, -⟩ := hsj
      obtain ⟨d', n', hσ'⟩ := w12_bar2 hp hX hFw hgj hw
      exact mma_bar1_first hσ hb1 hjk hkl.le hσ'
    rw [h1, hpc, hb1]
    rfl
  · obtain ⟨j, hj, pcj, hgj⟩ := mma_bar1_before hp hX he hσ hb1
    have h2 := two hj hgj
    rw [hpc]
    simp only [mmaPc, show ((X.tr g).take k).countP Execution.isBar ≠ 0 by omega,
      show ((X.tr g).take k).countP Execution.isBar ≠ 1 by omega, ↓reduceIte]
    obtain ⟨site, v⟩ := d
    cases site <;> simp only [Mma.Ev] at hev
    case bar1 => exact absurd rfl hb1
    case bar2 l => rfl
    all_goals exfalso
    all_goals try exact epi_nobar hev _ _ _ rfl
    all_goals shape_destruct hev
    all_goals contradiction

end
end PTX.Kernels.TmlFa4Fwd.Proof
