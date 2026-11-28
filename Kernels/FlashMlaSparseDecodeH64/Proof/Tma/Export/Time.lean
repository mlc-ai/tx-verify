-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Wait
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Tma
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.LastTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.ObjCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefStep
import Lemmas.Step.ExitLast

@[expose] public section

/-! # The TMA lane's time facts

A lane whose next event is the TMA lane's wait at pc 2205 is a TMA state at the wait
(`tma_state`, `Common/Where.lean`), whose glued time is `qUtccpSlot` (`tma_slot_wait`): the
slot of the MMA lane's commit (`qUtccpSlot`), the TMA part of `QueryTime.slot`.

## The channel table (slots of `Lib/Slots.lean`, the CTA's block count `blocksOf P L c`)

The waits (lane `g` with `Sched.NextEv … g ⟨pc, .wait (mbarLoc L c f) p ok acq sc⟩`; no other
hypothesis): each gives an event of `g` at a `TmaOn` pc (so `g` is the CTA's `tmaLane`,
`laneOn_eq` with `TmaOne`), the use number `u = okPolls (mbarLoc L c f) (X.tr g)` below the CTA's
uses, and the slot of that use's block below the lane's time.

| channel | waiter (pc) | u bound | time bound |
|---|---|---|---|
| `last_store_done` | `tma_lastWait` (2209) | `u < 1` | `lastWait ≤ t` |
| `valid_coord_ready[j]` | `tma_crWait` (2234) | `u < ringUses 4 j R` | `crWaitT (4 u + j) ≤ t` |
| `raw_free[j]` | `tma_rfWait` (2245) | `u < ringUses 2 j R` | `rfWait (2 u + j) ≤ t` |

The producers (lane `g` that won its CTA's election: `hwin : X.get (g, k0) = some ⟨2165, .elect
(2 ^ 32 - 1) inst (PTX.laneOf L g)⟩`, from a `TmaOn` event by `tma_won_on`; `hc : g / L.block =
c`; with `a = arrivals (mbarLoc L c f) (X.tr g)`):

* `raw_ready[j]` (pc 2305, `N = 2`): early `tma_rrEarly` (`¬ HasUb X`, `a < ringUses 2 j R`):
  `t ≤ rrArr (2 a + j)`; exit `tma_rrExit` (`X.get (g, k) = some ⟨pc, .exit⟩`):
  `ringUses 2 j R ≤ a`.
* `raw_ready[j]` loads (pcs of the 16 gathers, `I = (X.tr g).countP (issuesTo (mbarLoc L c
  (.rawReady j)))`): early `tma_riEarly` (`I < 16 * ringUses 2 j R`): `t ≤ rrArr (2 (I / 16) + j)`;
  exit `tma_riExit`: `16 * ringUses 2 j R ≤ I`.
* `valid_coord_free[j]` (pc 2308, `N = 4`): early `tma_cfEarly`: `t ≤ cfArrT (4 a + j)`; exit
  `tma_cfExit`: `ringUses 4 j R ≤ a`.

All producer facts come from one view of the lane's last state (`tma_end`): the election or a
prologue state (time at most `137`), a block-`r` state at `frame r + tmaOff + x` with its counts
(`Tma.cntAt`), or the CTA barrier or the exit after it with every block's counts
(`tma_exit_full`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

/-- A site of stage 3 (the arrival on `coordFree`) is past the block's 16 gathers. -/
private theorem stage_gN (s : Tma.Site) : s.stage < 3 ∨ s.gN = 16 := by
  cases s <;> simp [Tma.Site.stage, Tma.Site.gN]

/-! ### The view of the winner's last state -/

section
variable {g : Nat}

/-- A state's counts on the role's classes at prefix `i`. -/
private def pc' (X : Execution) (g i : Nat) : Tma.Cnt → Nat :=
  fun c => ((X.tr g).take i).countP (Tma.cls c)

/-- The counts after every block, before the CTA barrier. -/
private abbrev Full (L : Launch) (g : Nat) (n : Tma.Cnt → Nat) (R : Nat) : Prop :=
  ∀ c, c ≠ .ub → n c = Tma.cntAt (Tma.objs L g) 3 R 0 0 0 false c

/-- No undefined behaviour in any prefix. -/
private theorem noUbG (hub : ¬ HasUb X) (i : Nat) : ((X.tr g).take i).countP (cls .ub) = 0 :=
  List.countP_eq_zero.mpr fun f hf hcl => hub (by
    obtain ⟨j, -, hj⟩ := get_lt_of_mem_take hf
    obtain ⟨pc, kd⟩ := f
    cases kd <;> simp [cls] at hcl
    exact ⟨(g, j), pc, _, hj⟩)

variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  {j inst : Nat} (hj : X.get (g, j) = some ⟨2165, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩)
include hp hX hFw hj

/-- **The time of a state of the winner from its election on**, plus `δ` when the machine
stops after it. -/
private theorem tma_step (hub : ¬ HasUb X) {Q : Nat → Prop} (hpro : ∀ t, t ≤ 137 → Q t)
    (hloop : ∀ i r x (s : Tma.Site), i ≤ (X.tr g).length → r < blocksOf P L (g / L.block) →
      x ≤ 83 → (s.stage < 3 → x ≤ 82) →
      (∀ c, c ≠ .ub → pc' X g i c = Tma.cntAt (Tma.objs L g) 3 r s.stage s.rdN s.gN false c) →
      Q (frame r + tmaOff + x))
    (hend : ∀ i, i ≤ (X.tr g).length → Full L g (pc' X g i) (blocksOf P L (g / L.block)) → False)
    {i δ : Nat} {σ : (thread P L g).D} (hi : i ≤ (X.tr g).length) (hji : j ≤ i) (hδ : δ ≤ 1)
    (hσ : Frame.stateAt (thread P L) X g i = some (some σ))
    (hmv : δ = 1 → ∀ d n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n) →
      d.site ≠ .rawArrive ∧ d.site ≠ .coordFree) :
    Q (time P L g σ + δ) := by
  rcases Nat.eq_or_lt_of_le hji with rfl | hji
  · obtain ⟨σj, hσj, hJj, hij, hevj, hpcj⟩ := ev_at hp hX hFw hj (fun _ h => by cases h)
    rw [hσj, Option.some.injEq, Option.some.injEq] at hσ
    subst hσ
    obtain ⟨dj, nj, rfl, -, -, hEj, hlj, -⟩ := tma_state hJj hij hevj hpcj
      ⟨show 2162 ≤ 2165 by decide, show 2165 < 2332 by decide⟩
    obtain ⟨hsj, -, -⟩ := Tma.ev_elect hlj hEj
    have h0 : Tma.place dj = 0 := by
      rw [Tma.place_pro (by rw [hsj]; exact ⟨rfl, by simp, by simp⟩), hsj]
      rfl
    apply hpro
    simp only [time, fragTime, wg1Time, tmaTime, Tma.time, h0, idleBase, roleBase]
    omega
  obtain ⟨d, n, rfl, hP, hw, hR⟩ := tma_win_state hp hX hFw hj hji hσ (noUbG hub i)
  have ht : time P L g (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n) = tmaOrg + Tma.place d := by
    simp only [time, fragTime, wg1Time, tmaTime, Tma.time, idleBase, roleBase, tmaOrg]
  rw [ht]
  by_cases hlp : d.site.inLoop = true
  · obtain ⟨⟨-, -, -, hrR, -⟩, hcnt⟩ := (Tma.core_loop hlp).mp hR
    rw [tma_rounds_of (fun h => by rw [h] at hlp; cases hlp)
      (fun h => by rw [h] at hlp; cases hlp) hw] at hrR
    have hpl := Tma.place_loop hlp
    have hx : d.site.idx + δ ≤ 83 ∧ (d.site.stage < 3 → d.site.idx + δ ≤ 82) := by
      rcases Tma.idx_mid d.site with h | h | h
      · exact ⟨by omega, fun _ => by omega⟩
      · have h0 : δ = 0 := by
          by_contra h1
          exact (hmv (by omega) d n rfl).1 h
        simp only [h, h0, Tma.Site.idx, Tma.Site.stage, Tma.Site.rdN, Tma.Site.gN]
        omega
      · have h0 : δ = 0 := by
          by_contra h1
          exact (hmv (by omega) d n rfl).2 h
        simp only [h, h0, Tma.Site.idx, Tma.Site.stage, Tma.Site.rdN, Tma.Site.gN]
        omega
    have heq : tmaOrg + Tma.place d + δ = frame d.cnt.toNat + tmaOff + (d.site.idx + δ) := by
      rw [hpl]
      simp only [frame, tmaOrg, tmaBlk0, loopBase, tmaOff, stride]
      omega
    rw [heq]
    exact hloop i _ _ d.site hi hrR hx.1 hx.2 hcnt
  by_cases hb : d.site = .outBar
  · simp only [Tma.RefCore, hb] at hR
    rw [tma_rounds_of (by rw [hb]; simp) (by rw [hb]; simp) hw] at hR
    exact (hend i hi hR).elim
  by_cases hx : d.site = .exit
  · obtain ⟨i', -, hi', hF⟩ := tma_exit_full hp hX hFw hj hji hi (noUbG hub i) hσ hx
    exact (hend i' (by omega) hF).elim
  · have hpl := Tma.place_pro_le ⟨by simpa using hlp, hx, hb⟩
    exact hpro _ (by simp only [tmaOrg]; omega)

/-- **The winner's last state**: the principle behind the producers' facts. -/
private theorem tma_end (hub : ¬ HasUb X) {Q : Nat → Prop} (hpro : ∀ t, t ≤ 137 → Q t)
    (hloop : ∀ i r x (s : Tma.Site), i ≤ (X.tr g).length → r < blocksOf P L (g / L.block) →
      x ≤ 83 → (s.stage < 3 → x ≤ 82) →
      (∀ c, c ≠ .ub → pc' X g i c = Tma.cntAt (Tma.objs L g) 3 r s.stage s.rdN s.gN false c) →
      Q (frame r + tmaOff + x))
    (hend : ∀ i, i ≤ (X.tr g).length → Full L g (pc' X g i) (blocksOf P L (g / L.block)) → False) :
    Q (Sched.threadTime (timed P L) X g) := by
  have hjl : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hj).1
  refine time_last (hpro 0 (by omega)) (fun σ hs => ?_) (fun σ f hs hf hn => ?_)
  · simpa using tma_step hp hX hFw hj hub hpro hloop hend (Nat.le_refl _) hjl.le (Nat.zero_le 1)
      hs (by omega)
  · refine tma_step hp hX hFw hj hub hpro hloop hend (by omega) (by omega) (Nat.le_refl 1) hs
      fun _ d n hd => ?_
    rw [hd] at hn
    exact ⟨fun h => tma_arr_next (.inl h) hn, fun h => tma_arr_next (.inr h) hn⟩

/-- **The counts behind the winner's exit**: at a prefix every block's. -/
private theorem exit_full {k pc : Nat} (hx : X.get (g, k) = some ⟨pc, .exit⟩) :
    ∃ i, i ≤ (X.tr g).length ∧ Full L g (pc' X g i) (blocksOf P L (g / L.block)) := by
  have hk := Execution.exit_last hX (Frame.lt_of_get hX hx) hx
  have hjl : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hj).1
  have hjk : j < k := by
    refine Nat.lt_of_le_of_ne (by omega) fun h => ?_
    rw [h, hx] at hj
    cases hj
  obtain ⟨σ, hσ, -, -, hev, -⟩ := ev_at hp hX hFw hx (fun _ h => by cases h)
  have hu : ((X.tr g).take k).countP (cls .ub) = 0 :=
    (state_count hσ .ub).symm.trans (state_ub hX hσ hx)
  obtain ⟨d, n, rfl, hP, -, -⟩ := tma_win_state hp hX hFw hj hjk hσ hu
  have hE : Tma.Ev L g d ⟨pc, .exit⟩ := hev
  obtain ⟨i', -, hi', hF⟩ := tma_exit_full hp hX hFw hj hjk (by omega) hu hσ
    (Tma.ev_exit hP.2 hE rfl)
  exact ⟨i', by omega, hF⟩

/-- The arrivals of the lane on its CTA's objects at prefix `i`. -/
private theorem arr_at (i : Nat) (f : MbarFam) :
    arrivals (MbarRow.loc L g f) ((X.tr g).take i) ≤ arrivals (MbarRow.loc L g f) (X.tr g) ∧
    arrivals (MbarRow.loc L g f) ((X.tr g).take i) = pc' X g i (.arrive (MbarRow.loc L g f)) := by
  obtain ⟨σj, hσj, hJj, hij, hevj, hpcj⟩ := ev_at hp hX hFw hj (fun _ h => by cases h)
  obtain ⟨-, -, -, -, -, -, -, hw⟩ := tma_state hJj hij hevj hpcj
    ⟨show 2162 ≤ 2165 by decide, show 2165 < 2332 by decide⟩
  exact ⟨(List.take_sublist i _).countP_le, lane5_arrivals hp hX hFw hw i _⟩

/-- **The TMA lane short of its uses of `rawReady j` is no later than the arrival slot of its next
use.** -/
theorem tma_rrEarly (hub : ¬ HasUb X) {c : Nat} {s : Fin 2} (hc : g / L.block = c)
    (hlt : arrivals (mbarLoc L c (.rawReady s)) (X.tr g) < ringUses 2 s.val (blocksOf P L c)) :
    Sched.threadTime (timed P L) X g ≤
      rrArr (2 * arrivals (mbarLoc L c (.rawReady s)) (X.tr g) + s.val) := by
  subst hc
  have hs := s.isLt
  refine tma_end (Q := fun t => t ≤ rrArr (2 * arrivals (mbarLoc L (g / L.block) (.rawReady s))
    (X.tr g) + s.val)) hp hX hFw hj hub (fun t ht => ?_) (fun i r x s' hi _ hx h3 hcnt => ?_)
    (fun i hi hF => ?_)
  · simp only [rrArr, frame, loopBase, stride, tmaOff, tmaRa]
    omega
  · obtain ⟨hle, heq⟩ := arr_at hp hX hFw hj i (.rawReady s)
    rw [heq, hcnt _ (by simp), Tma.tcnt_raw hp] at hle
    simp only [MbarRow.loc] at hle
    simp only [Tma.useAt, Tma.ind, ringUses, rrArr, frame, loopBase, stride, tmaOff, tmaRa] at hle ⊢
    split_ifs at hle <;> omega
  · obtain ⟨hle, heq⟩ := arr_at hp hX hFw hj i (.rawReady s)
    rw [heq, hF _ (by simp), Tma.tcnt_raw hp] at hle
    simp only [MbarRow.loc] at hle
    simp only [Tma.useAt, Tma.ind, ringUses] at hle hlt
    omega

/-- **The TMA lane that exited has made all its uses of `rawReady j`.** -/
theorem tma_rrExit {c k pc : Nat} {s : Fin 2} (hc : g / L.block = c)
    (hx : X.get (g, k) = some ⟨pc, .exit⟩) :
    ringUses 2 s.val (blocksOf P L c) ≤ arrivals (mbarLoc L c (.rawReady s)) (X.tr g) := by
  subst hc
  obtain ⟨i, -, hF⟩ := exit_full hp hX hFw hj hx
  obtain ⟨hle, heq⟩ := arr_at hp hX hFw hj i (.rawReady s)
  rw [heq, hF _ (by simp), Tma.tcnt_raw hp] at hle
  simp only [MbarRow.loc] at hle
  simp only [Tma.useAt, Tma.ind, ringUses] at hle ⊢
  omega

/-- **The TMA lane short of its uses of `coordFree j` is no later than the arrival slot of its
next use.** -/
theorem tma_cfEarly (hub : ¬ HasUb X) {c : Nat} {s : Fin 4} (hc : g / L.block = c)
    (hlt : arrivals (mbarLoc L c (.coordFree s)) (X.tr g) < ringUses 4 s.val (blocksOf P L c)) :
    Sched.threadTime (timed P L) X g ≤
      cfArrT (4 * arrivals (mbarLoc L c (.coordFree s)) (X.tr g) + s.val) := by
  subst hc
  have hs := s.isLt
  refine tma_end (Q := fun t => t ≤ cfArrT (4 * arrivals (mbarLoc L (g / L.block) (.coordFree s))
    (X.tr g) + s.val)) hp hX hFw hj hub (fun t ht => ?_) (fun i r x s' hi _ hx _ hcnt => ?_)
    (fun i hi hF => ?_)
  · simp only [cfArrT, frame, loopBase, stride, tmaOff, tmaCf]
    omega
  · obtain ⟨hle, heq⟩ := arr_at hp hX hFw hj i (.coordFree s)
    rw [heq, hcnt _ (by simp), Tma.tcnt_cfree hp] at hle
    simp only [MbarRow.loc] at hle
    simp only [ringUses, cfArrT, frame, loopBase, stride, tmaOff, tmaCf] at hle ⊢
    omega
  · obtain ⟨hle, heq⟩ := arr_at hp hX hFw hj i (.coordFree s)
    rw [heq, hF _ (by simp), Tma.tcnt_cfree hp] at hle
    simp only [MbarRow.loc] at hle
    simp only [ringUses] at hle hlt
    omega

/-- **The TMA lane that exited has made all its uses of `coordFree j`.** -/
theorem tma_cfExit {c k pc : Nat} {s : Fin 4} (hc : g / L.block = c)
    (hx : X.get (g, k) = some ⟨pc, .exit⟩) :
    ringUses 4 s.val (blocksOf P L c) ≤ arrivals (mbarLoc L c (.coordFree s)) (X.tr g) := by
  subst hc
  obtain ⟨i, -, hF⟩ := exit_full hp hX hFw hj hx
  obtain ⟨hle, heq⟩ := arr_at hp hX hFw hj i (.coordFree s)
  rw [heq, hF _ (by simp), Tma.tcnt_cfree hp] at hle
  simp only [MbarRow.loc] at hle ⊢
  exact hle

/-- The lane's tensor loads on its CTA's objects at prefix `i`. -/
private theorem iss_at (i : Nat) (f : MbarFam) :
    ((X.tr g).take i).countP (issuesTo (MbarRow.loc L g f)) ≤
      (X.tr g).countP (issuesTo (MbarRow.loc L g f)) ∧
    ((X.tr g).take i).countP (issuesTo (MbarRow.loc L g f)) =
      pc' X g i (.gather (MbarRow.loc L g f)) := by
  obtain ⟨σj, hσj, hJj, hij, hevj, hpcj⟩ := ev_at hp hX hFw hj (fun _ h => by cases h)
  obtain ⟨-, -, -, -, -, -, -, hw⟩ := tma_state hJj hij hevj hpcj
    ⟨show 2162 ≤ 2165 by decide, show 2165 < 2332 by decide⟩
  exact ⟨(List.take_sublist i _).countP_le, lane5_issues hp hX hFw hw i _⟩

/-- **The TMA lane short of its loads on `rawReady j`** is no later than the arrival slot of the
block of its next load: with `I` loads made, block `2 (I / 16) + j`. -/
theorem tma_riEarly (hub : ¬ HasUb X) {c : Nat} {s : Fin 2} (hc : g / L.block = c)
    (hlt : (X.tr g).countP (issuesTo (mbarLoc L c (.rawReady s))) <
      16 * ringUses 2 s.val (blocksOf P L c)) :
    Sched.threadTime (timed P L) X g ≤
      rrArr (2 * ((X.tr g).countP (issuesTo (mbarLoc L c (.rawReady s))) / 16) + s.val) := by
  subst hc
  have hs := s.isLt
  refine tma_end (Q := fun t => t ≤ rrArr (2 * ((X.tr g).countP
    (issuesTo (mbarLoc L (g / L.block) (.rawReady s))) / 16) + s.val)) hp hX hFw hj hub
    (fun t ht => ?_) (fun i r x s' hi _ hx h3 hcnt => ?_) (fun i hi hF => ?_)
  · simp only [rrArr, frame, loopBase, stride, tmaOff, tmaRa]
    omega
  · obtain ⟨hle, heq⟩ := iss_at hp hX hFw hj i (.rawReady s)
    rw [heq, hcnt _ (by simp), Tma.tcnt_gather hp] at hle
    simp only [MbarRow.loc] at hle
    have hg := stage_gN s'
    simp only [Tma.ind, ringUses, rrArr, frame, loopBase, stride, tmaOff, tmaRa] at hle ⊢
    split_ifs at hle <;> omega
  · obtain ⟨hle, heq⟩ := iss_at hp hX hFw hj i (.rawReady s)
    rw [heq, hF _ (by simp), Tma.tcnt_gather hp] at hle
    simp only [MbarRow.loc] at hle
    simp only [Tma.ind, ringUses] at hle hlt
    split_ifs at hle <;> omega

/-- **The TMA lane that exited has made all its loads on `rawReady j`** (16 per use). -/
theorem tma_riExit {c k pc : Nat} {s : Fin 2} (hc : g / L.block = c)
    (hx : X.get (g, k) = some ⟨pc, .exit⟩) :
    16 * ringUses 2 s.val (blocksOf P L c) ≤
      (X.tr g).countP (issuesTo (mbarLoc L c (.rawReady s))) := by
  subst hc
  obtain ⟨i, -, hF⟩ := exit_full hp hX hFw hj hx
  obtain ⟨hle, heq⟩ := iss_at hp hX hFw hj i (.rawReady s)
  rw [heq, hF _ (by simp), Tma.tcnt_gather hp] at hle
  simp only [MbarRow.loc] at hle
  simp only [Tma.ind] at hle
  split_ifs at hle <;> omega

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
