-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.LastTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.SubWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.EarlyCore

@[expose] public section

/-! # Warpgroup 0's time at its waits and before its arrivals

A lane of warpgroup 0 whose next event is a wait is at that wait's slot (`Lib/Slots.lean`), the
block read off the lane's successful polls: at pc 264 on `valid_coord_ready` at
`crWaitW0 (polls4 … coordReady es)` (`wg0_slot_ready`, `wg0_crWait`), at pc 272 on `qk_done` at
`qkWait (polls2 … qkDone es)` (`wg0_slot_qk`; per slot `wg0_qkWait`: the use of slot `j` is the
lane's successful polls of it), at pc 1184 on `sv_done` at `svWaitW0 (polls2 … qkDone es)`
(`wg0_slot_sv`; `wg0_svWait`: the slot and parity of the CTA's last block). A lane whose next
event is warpgroup 0's is no later than the slot of its next arrival on each channel, read off its
arrivals (`wg0_slot_last`, `wg0_slot_free`, `wg0_slot_so`). The state behind the next event is
taken privately (`next_state`, `end_state`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat} {e : Event}


private theorem end_state (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hn : Sched.NextEv L kernel Assumptions.all m X y e)
    (hub : ∀ f, e.kind ≠ .ub f) (hpc : 103 ≤ e.pc ∧ e.pc < 1842) :
    ∃ d : Wg0.Control.D, Wg0.RefCore L y d (fun c => (X.tr y).countP (Wg0.cls c)) ∧
      Wg0.Ev P L y (warpW L y) d e ∧
      Sched.threadTime (timed P L) X y = roleBase + Wg0.place d ∧
      (∀ l, okPolls l (X.tr y) = (X.tr y).countP (Wg0.cls (.acq l))) ∧
      (∀ l, arrivals l (X.tr y) = (X.tr y).countP (Wg0.cls (.arrive l))) ∧
      Wg0.LaunchOk P L y d := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := next_state hp hFw hn hub
  obtain ⟨d, n, rfl, hR, hE, hw⟩ := wg0_state hJ hi hev hpc' hpc
  obtain ⟨Y, hY, hpre, he⟩ := hn
  have hσY : Frame.stateAt (thread P L) Y y (X.tr y).length = some (some (_, n)) :=
    (Sched.stateAt_congr (by rw [hpre, List.take_length])).trans hσ
  have hc : (fun c => n (.wg0 c)) = fun c => (X.tr y).countP (Wg0.cls c) :=
    funext fun c => (state_count hσ (.wg0 c)).trans (by rw [List.take_length]; rfl)
  have hu : (X.tr y).countP (Wg0.cls .ub) = 0 := by
    rw [← hpre]
    exact wg0_take_noUb hY he
  have hR' := hR (state_ub hY hσY he)
  rw [hc] at hR'
  obtain ⟨hR'', hL, -⟩ := hR' hu
  refine ⟨d, hR'', hE, ?_, fun l => ?_, fun l => ?_, hL⟩
  · rw [timed_eq, Sched.threadTime_of hσ]
    rfl
  · simpa only [List.take_length] using wg0_okPolls hp hX hFw hw (X.tr y).length l
  · simpa only [List.take_length] using wg0_arrivals hp hX hFw hw (X.tr y).length l

private theorem glue : roleBase = wg0Org := rfl

/-- **At its poll of `valid_coord_ready`, a lane is at the slot of its block.** -/
theorem wg0_slot_ready (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {l : Loc} {q : Nat} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X y ⟨264, .wait l q ok acq sc⟩) :
    Sched.threadTime (timed P L) X y = crWaitW0 (polls4 L y .coordReady (X.tr y)) := by
  obtain ⟨d, hc, ⟨hpc, hk⟩, ht, hP, -⟩ := end_state hp hX hFw hn (fun _ h => by cases h)
    ⟨by simp, by simp⟩
  rw [ht]
  rcases Wg0.evK_wait_site hk rfl with hs | hs | hs <;> rw [hs] at hpc <;>
    simp only [Wg0.Site.pc] at hpc <;> (try omega)
  unfold Wg0.RefCore Wg0.RefAt at hc
  rw [hs] at hc
  obtain ⟨r, ⟨-, hR, hr, hbi, -⟩, hn', -⟩ := hc
  obtain ⟨h4, -⟩ := Wg0.ready_cnt hp fun l => (hP l).trans (hn' l)
  rw [h4, Wg0.place_reg (by simp [hs]), hs]
  simp only [Wg0.Site.reg, Wg0.regPlace, Wg0.Site.ord, Wg0.elOff, hs, Wg0.Control.D.words] at hbi ⊢
  rw [hbi, PTX.Flow.Arith32.toNat_W (by omega)]
  simp only [crWaitW0, frame, stride, Nat.add_sub_cancel, glue, wg0Blk0, wg0Off, wg0Org, loopBase,
    w0Wv]
  omega

/-- **At its poll of `valid_coord_ready j` of CTA `c`, a lane of CTA `c` past barrier 0 polls a
use below the CTA's uses of the slot, no earlier than the wait's slot of that use's block.** -/
theorem wg0_crWait (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {c p : Nat} {j : Fin 4} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X y
      ⟨264, .wait (mbarLoc L c (.coordReady j)) p ok acq sc⟩) :
    y / L.block = c ∧
    okPolls (mbarLoc L c (.coordReady j)) (X.tr y) < ringUses 4 j.val (blocksOf P L c) ∧
    crWaitW0 (4 * okPolls (mbarLoc L c (.coordReady j)) (X.tr y) + j.val) ≤
      Sched.threadTime (timed P L) X y ∧ 0 < (X.tr y).countP isBar0 := by
  have hb0 : 0 < (X.tr y).countP isBar0 := by
    obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := next_state hp hFw hn (fun _ h => by cases h)
    obtain ⟨d, n, rfl, -⟩ := wg0_state hJ hi hev hpc' ⟨by simp, by simp⟩
    have hb : n .bar0 = ((X.tr y).take (X.tr y).length).countP isBar0 := state_count hσ .bar0
    have h1 : 1 ≤ n .bar0 := hJ.1
    rw [List.take_length] at hb; omega
  have ht := wg0_slot_ready hp hX hFw hn
  obtain ⟨d, hc, ⟨hpc, hk⟩, -, hP, -, hL⟩ := end_state hp hX hFw hn (fun _ h => by cases h)
    ⟨by simp, by simp⟩
  rcases Wg0.evK_wait_site hk rfl with hs | hs | hs <;> rw [hs] at hpc <;>
    simp only [Wg0.Site.pc] at hpc <;> (try omega)
  have hb := Wg0.rounds_blocks hL (by rw [hs]; decide)
  unfold Wg0.EvK at hk; unfold Wg0.RefCore Wg0.RefAt at hc; rw [hs] at hk hc
  obtain ⟨r, ⟨-, -, hr, -, -, hvs, -⟩, hn', -⟩ := hc
  obtain ⟨h4, h1⟩ := Wg0.ready_cnt hp fun l => (hP l).trans (hn' l)
  rcases hk with ⟨ok', hk⟩ | ⟨f, hk⟩
  · simp only [Kind.wait.injEq] at hk; obtain ⟨hl, -⟩ := hk
    obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
    simp only [Wg0.Control.D.words] at hvs hr hb; subst hvs
    obtain ⟨hcy, hf⟩ := by simpa only [loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff,
      true_and] using hl.trans (Wg0.vReady_loc hp (slot4 r))
    have hj : j = slot4 r := MbarFam.coordReady.inj (MbarFam.off_inj hf)
    subst hcy hj; rw [h1, ← hb, ht, h4]
    refine ⟨rfl, ?_, ?_, hb0⟩
    · simp only [ringUses, slot4]; omega
    · simp only [slot4]; rw [show 4 * (r / 4) + r % 4 = r by omega]
  · cases hk

/-- **At its poll of `qk_done`, a lane is at the slot of its block.** -/
theorem wg0_slot_qk (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {l : Loc} {q : Nat} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X y ⟨272, .wait l q ok acq sc⟩) :
    Sched.threadTime (timed P L) X y = qkWait (polls2 L y .qkDone (X.tr y)) := by
  obtain ⟨d, hc, ⟨hpc, hk⟩, ht, hP, -⟩ := end_state hp hX hFw hn (fun _ h => by cases h)
    ⟨by simp, by simp⟩
  rw [ht]
  rcases Wg0.evK_wait_site hk rfl with hs | hs | hs <;> rw [hs] at hpc <;>
    simp only [Wg0.Site.pc] at hpc <;> (try omega)
  unfold Wg0.RefCore Wg0.RefAt at hc
  rw [hs] at hc
  obtain ⟨r, ⟨-, hR, hr, hbi, -⟩, hn', -⟩ := hc
  obtain ⟨h2, -⟩ := Wg0.qk_cnt hp (by decide) fun l => (hP l).trans (hn' l)
  rw [h2, Wg0.place_reg (by simp [hs]), hs]
  simp only [Wg0.Site.reg, Wg0.regPlace, Wg0.Site.ord, Wg0.elOff, hs, Wg0.Control.D.words] at hbi ⊢
  rw [hbi, PTX.Flow.Arith32.toNat_W (by omega)]
  simp only [qkWait, frame, stride, Nat.add_sub_cancel, glue, wg0Blk0, wg0Off, wg0Org, loopBase,
    w0Wq]
  omega

/-- **At its poll of `sv_done`, a lane is at the slot after its blocks.** -/
theorem wg0_slot_sv (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {l : Loc} {q : Nat} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X y ⟨1184, .wait l q ok acq sc⟩) :
    Sched.threadTime (timed P L) X y = svWaitW0 (polls2 L y .qkDone (X.tr y)) := by
  obtain ⟨d, hc, ⟨hpc, hk⟩, ht, hP, -⟩ := end_state hp hX hFw hn (fun _ h => by cases h)
    ⟨by simp, by simp⟩
  rw [ht]
  rcases Wg0.evK_wait_site hk rfl with hs | hs | hs <;> rw [hs] at hpc <;>
    simp only [Wg0.Site.pc] at hpc <;> (try omega)
  unfold Wg0.RefCore Wg0.RefAt at hc
  rw [hs] at hc
  simp only [Wg0.Site.reg, Wg0.Site.idx, Nat.reduceEqDiff, ↓reduceIte] at hc
  obtain ⟨-, hn', -⟩ := hc
  obtain ⟨h2, -⟩ := Wg0.qk_cnt hp (by decide) fun l => (hP l).trans (hn' l)
  rw [h2, Wg0.place_reg (by simp [hs]), hs]
  simp only [Wg0.Site.reg, Wg0.regPlace, Wg0.Site.ord, Wg0.elOff, hs, Wg0.Control.D.words]
  simp only [svWaitW0, epi, frame, stride, glue, wg0EpiBlk0, w0Epi, wg0Org, loopBase, w0Wsv]
  omega

/-! ### Before an arrival -/

private theorem early_state (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hn : Sched.NextEv L kernel Assumptions.all m X y e)
    (hub : ∀ f, e.kind ≠ .ub f) (hpc : 103 ≤ e.pc ∧ e.pc < 1842) :
    (∃ a r i, (∀ l, arrivals l (X.tr y) = Wg0.arrCnt (Wg0.objs L y) a r i l) ∧
      (a = false → Sched.threadTime (timed P L) X y ≤ lastArr) ∧
      Sched.threadTime (timed P L) X y ≤ wg0Org + wg0Blk0 + stride * r + w0ArrS ∧
      (i ≤ 2 → Sched.threadTime (timed P L) X y ≤ wg0Org + wg0Blk0 + stride * r + w0ArrV)) ∨
    (∀ l, arrivals l (X.tr y) =
      Wg0.arrCnt (Wg0.objs L y) true (blocksOf P L (y / L.block)) 0 l) := by
  obtain ⟨d, hc, -, ht, -, hA, hL⟩ := end_state hp hX hFw hn hub hpc
  rcases Wg0.early_core hc hL with ⟨a, r, i, hC, h5, hS, hV⟩ | hC
  · rw [ht, glue]
    exact .inl ⟨a, r, i, fun l => (hA l).trans (hC l),
      fun h => by have := h5 h; simp only [lastArr, w0ArrL]; omega,
      by omega, fun h => by have := hV h; omega⟩
  · exact .inr fun l => (hA l).trans (hC l)


/-! ### The score ring's waits, per slot -/

/-- **At its poll of `qk_done j` of CTA `c`, a lane of CTA `c` past barrier 0 polls a use below
the CTA's uses of the slot, no earlier than the wait's slot of that use's block** (block
`2 u + j`, `u` its successful polls of the slot). -/
theorem wg0_qkWait (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {c p : Nat} {j : Fin 2} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X y
      ⟨272, .wait (mbarLoc L c (.qkDone j)) p ok acq sc⟩) :
    y / L.block = c ∧
    okPolls (mbarLoc L c (.qkDone j)) (X.tr y) < ringUses 2 j.val (blocksOf P L c) ∧
    qkWait (2 * okPolls (mbarLoc L c (.qkDone j)) (X.tr y) + j.val) ≤
      Sched.threadTime (timed P L) X y ∧ 0 < (X.tr y).countP isBar0 := by
  have hb0 : 0 < (X.tr y).countP isBar0 := by
    obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := next_state hp hFw hn (fun _ h => by cases h)
    obtain ⟨d, n, rfl, -⟩ := wg0_state hJ hi hev hpc' ⟨by simp, by simp⟩
    have hb : n .bar0 = ((X.tr y).take (X.tr y).length).countP isBar0 := state_count hσ .bar0
    have h1 : 1 ≤ n .bar0 := hJ.1
    rw [List.take_length] at hb; omega
  have ht := wg0_slot_qk hp hX hFw hn
  obtain ⟨d, hc, ⟨hpc, hk⟩, -, hP, -, hL⟩ := end_state hp hX hFw hn (fun _ h => by cases h)
    ⟨by simp, by simp⟩
  rcases Wg0.evK_wait_site hk rfl with hs | hs | hs <;> rw [hs] at hpc <;>
    simp only [Wg0.Site.pc] at hpc <;> (try omega)
  have hb := Wg0.rounds_blocks hL (by rw [hs]; decide)
  unfold Wg0.EvK at hk; unfold Wg0.RefCore Wg0.RefAt at hc; rw [hs] at hk hc
  obtain ⟨r, ⟨-, -, hr, -, -, -, -, hsl, -⟩, hn', -⟩ := hc
  obtain ⟨h2, h1⟩ := Wg0.qk_cnt hp (by decide) fun l => (hP l).trans (hn' l)
  rcases hk with ⟨ok', hk⟩ | ⟨f, hk⟩
  · simp only [Kind.wait.injEq] at hk; obtain ⟨hl, -⟩ := hk
    obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
    simp only [Wg0.Control.D.words] at hsl hr hb; subst hsl
    obtain ⟨hcy, hf⟩ := by simpa only [loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff,
      true_and] using hl.trans (Wg0.qk_loc hp (slot2 r))
    have hj : j = slot2 r := MbarFam.qkDone.inj (MbarFam.off_inj hf)
    subst hcy hj; rw [h1, ← hb, ht, h2]
    refine ⟨rfl, ?_, ?_, hb0⟩
    · simp only [ringUses, slot2]; omega
    · simp only [slot2]; rw [show 2 * (r / 2) + r % 2 = r by omega]
  · cases hk

/-- **At its poll of `sv_done j` of CTA `c` (pc 1184), a lane of CTA `c` past barrier 0 polls
the slot of the CTA's last block with that block's parity, no earlier than the wait's slot.** -/
theorem wg0_svWait (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {c p : Nat} {j : Fin 2} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X y
      ⟨1184, .wait (mbarLoc L c (.svDone j)) p ok acq sc⟩) :
    y / L.block = c ∧ j = slot2 (blocksOf P L c - 1) ∧
    p % 2 = (blocksOf P L c - 1) / 2 % 2 ∧
    svWaitW0 (blocksOf P L c) ≤ Sched.threadTime (timed P L) X y ∧
    0 < (X.tr y).countP isBar0 := by
  have hb0 : 0 < (X.tr y).countP isBar0 := by
    obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := next_state hp hFw hn (fun _ h => by cases h)
    obtain ⟨d, n, rfl, -⟩ := wg0_state hJ hi hev hpc' ⟨by simp, by simp⟩
    have hb : n .bar0 = ((X.tr y).take (X.tr y).length).countP isBar0 := state_count hσ .bar0
    have h1 : 1 ≤ n .bar0 := hJ.1
    rw [List.take_length] at hb; omega
  have ht := wg0_slot_sv hp hX hFw hn
  obtain ⟨d, hc, ⟨hpc, hk⟩, -, hP, -, hL⟩ := end_state hp hX hFw hn (fun _ h => by cases h)
    ⟨by simp, by simp⟩
  rcases Wg0.evK_wait_site hk rfl with hs | hs | hs <;> rw [hs] at hpc <;>
    simp only [Wg0.Site.pc] at hpc <;> (try omega)
  have hb := Wg0.rounds_blocks hL (by rw [hs]; decide)
  unfold Wg0.EvK at hk; unfold Wg0.RefCore Wg0.RefAt at hc; rw [hs] at hk hc
  simp only [Wg0.Site.reg, Wg0.Site.idx, Nat.reduceEqDiff, ↓reduceIte] at hc
  obtain ⟨⟨hsl, hps⟩, hn', -⟩ := hc
  obtain ⟨h2, -⟩ := Wg0.qk_cnt hp (by decide) fun l => (hP l).trans (hn' l)
  rcases hk with ⟨ok', hk⟩ | ⟨f, hk⟩
  · simp only [Kind.wait.injEq] at hk; obtain ⟨hl, hq, -⟩ := hk
    obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
    simp only [Wg0.Control.D.words] at hsl hps hb h2; subst hsl hps
    obtain ⟨hcy, hf⟩ := by simpa only [loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff,
      true_and] using hl.trans (Wg0.sv_loc hp (slot2 (Wg0.rounds l0 l1 - 1)))
    have hj : j = slot2 (Wg0.rounds l0 l1 - 1) := MbarFam.svDone.inj (MbarFam.off_inj hf)
    subst hcy hj
    rw [ht, h2, hq, Wg0.parW_W (Nat.mod_lt _ (by decide)), hb]
    exact ⟨rfl, rfl, Nat.mod_mod _ _, le_rfl, hb0⟩
  · cases hk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
