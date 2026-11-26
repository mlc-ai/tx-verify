-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarInit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Lemmas.Kernel.Progress.NextEv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Next
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Recv
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WfStep

@[expose] public section

/-! # The exports of every role, by role: the progress rows

The one place where a trace-level statement is assembled from the roles' states by a case split
on the thread machine's state. Each role has two progress rows (`lane-rules`, rule 2), the only
way the progress classes see a waiting lane:

* **next-event row** `<role>_next`: under `Follow`, a next event of a lane of the role (no
  undefined behaviour) is classified by its pc. The role is identified by the next event's pc
  region (the regions are disjoint, `Common/Sites.lean`); a prefix-count hypothesis is added only
  where the pc does not determine the class. The event is classified: a wait on a named object
  and parity, an issue that continues, or `exit`. It is stated for every next event; the
  existence of one comes from the released lane at the use site (`Descent.next_classUQ`,
  `Sched.wait_site_stepsUN`);
* **wait-step row** `<role>_wait`: a pending released lane whose next event is a failed poll of
  `⟨pc, .wait l q false true sc⟩` steps (`Sched.Steps (timed P L)`), given the channel's blocker
  (`Sched.WaitBlk`); proved here with `Sched.wait_site_stepsUN` and the state taken privately
  (`next_state`, `Common/View.lean`).

**Recipe for a role lane's two rows** (`mma_next`, `mma_wait` are the model):
1. in the role, prove `ev_class` (its next events classified by pc, from `Ref` and `Ev`),
   `wait_op` (each poll site's instruction is a wait), `evK_wait_site` and `evK_wait_det` (the
   shape table fixes a poll's object and parity), as `Mma/{Class,Poll}.lean`;
2. add the role's time and measure slots (`Common/{Time,Measure}.lean`, from `<Role>/{Time,
   Measure}.lean`) so that `time_ge` holds for its states;
3. `<role>_next`: `next_<role>`-style state (`next_state` + `<role>_state`), then `ev_class`;
4. `<role>_wait`: `role_wait` with `<role>_state` and the two poll facts (five lines, as
   `mma_wait`);
5. add both rows to `Common/Export/Next.lean`'s per-role bundle.

The startup and warpgroup 1's head and idle code poll no mbarrier, so their wait-step rows hold
because no such next event exists. A role lane adds its two rows here the same way (the
coordinator lands them); `Protocol/` and `Top/` import this file and the roles' export files,
never a role's internals. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {e : Event}

/-! ### The startup (pcs below 103) -/

/-- **Startup, next-event row**: a next event below pc 103 is at a pc up to `97`, polls no
mbarrier and is no `exit`; at pc 97 it is `bar.sync 0`. -/
theorem startup_next (hp : Pre P L m) (hFw : Follow P L X)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f)
    (hpc0 : e.pc < 103) :
    e.pc ≤ 97 ∧ (∀ l q ok b sc, e.kind ≠ .wait l q ok b sc) ∧ e.kind ≠ .exit ∧
      (e.pc = 97 → e.kind = .bar 0 none .sync) := by
  obtain ⟨σ, -, hJ, hi, hev, hpc⟩ := next_state hp hFw hn hub
  obtain ⟨d, n, rfl, -, -, hev, hx, hpc'⟩ := startup_state hJ hi hev hpc hpc0
  obtain ⟨hw, hex, hbar⟩ := Startup.ev_quiet hev hx
  have hne : ∀ r, d.site ≠ .enter r := fun r hr => by simp [Startup.exitOf, hr] at hx
  have hle := Startup.Site.pc_le d.site hne
  exact ⟨by omega, hw, hex, fun h97 => hbar (Startup.Site.eq_bar hne (by omega))⟩

/-- **Startup, wait-step row**: vacuous, the startup polls no mbarrier. -/
theorem startup_wait (hp : Pre P L m) (hFw : Follow P L X) (_hpd : Frame.Pending L X g)
    (_hrel : Step.Released L X g) {pc : Nat} {l : Loc} {q : Nat} {sc : MbarScope}
    (hpc0 : pc < 103)
    (hn : Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q false true sc⟩)
    (_hblk : Sched.WaitBlk (timed P L) X g l q) : Sched.Steps (timed P L) m X (.thread g) := by
  obtain ⟨-, hw, -⟩ := startup_next hp hFw hn (fun f h => by cases h) hpc0
  exact absurd rfl (hw l q false true sc)

/-! ### Warpgroup 1's head (pcs 1842, 1843) and idle code (pcs 2596, 2601, 2604) -/

/-! ### The MMA warp (pcs 1853–2160) -/

/-- **MMA warp, next-event row**: a next event at a pc of the MMA code is a poll of `bar_q_tma`
(pc 1931) or `bar_q_utccp` (pc 1983) with parity 0, of a stage of `dequantReady` (pc 2012) or
`soReady` (pc 2107) of the lane's CTA, or neither a poll nor an exit. -/
theorem mma_next (hp : Pre P L m) (hFw : Follow P L X)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f)
    (hpc0 : 1853 ≤ e.pc ∧ e.pc ≤ 2160) :
    (e.pc = 1931 ∧ ∃ ok, e.kind = .wait (MbarRow.loc L g .qTma) 0 ok true .cta) ∨
      (e.pc = 1983 ∧ ∃ ok, e.kind = .wait (MbarRow.loc L g .qUtccp) 0 ok true .cta) ∨
      (e.pc = 2012 ∧ ∃ b q ok,
        e.kind = .wait (MbarRow.loc L g (.dequantReady b)) q ok true .cta) ∨
      (e.pc = 2107 ∧ ∃ b q ok, e.kind = .wait (MbarRow.loc L g (.soReady b)) q ok true .cta) ∨
      ((∀ l q ok a sc, e.kind ≠ .wait l q ok a sc) ∧ e.kind ≠ .exit) := by
  obtain ⟨d, hR, hev, hl, hu⟩ := next_mma hp hFw hn hub ⟨by omega, by omega⟩
  exact Mma.ev_class hp hR hu hl hev hub hpc0.2

/-- **The wait-step row of any role**: a pending released lane whose next event is a failed
poll steps, given the poll's blocker and the role's two facts at the state behind the poll (taken
privately here): the instruction at its pc is a wait, and its shape table determines the polled
object and parity. The time bound is the glued table's (`time_ge`). -/
private theorem role_wait (hp : Pre P L m) (hFw : Follow P L X)
    (hmax : Maximal L kernel Assumptions.all m X) (hnu : ¬ HasUb X) (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g) {pc : Nat} {l : Loc} {q : Nat} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q false true sc⟩)
    (hblk : Sched.WaitBlk (timed P L) X g l q)
    (hrole : ∀ σ, (table P L).J g σ → (thread P L g).inv σ →
      (table P L).Ev g σ ⟨pc, .wait l q false true sc⟩ → pc = (thread P L g).pc σ →
      σ ≠ (thread P L g).init ∧
      (∀ ins, kernel.code[(thread P L g).pc σ]? = some ins → Sched.waitOp ins.op = true) ∧
        ∀ l' q' ok sc', (table P L).Ev g σ ⟨(thread P L g).pc σ, .wait l' q' ok true sc'⟩ →
          l' = l ∧ q' = q) :
    Sched.Steps (timed P L) m X (.thread g) := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := next_state hp hFw hn (fun f h => by cases h)
  obtain ⟨hin, hop, hdet⟩ := hrole σ hJ hi hev hpc
  have hne : X.tr g ≠ [] := by
    intro h0
    rw [h0, List.length_nil, Frame.stateAt_zero] at hσ
    exact hin (Option.some.inj (Option.some.inj hσ)).symm
  rw [timed_eq] at hblk ⊢
  refine Sched.wait_site_stepsUN (M := ⟨thread P L, time P L⟩) wfQuiet_all hmax hnu
    (fun _ _ => thread_sound hp) hpd hσ hne hrel hop
    (P := (table P L).Ev g _) (fun hat hi' hc hf _ =>
      (shapeOk hp (fun _ => True)).shape g trivial _ _ _ _ _ hJ hat hi' hc hf)
    (fun l' q' ok sc' hP => ?_) (fun l' q' sc' hP _ => ?_) (time_ge P L g σ)
  · obtain ⟨hl', -⟩ := hdet l' q' ok sc' hP
    obtain ⟨before, hb, -⟩ := hblk
    exact ⟨before, hl' ▸ hb⟩
  · obtain ⟨hl', hq'⟩ := hdet l' q' false sc' hP
    subst hl' hq'
    exact hblk

/-- **MMA warp, wait-step row**: a pending released lane whose next event is a failed poll at a
pc of the MMA code steps, given the poll's blocker. -/
theorem mma_wait (hp : Pre P L m) (hFw : Follow P L X)
    (hmax : Maximal L kernel Assumptions.all m X) (hnu : ¬ HasUb X) (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g) {pc : Nat} {l : Loc} {q : Nat} {sc : MbarScope}
    (hpc0 : 1853 ≤ pc ∧ pc ≤ 2160)
    (hn : Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q false true sc⟩)
    (hblk : Sched.WaitBlk (timed P L) X g l q) : Sched.Steps (timed P L) m X (.thread g) :=
  role_wait hp hFw hmax hnu hpd hrel hn hblk fun σ hJ hi hev hpc => by
    obtain ⟨d, n, rfl, -, hE, hl, -⟩ := mma_state hJ hi hev hpc ⟨by simp only; omega,
      by simp only; omega⟩
    exact ⟨(fun h => by cases h), Mma.wait_op (Mma.evK_wait_site hl hE.2 rfl),
      fun l' q' ok sc' hP => Mma.evK_wait_det hl hE.2 hP.2 rfl rfl⟩

/-! ### The TMA warp (pcs 2162–2331, `MbarRow.TmaAt`) -/

/-- **TMA warp, next-event row**: a next event at a pc of the TMA code is a poll of `bar_q_utccp`
(pc 2205) or `bar_last_store_done` (pc 2209) with parity 0, of a slot of `coordReady` (pc 2234)
or `rawFree` (pc 2245) of the lane's CTA, or neither a poll nor an exit. -/
theorem tma_next (hp : Pre P L m) (hFw : Follow P L X)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f)
    (hpc0 : 2162 ≤ e.pc ∧ e.pc < 2332) :
    (e.pc = 2205 ∧ ∃ ok, e.kind = .wait (MbarRow.loc L g .qUtccp) 0 ok true .cta) ∨
      (e.pc = 2209 ∧ ∃ ok, e.kind = .wait (MbarRow.loc L g .lastStoreDone) 0 ok true .cta) ∨
      (e.pc = 2234 ∧ ∃ b q ok,
        e.kind = .wait (MbarRow.loc L g (.coordReady b)) q ok true .cta) ∨
      (e.pc = 2245 ∧ ∃ b q ok, e.kind = .wait (MbarRow.loc L g (.rawFree b)) q ok true .cta) ∨
      ((∀ l q ok a sc, e.kind ≠ .wait l q ok a sc) ∧ e.kind ≠ .exit) := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := next_state hp hFw hn hub
  obtain ⟨d, n, rfl, hR, -, hE, hl, -⟩ := tma_state hJ hi hev hpc hpc0
  have hu : n (.tma .ub) = 0 := by
    obtain ⟨Y, hY, hpre, he⟩ := hn
    have h0 := lane5_take_noUb hY he
    rw [hpre] at h0
    exact (state_count hσ (.tma .ub)).trans (by rw [List.take_length]; exact h0)
  exact Tma.ev_class hp (hR (next_ub hn hσ)) hu hl hE hub hpc0.2

/-- **TMA warp, wait-step row**: a pending released lane whose next event is a failed poll at a
pc of the TMA code steps, given the poll's blocker. -/
theorem tma_wait (hp : Pre P L m) (hFw : Follow P L X)
    (hmax : Maximal L kernel Assumptions.all m X) (hnu : ¬ HasUb X) (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g) {pc : Nat} {l : Loc} {q : Nat} {sc : MbarScope}
    (hpc0 : 2162 ≤ pc ∧ pc < 2332)
    (hn : Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q false true sc⟩)
    (hblk : Sched.WaitBlk (timed P L) X g l q) : Sched.Steps (timed P L) m X (.thread g) :=
  role_wait hp hFw hmax hnu hpd hrel hn hblk fun σ hJ hi hev hpc => by
    obtain ⟨d, n, rfl, -, -, hE, hl, -⟩ := tma_state hJ hi hev hpc ⟨by simp only; omega,
      by simp only; omega⟩
    exact ⟨(fun h => by cases h), Tma.wait_op (Tma.evK_wait_site hl hE.2 rfl),
      fun l' q' ok sc' hP => Tma.evK_wait_det hl hE.2 hP.2 rfl rfl⟩

/-! ### The index warp (pcs 2332–2586, `MbarRow.IndexAt`) -/

/-- **Index warp, next-event row**: a next event at a pc of the index code is a poll of a slot of
`valid_coord_free` of the lane's CTA (pc 2446 in the main loop, 2534 in the extra loop), named
barrier 12 (pc 2585), or neither a poll nor an exit. -/
theorem index_next (hp : Pre P L m) (hFw : Follow P L X)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f)
    (hpc0 : 2332 ≤ e.pc ∧ e.pc < 2587) :
    (e.pc = 2446 ∧ ∃ b q ok,
        e.kind = .wait (MbarRow.loc L g (.coordFree b)) q ok true .cta) ∨
      (e.pc = 2534 ∧ ∃ b q ok,
        e.kind = .wait (MbarRow.loc L g (.coordFree b)) q ok true .cta) ∨
      (e.pc = 2585 ∧ e.kind = .bar 12 none .sync) ∨
      ((∀ l q ok a sc, e.kind ≠ .wait l q ok a sc) ∧ e.kind ≠ .exit) := by
  obtain ⟨σ, -, hJ, hi, hev, hpc⟩ := next_state hp hFw hn hub
  obtain ⟨d, n, rfl, -, hE, -⟩ := index_state hJ hi hev hpc hpc0
  exact Index.ev_class hp hE hub hpc0.2

/-- **Index warp, wait-step row**: a pending released lane whose next event is a failed poll at a
pc of the index code steps, given the poll's blocker. -/
theorem index_wait (hp : Pre P L m) (hFw : Follow P L X)
    (hmax : Maximal L kernel Assumptions.all m X) (hnu : ¬ HasUb X) (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g) {pc : Nat} {l : Loc} {q : Nat} {sc : MbarScope}
    (hpc0 : 2332 ≤ pc ∧ pc < 2587)
    (hn : Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q false true sc⟩)
    (hblk : Sched.WaitBlk (timed P L) X g l q) : Sched.Steps (timed P L) m X (.thread g) :=
  role_wait hp hFw hmax hnu hpd hrel hn hblk fun σ hJ hi hev hpc => by
    obtain ⟨d, n, rfl, -, hE, -⟩ := index_state hJ hi hev hpc ⟨by simp only; omega,
      by simp only; omega⟩
    exact ⟨(fun h => by cases h), Index.wait_op (Index.evK_wait_site hE.2 rfl),
      fun l' q' ok sc' hP => Index.evK_wait_det hE.2 hP.2 rfl rfl⟩

/-! ### Warpgroup 2 (pcs 2606–3610) -/

/-- **Warpgroup 2, next-event row**: a next event at a pc of warpgroup 2's code is a poll of
`bar_q_utccp` with parity 0 (pc 2644), of a slot's `rawReady` (pc 2677) or `svDone` (pc 2684) of
the lane's CTA, named barrier 12 (pc 3610), or neither a poll nor an exit. -/
theorem dequant_next (hp : Pre P L m) (hFw : Follow P L X)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f)
    (hpc0 : 2606 ≤ e.pc ∧ e.pc ≤ 3610) :
    (e.pc = 2644 ∧ ∃ ok, e.kind = .wait (MbarRow.loc L g .qUtccp) 0 ok true .cta) ∨
      (e.pc = 2677 ∧ ∃ b q ok,
        e.kind = .wait (MbarRow.loc L g (.rawReady b)) q ok true .cta) ∨
      (e.pc = 2684 ∧ ∃ b q ok, e.kind = .wait (MbarRow.loc L g (.svDone b)) q ok true .cta) ∨
      (e.pc = 3610 ∧ e.kind = .bar 12 none .sync) ∨
      ((∀ l q ok a sc, e.kind ≠ .wait l q ok a sc) ∧ e.kind ≠ .exit) := by
  obtain ⟨σ, -, hJ, hi, hev, hpc⟩ := next_state hp hFw hn hub
  obtain ⟨d, n, rfl, -, hE, -⟩ := dequant_state hp hJ hi hev hpc ⟨hpc0.1, by omega⟩
  exact Dequant.ev_class hp hE hub hpc0.2

/-- **Warpgroup 2, wait-step row**: a pending released lane whose next event is a failed poll at a
pc of warpgroup 2's code steps, given the poll's blocker. -/
theorem dequant_wait (hp : Pre P L m) (hFw : Follow P L X)
    (hmax : Maximal L kernel Assumptions.all m X) (hnu : ¬ HasUb X) (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g) {pc : Nat} {l : Loc} {q : Nat} {sc : MbarScope}
    (hpc0 : 2606 ≤ pc ∧ pc ≤ 3610)
    (hn : Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q false true sc⟩)
    (hblk : Sched.WaitBlk (timed P L) X g l q) : Sched.Steps (timed P L) m X (.thread g) :=
  role_wait hp hFw hmax hnu hpd hrel hn hblk fun σ hJ hi hev hpc => by
    obtain ⟨d, n, rfl, -, hE, -⟩ := dequant_state hp hJ hi hev hpc ⟨by simp only; omega,
      by simp only; omega⟩
    exact ⟨(fun h => by cases h), Dequant.wait_op (Dequant.evK_wait_site hE.2 rfl),
      fun l' q' ok sc' hP => Dequant.evK_wait_det hE.2 hP.2 rfl rfl⟩

/-- **The TMA warp's wait-step row in the bundle's form** (`WaitRows.tma`). -/
theorem tma_waitRow (hp : Pre P L m) (hFw : Follow P L X) :
    NextRow.Wait P L m X (MbarRow.TmaAt L) := fun hs hmax _ _ _ _ _ hpd hrel hat hn hblk => by
  obtain ⟨-, hlo, hhi⟩ := hat
  exact tma_wait hp hFw hmax (Sched.safe_noUb (hs.2 X hmax.1)) hpd hrel ⟨hlo, hhi⟩ hn hblk

/-- **The index warp's wait-step row in the bundle's form** (`WaitRows.index`). -/
theorem index_waitRow (hp : Pre P L m) (hFw : Follow P L X) :
    NextRow.Wait P L m X (MbarRow.IndexAt L) := fun hs hmax _ _ _ _ _ hpd hrel hat hn hblk => by
  obtain ⟨-, hlo, hhi⟩ := hat
  exact index_wait hp hFw hmax (Sched.safe_noUb (hs.2 X hmax.1)) hpd hrel ⟨hlo, hhi⟩ hn hblk

/-- **Warpgroup 2's wait-step row in the bundle's form** (`WaitRows.dequant`). -/
theorem dequant_waitRow (hp : Pre P L m) (hFw : Follow P L X) :
    NextRow.Wait P L m X (MbarRow.DequantAt L) := fun hs hmax _ _ _ _ _ hpd hrel hat hn hblk => by
  obtain ⟨-, -, hlo, hhi⟩ := hat
  exact dequant_wait hp hFw hmax (Sched.safe_noUb (hs.2 X hmax.1)) hpd hrel ⟨hlo, by omega⟩ hn
    hblk


/-! ### Warpgroup 0 (pcs 103–1841) -/

/-- **Warpgroup 0, next-event row**: a next event at a pc of warpgroup 0's code is a poll of the
valid-mask slot `coordReady (slot4 (polls4 … coordReady es))` (pc 264) or of the score slot
`qkDone (slot2 (polls2 … qkDone es))` (pc 272), each with the parity of the lane's successful polls
of it, of the last block's `svDone (slot2 (b - 1))` with parity `(b - 1) / 2 % 2` (pc 1184, `b`
the blocks `polls2 … qkDone es`), or neither a poll nor an exit; `es` is the lane's trace. -/
theorem wg0_next (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hn : Sched.NextEv L kernel Assumptions.all m X g e)
    (hub : ∀ f, e.kind ≠ .ub f) (hpc0 : 103 ≤ e.pc ∧ e.pc < 1842) :
    (e.pc = 264 ∧ MbarRow.Wait e
        (MbarRow.loc L g (.coordReady (MbarRow.slot4 (MbarRow.polls4 L g .coordReady (X.tr g)))))
        (okPolls (MbarRow.loc L g
          (.coordReady (MbarRow.slot4 (MbarRow.polls4 L g .coordReady (X.tr g))))) (X.tr g) % 2)) ∨
      (e.pc = 272 ∧ MbarRow.Wait e
        (MbarRow.loc L g (.qkDone (MbarRow.slot2 (MbarRow.polls2 L g .qkDone (X.tr g)))))
        (okPolls (MbarRow.loc L g
          (.qkDone (MbarRow.slot2 (MbarRow.polls2 L g .qkDone (X.tr g))))) (X.tr g) % 2)) ∨
      (e.pc = 1184 ∧ MbarRow.Wait e
        (MbarRow.loc L g (.svDone (MbarRow.slot2 (MbarRow.polls2 L g .qkDone (X.tr g) - 1))))
        ((MbarRow.polls2 L g .qkDone (X.tr g) - 1) / 2 % 2)) ∨
      ((∀ l q ok a sc, e.kind ≠ .wait l q ok a sc) ∧ e.kind ≠ .exit) := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := next_state hp hFw hn hub
  obtain ⟨d, n, rfl, hR, hE, hw⟩ := wg0_state hJ hi hev hpc hpc0
  obtain ⟨Y, hY, hpre, he⟩ := hn
  have hσY : Frame.stateAt (thread P L) Y g (X.tr g).length = some (some (_, n)) :=
    (Sched.stateAt_congr (by rw [hpre, List.take_length])).trans hσ
  have hc : ∀ c, n (.wg0 c) = (X.tr g).countP (Wg0.cls c) := fun c =>
    (state_count hσ (.wg0 c)).trans (by rw [List.take_length]; rfl)
  have hu : n (.wg0 .ub) = 0 := by
    rw [hc, ← hpre]
    exact wg0_take_noUb hY he
  refine Wg0.ev_class hp (hR (state_ub hY hσY he)) hu (fun l => ?_) hE hub hpc0.2
  have h := wg0_okPolls hp hX hFw hw (X.tr g).length l
  rw [List.take_length] at h
  rw [h, hc]

/-- **Warpgroup 0, wait-step row**: a pending released lane whose next event is a failed poll at a
pc of warpgroup 0's code steps, given the poll's blocker. -/
theorem wg0_wait (hp : Pre P L m) (hFw : Follow P L X)
    (hmax : Maximal L kernel Assumptions.all m X) (hnu : ¬ HasUb X) (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g) {pc : Nat} {l : Loc} {q : Nat} {sc : MbarScope}
    (hpc0 : 103 ≤ pc ∧ pc < 1842)
    (hn : Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q false true sc⟩)
    (hblk : Sched.WaitBlk (timed P L) X g l q) : Sched.Steps (timed P L) m X (.thread g) :=
  role_wait hp hFw hmax hnu hpd hrel hn hblk fun σ hJ hi hev hpc => by
    obtain ⟨d, n, rfl, -, hE, -⟩ := wg0_state hJ hi hev hpc ⟨by simp only; omega,
      by simp only; omega⟩
    exact ⟨(fun h => by cases h), Wg0.wait_op (Wg0.evK_wait_site hE.2 rfl),
      fun l' q' ok sc' hP => Wg0.evK_wait_det hE.2 hP.2 rfl rfl⟩

/-- **Warpgroup 0's wait-step row in the bundle's form** (`WaitRows.wg0`). -/
theorem wg0_waitRow (hp : Pre P L m) (hFw : Follow P L X) :
    NextRow.Wait P L m X (MbarRow.Wg0At L) := fun hs hmax _ _ _ _ _ hpd hrel hat hn hblk => by
  obtain ⟨-, hlo, hhi⟩ := hat
  exact wg0_wait hp hFw hmax (Sched.safe_noUb (hs.2 X hmax.1)) hpd hrel ⟨hlo, hhi⟩ hn hblk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
