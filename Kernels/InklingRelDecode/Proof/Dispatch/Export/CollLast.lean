-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Export.WarpRel
import Kernels.InklingRelDecode.Proof.Common.Roles
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.Block
import Kernels.InklingRelDecode.Proof.Common.BarPc
import Kernels.InklingRelDecode.Proof.Common.WorkerBar
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.ClsBuild
import Kernels.InklingRelDecode.Proof.Common.DataOrdinal
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import all Kernels.InklingRelDecode.Proof.Common.Time

@[expose] public section

/-! # What follows a blocking event of the dispatch loop

A blocking event of the dispatch loop (the rendezvous of the idle rounds and of the exit) is
followed by a state at no collective. The machine does not stop after it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch.Export
open PTX PTX.Flow PTX.Frame

private theorem blk_sites : ∀ s : Dispatch.Site, s ≠ .loaderEntry → s ≠ .mmaEntry →
    s.pc ∈ Lib.blockPcs → s = .idleDec ∨ s = .idleSync ∨ s = .idleSyncAgain ∨ s = .idleInc ∨
      s = .head ∨ s = .sync ∨ s = .badSync ∨ s = .badSyncAgain ∨ s = .exitSync ∨
      s = .exitDealloc := by
  intro s
  cases s <;> decide +kernel

private theorem next_block {L g} (d : Dispatch.D) (e : Event) (h1 : d.site ≠ .loaderEntry)
    (h2 : d.site ≠ .mmaEntry) (hb : d.site.pc ∈ Lib.blockPcs) :
    ∃ d', Dispatch.next L g d e = some (some d') ∧ workerEntry d' = none ∧
      (isWarpAt d'.site.pc = true → (d.site.pc, d'.site.pc) ∈ Lib.pairs) := by
  rcases blk_sites _ h1 h2 hb with h | h | h | h | h | h | h | h | h | h <;>
    simp only [Dispatch.next, h]
  all_goals first
    | exact ⟨_, rfl, rfl, by intro h; dsimp only at h ⊢; revert h; decide +kernel⟩
    | (repeat' split
       all_goals exact ⟨_, rfl, rfl, by intro h; dsimp only at h ⊢; revert h; decide +kernel⟩)

/-- The state before a blocking event of the dispatch loop is a dispatch state. -/
private theorem at_dispatch {Q L m X g k p} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) {σ : (thread Q L g).D}
    (hs : stateAt (thread Q L) X g k = some (some σ)) (hk : k < (X.tr g).length)
    (inv : (thread Q L g).inv σ) (hpc : (thread Q L g).pc σ = p)
    (h : 2333 ≤ p ∧ p ≤ 2338 ∨ p = 2557 ∨ p = 2558 ∨ 2853 ≤ p ∧ p ≤ 2854) :
    ∃ (w : Value) (x : BitVec 64) (d : Dispatch.D) (n : Cls → Nat),
      σ = (.inr ⟨.inl (.dispatch w x), .inl d⟩, n) ∧ d.site ≠ .loaderEntry ∧
        d.site ≠ .mmaEntry := by
  obtain ⟨s0, n⟩ := σ
  rcases s0 with st | ⟨r, s⟩
  · exfalso
    simp [Code.gatedExit_none] at inv
    change st.site.pc = p at hpc
    subst hpc
    obtain ⟨site, tm, x, w⟩ := st
    cases site <;> simp [Startup.enterOf, Startup.Site.pc] at inv h
  · rcases r with r | r
    · cases r with
      | prologue w =>
        exfalso
        rcases s with d | ⟨e, d | ⟨u, d⟩⟩
        · have := d.site.pc_range
          change d.site.pc = p at hpc
          omega
        · have := d.site.pc_range
          change d.site.pc = p at hpc
          rcases this with h' | h'
          · omega
          · rw [h'] at hpc; change 2565 = p at hpc; omega
        · change d.site.pc = p at hpc
          subst hpc
          generalize d.site = z at h
          revert h; cases z <;> repeat' first | decide +kernel | (rename_i j; revert j)
      | dispatch w x =>
        rcases s with d | ⟨r, d⟩
        · refine ⟨w, x, d, n, rfl, fun hd => ?_, fun hd => ?_⟩
          all_goals simp [workerEntry, hd] at inv
        · exfalso
          cases r with
          | loader r =>
            have hd : d.site ≠ .dispatch := fun hd => by simp [workerBack, hd] at inv
            change d.site.pc = p at hpc
            subst hpc
            generalize d.site = z at h hd
            revert h hd; cases z <;> repeat' first | decide +kernel | (rename_i j; revert j)
          | mma r =>
            have hd : d.site ≠ .dispatch := fun hd => by simp [workerBack, hd] at inv
            change d.site.pc = p at hpc
            subst hpc
            generalize d.site = z at h hd
            revert h hd; cases z <;> repeat' first | decide +kernel | (rename_i j; revert j)
    · exact (no_stub hp hX hk.le hs).elim

public theorem block {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f) (nu : NoUbBefore X g k)
    (hr : 2333 ≤ e.pc ∧ e.pc ≤ 2338 ∨ e.pc = 2557 ∨ e.pc = 2558 ∨ 2853 ≤ e.pc ∧ e.pc ≤ 2854)
    (hb : e.pc ∈ Lib.blockPcs) :
    Lib.BlockFacts (schedule Q L).code (CollAt Q L) X g k e := by
  obtain ⟨σ, hs, -⟩ := event_table hf hX hp he hu
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs hu
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have inv := (reached_table hf (Frame.lt_of_get hX he) nu hs).1
  obtain ⟨w, x, d, n, rfl, h1, h2⟩ := at_dispatch hp hX hs hk inv pc.symm hr
  have step := Frame.stateAt_succ (C := thread Q L) (X := X) (show (X.tr g)[k]? = some e from he)
  rw [hs] at step
  change e.pc = d.site.pc at pc
  obtain ⟨d', hd', hen, hw'⟩ := next_block (L := L) (g := g) d e h1 h2 (pc ▸ hb)
  simp only [thread, Code.roleThread, Code.counted, Code.toMachine, Code.glue, hd',
    Option.map_some, Option.bind_some] at step
  have en : (Dispatch.code L g (startRegs Q L g w x) x 0).enter (workerFrag Q L g w x) workerEntry
      d' = .inl d' := Code.enter_none hen
  rw [en] at step
  exact Lib.BlockFacts.of_step hs (Lib.not_coll hb pc) step
    (fun h2 => pc ▸ hw' (collAt_iff_warp.mp h2))

end PTX.Kernels.InklingRelDecode.Proof.Dispatch.Export
