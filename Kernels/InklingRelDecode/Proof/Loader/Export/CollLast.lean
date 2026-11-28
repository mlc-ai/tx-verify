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

/-! # What follows a blocking event of the loader warp

A blocking event of the loader warp is followed by a state at no collective. The machine does
not stop after it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Flow PTX.Frame

private theorem mma_pc (s : Mma.Site) : ¬ (2344 ≤ s.pc ∧ s.pc < 2422) := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem blk_sites : ∀ s : Loader.Site, s ≠ .dispatch → s.pc ∈ Lib.blockPcs →
    s = .dec ∨ s = .beginBar ∨ s = .endBar ∨ s = .inc := by
  intro s
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem next_block {L g} (d : Loader.D) (e : Event) (hx : d.site ≠ .dispatch)
    (hb : d.site.pc ∈ Lib.blockPcs) :
    ∃ d', Loader.next L g d e = some (some d') ∧
      (isWarpAt d'.site.pc = true → (d.site.pc, d'.site.pc) ∈ Lib.pairs) := by
  rcases blk_sites _ hx hb with h | h | h | h <;> simp only [Loader.next, h]
  all_goals first
    | exact ⟨_, rfl, by intro h; dsimp only at h ⊢; revert h; decide +kernel⟩
    | (repeat' split
       all_goals exact ⟨_, rfl, by intro h; dsimp only at h ⊢; revert h; decide +kernel⟩)

/-- The state before the loader warp's first event is its initial state. -/
private theorem at2344 {Q L m X g k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) {σ : (thread Q L g).D}
    (hs : stateAt (thread Q L) X g k = some (some σ)) (hk : k < (X.tr g).length)
    (inv : (thread Q L g).inv σ) (h : (thread Q L g).pc σ = 2344) :
    ∃ w x r d n, σ = workerState w x (.loader r) d n ∧ d.site ≠ .dispatch := by
  obtain ⟨s0, n⟩ := σ
  rcases s0 with st | ⟨r, s⟩
  · exfalso
    simp [Code.gatedExit_none] at inv
    change st.site.pc = 2344 at h
    obtain ⟨site, tm, x, w⟩ := st
    cases site <;> simp [Startup.enterOf, Startup.Site.pc] at inv h
  · rcases r with r | r
    · cases r with
      | prologue w =>
        exfalso
        rcases s with d | ⟨e, d | ⟨u, d⟩⟩
        · have := d.site.pc_range
          change d.site.pc = 2344 at h
          omega
        · have := d.site.pc_range
          change d.site.pc = 2344 at h
          rcases this with h' | h'
          · omega
          · rw [h'] at h; revert h; decide
        · have := d.site.pc_range
          change d.site.pc = 2344 at h
          omega
      | dispatch w x =>
        rcases s with ⟨d, i⟩ | ⟨r, d⟩
        · exfalso
          have := inv
          simp [workerEntry] at this
          change d.pc = 2344 at h
          cases d <;> simp [Dispatch.Site.pc] at h this
        · cases r with
          | loader r =>
            refine ⟨w, x, r, d, n, rfl, fun hd => ?_⟩
            have := inv
            simp [workerBack, hd] at this
          | mma r =>
            exfalso
            change d.site.pc = 2344 at h
            generalize d.site = z at h
            revert h; cases z <;> repeat' first | decide +kernel | (rename_i j; revert j)
    · exact (no_stub hp hX hk.le hs).elim

public theorem block {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f) (nu : NoUbBefore X g k)
    (hr : 2344 ≤ e.pc ∧ e.pc < 2422) (hb : e.pc ∈ Lib.blockPcs) :
    Lib.BlockFacts (schedule Q L).code (CollAt Q L) X g k e := by
  obtain ⟨σ, hs, -⟩ := event_table hf hX hp he hu
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs hu
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have inv := (reached_table hf (Frame.lt_of_get hX he) nu hs).1
  have role : ∃ w x r d n, σ = workerState w x (.loader r) d n ∧ d.site ≠ .dispatch := by
    by_cases h : e.pc = 2344
    · exact at2344 hp hX hs hk inv (pc ▸ h)
    · obtain ⟨w, x, r, d, n, hs', hj⟩ := worker_event hp hX hf he hu (by omega) (by omega)
        (by omega)
      obtain rfl : σ = workerState w x r d n :=
        Option.some.inj (Option.some.inj (hs.symm.trans hs'))
      cases r with
      | mma r =>
        exfalso
        change e.pc = d.site.pc at pc
        exact mma_pc d.site (by rw [← pc]; exact ⟨hr.1, hr.2⟩)
      | loader r =>
        refine ⟨w, x, r, d, n, rfl, fun hd => ?_⟩
        have := inv
        simp [workerBack, hd] at this
  obtain ⟨w, x, r, d, n, rfl, hx⟩ := role
  have step := Frame.stateAt_succ (C := thread Q L) (X := X) (show (X.tr g)[k]? = some e from he)
  rw [hs] at step
  change e.pc = d.site.pc at pc
  obtain ⟨d', hd', hw'⟩ := next_block (L := L) (g := g) d e hx (pc ▸ hb)
  simp only [workerState, thread, Code.roleThread, Code.counted, Code.toMachine, Code.glue,
    workerCode, Code.loopGlue, workerFrag, workerBack, Code.backEnter, Code.withStubs, frag,
    Loader.code,
    hd', Option.map_some, Option.bind_some] at step
  by_cases hd : d'.site = .dispatch
  · simp only [hd, ↓reduceIte] at step
    have en : (Dispatch.code L g (startRegs Q L g w x) x 0).enter (workerFrag Q L g w x)
        workerEntry ⟨.head, r + 1⟩ = .inl ⟨.head, r + 1⟩ := Code.enter_none rfl
    rw [en] at step
    exact Lib.BlockFacts.of_step hs (Lib.not_coll hb pc) step
        (fun h2 => absurd (collAt_iff_warp.mp h2)
          (by show ¬ isWarpAt Dispatch.Site.head.pc = true; decide +kernel))
  · simp only [hd, ↓reduceIte] at step
    exact Lib.BlockFacts.of_step hs (Lib.not_coll hb pc) step
      (fun h2 => pc ▸ hw' (collAt_iff_warp.mp h2))

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export
