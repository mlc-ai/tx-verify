-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Export.WarpRel
import Kernels.InklingRelDecode.Proof.Common.Roles
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.Block
import Kernels.InklingRelDecode.Proof.Common.BarPc
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.ClsBuild
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import all Kernels.InklingRelDecode.Proof.Common.Time

@[expose] public section

/-! # What follows a blocking event of the prologue

A blocking event of the prologue is followed by a state at no collective, except the five
barriers of each preload block, whose successors are the block's shuffle and elections. The
machine does not stop after them. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Frame

private theorem blk_sites : ∀ s : Prologue.Site, s ≠ .exit → s.pc ∈ Lib.blockPcs →
    s = .sMax ∨ s = .bar2 ∨ (∃ b j, s = .pb b j) ∨ s = .bar18 := by
  intro s
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem query_site (tid : Nat) (d : Prologue.Control.D) (n : Nat) :
    isWarpAt (Prologue.Control.querySite tid d n).pc = false := by
  unfold Prologue.Control.querySite
  repeat' split
  all_goals decide +kernel

private theorem next_block {Q L g} (d : Prologue.Control.D) (e : Event) (hx : d.site ≠ .exit)
    (hb : d.site.pc ∈ Lib.blockPcs) :
    ∃ d', Prologue.Control.next Q L g d e = some (some d') ∧
      (isWarpAt d'.site.pc = true → (d.site.pc, d'.site.pc) ∈ Lib.pairs) := by
  rcases blk_sites _ hx hb with h | h | ⟨b, j, h⟩ | h <;> simp only [h, Prologue.Control.next]
  · exact ⟨_, rfl, by intro h; dsimp only at h ⊢; revert h; decide +kernel⟩
  · split
    · exact ⟨_, rfl, fun h => absurd h (by simp [query_site])⟩
    · exact ⟨_, rfl, by intro h; dsimp only at h ⊢; revert h; decide +kernel⟩
  · fin_cases b <;> fin_cases j <;> dsimp only
    all_goals first
      | exact ⟨_, rfl, by intro h; dsimp only at h ⊢; revert h; decide +kernel⟩
      | (split <;> exact ⟨_, rfl, by intro h; dsimp only at h ⊢; revert h; decide +kernel⟩)
  · exact ⟨_, rfl, by intro h; dsimp only at h ⊢; revert h; decide +kernel⟩


/-- The state before a blocking event of the prologue is a prologue state. -/
private theorem role_at {Q L m X g k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) {σ : (thread Q L g).D}
    (hs : stateAt (thread Q L) X g k = some (some σ)) (hk : k < (X.tr g).length)
    (inv : (thread Q L g).inv σ) (hr : 27 ≤ ((thread Q L g).pc σ) ∧ (thread Q L g).pc σ < 574) :
    ∃ w s n, σ = proState w s n := by
  by_cases h27 : (thread Q L g).pc σ = 27
  · obtain ⟨s0, n⟩ := σ
    rcases s0 with st | ⟨r, s⟩
    · exfalso
      simp [Code.gatedExit_none] at inv
      change st.site.pc = 27 at h27
      obtain ⟨site, tm, x, w⟩ := st
      cases site <;> simp [Startup.enterOf, Startup.Site.pc] at inv h27
    · rcases r with r | r
      · cases r with
        | prologue w =>
          rcases s with d | ⟨e, d | ⟨u, d⟩⟩
          · exact ⟨w, d, n, rfl⟩
          · exfalso
            have := d.site.pc_range
            change d.site.pc = 27 at h27
            rcases this with h' | h'
            · omega
            · rw [h'] at h27; revert h27; decide
          · exfalso
            have := d.site.pc_range
            change d.site.pc = 27 at h27
            omega
        | dispatch w x =>
          exfalso
          rcases s with ⟨d, i⟩ | ⟨r, d⟩
          · change d.pc = 27 at h27
            revert h27; cases d <;> decide
          · cases r <;> change d.site.pc = 27 at h27 <;> generalize d.site = z at h27 <;>
              revert h27 <;> cases z <;> repeat' first | decide +kernel | (rename_i j; revert j)
      · exact (no_stub hp hX hk.le hs).elim
  · exact (state_role σ).prologue (by omega) hr.2

public theorem block {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f) (nu : NoUbBefore X g k)
    (hr : 27 ≤ e.pc ∧ e.pc < 574) (hb : e.pc ∈ Lib.blockPcs) :
    Lib.BlockFacts (schedule Q L).code (CollAt Q L) X g k e := by
  obtain ⟨σ, hs, -⟩ := event_table hf hX hp he hu
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs hu
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have inv := (reached_table hf (Frame.lt_of_get hX he) nu hs).1
  obtain ⟨w, d, n, rfl⟩ := role_at hp hX hs hk inv (by rw [← pc]; exact hr)
  have hx : d.site ≠ .exit := fun h => by
    simp [dataExit, h] at inv
  have step := Frame.stateAt_succ (C := thread Q L) (X := X) (show (X.tr g)[k]? = some e from he)
  rw [hs] at step
  change e.pc = d.site.pc at pc
  obtain ⟨d', hd', hw⟩ := next_block (Q := Q) (L := L) (g := g) d e hx (pc ▸ hb)
  simp only [proState, thread, Code.roleThread, Code.counted, Code.toMachine, Code.glue, hd',
    Option.map_some, Option.bind_some] at step
  by_cases hxd : d'.site = .exit
  · have en := Code.enter_some (P := Control.checkedCode Q L g w) (R := fun e => softCode e L g)
      (exit := dataExit Q L g w) (d := d') (i := dataEntry Q L g w d') (by simp [dataExit, hxd])
    rw [en] at step
    exact Lib.BlockFacts.of_step hs (Lib.not_coll hb pc) step
      (fun h2 => absurd (collAt_iff_warp.mp h2)
          (by
            show ¬ isWarpAt (Softmax.Site.pc (({} : Softmax.Control.D).site)) = true
            decide +kernel))
  · have en : (Control.checkedCode Q L g w).enter (fun e => softCode e L g) (dataExit Q L g w) d' =
        .inl d' := Code.enter_none (by simp [dataExit, hxd])
    rw [en] at step
    exact Lib.BlockFacts.of_step hs (Lib.not_coll hb pc) step
      (fun h2 => pc ▸ hw (collAt_iff_warp.mp h2))


end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
