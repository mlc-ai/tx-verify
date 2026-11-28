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
import Kernels.InklingRelDecode.Proof.Common.DataOrdinal
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import all Kernels.InklingRelDecode.Proof.Common.Time

@[expose] public section

/-! # What follows a blocking event of the epilogue

A blocking event of the epilogue is followed by a state at no collective. The machine does not
stop after it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
open PTX PTX.Flow PTX.Frame

private theorem blk_sites : ∀ s : Epilogue.Site, s.pc ∈ Lib.blockPcs →
    s = .load ∨ s = .waitLd ∨ s = .join ∨ s = .setMax ∨ s = .sync1 ∨ s = .sync0 ∨ s = .dealloc := by
  intro s
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem next_block {ent : Epilogue.Control.Entry} {L g} (d : Epilogue.Control.D)
    (ev : Event)
    (hb : d.site.pc ∈ Lib.blockPcs) :
    ∃ d', Epilogue.Control.next ent L g d ev = some (some d') ∧
      (isWarpAt d'.site.pc = true → (d.site.pc, d'.site.pc) ∈ Lib.pairs) := by
  rcases blk_sites _ hb with h | h | h | h | h | h | h <;> simp only [Epilogue.Control.next, h]
  all_goals first
    | exact ⟨_, rfl, by intro h; dsimp only at h ⊢; revert h; decide +kernel⟩
    | (try simp only [Epilogue.Control.firstStore]
       repeat' split
       all_goals exact ⟨_, rfl, by intro h; dsimp only at h ⊢; revert h; decide +kernel⟩)

public theorem block {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f) (nu : NoUbBefore X g k)
    (hr : 2565 ≤ e.pc ∧ e.pc < 2853) (hb : e.pc ∈ Lib.blockPcs) :
    Lib.BlockFacts (schedule Q L).code (CollAt Q L) X g k e := by
  obtain ⟨σ, hs, -⟩ := event_table hf hX hp he hu
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs hu
  have inv := (reached_table hf (Frame.lt_of_get hX he) nu hs).1
  obtain ⟨w, ent, d, n, rfl⟩ := (state_role σ).epilogue (by omega) (by omega) inv
  have step := Frame.stateAt_succ (C := thread Q L) (X := X) (show (X.tr g)[k]? = some e from he)
  rw [hs] at step
  change e.pc = d.site.pc at pc
  obtain ⟨d', hd', hw⟩ := next_block (ent := epiEntry ent (g % L.block)) (L := L) (g := g) d e
    (pc ▸ hb)
  simp only [epiState, thread, Code.roleThread, Code.counted, Code.toMachine, Code.glue, hd',
    Option.map_some, Option.bind_some] at step
  exact Lib.BlockFacts.of_step hs (Lib.not_coll hb pc) step
    (fun h2 => pc ▸ hw (collAt_iff_warp.mp h2))

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
