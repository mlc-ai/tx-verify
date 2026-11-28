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

/-! # What follows a blocking event of the Softmax

A blocking event of the Softmax is followed by a state at no collective, except the wait for the
S tile's load (pc 1298) and the barrier at pc 2241, which precede shuffles. The machine does not
stop after them. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Frame

private theorem blk_sites : ∀ s : Softmax.Site, s ≠ .epilogue → s.pc ∈ Lib.blockPcs →
    s = .setMaxReg ∨ s = .bar0 ∨ s = .ldS ∨ s = .waitLd ∨ s = .bar22 ∨ s = .bar23 ∨ s = .ldO ∨
    s = .waitLdO ∨ s = .bar24 ∨ s = .stO ∨ s = .waitStO ∨ s = .bar20 ∨ s = .tmemSt ∨
    s = .tmemWait ∨ s = .bar21 := by
  intro s
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem next_block {ent L g} (d : Softmax.Control.D) (ev : Event) (hx : d.site ≠ .epilogue)
    (hb : d.site.pc ∈ Lib.blockPcs) :
    ∃ d', Softmax.Control.next ent L g d ev = some (some d') ∧
      (isWarpAt d'.site.pc = true → (d.site.pc, d'.site.pc) ∈ Lib.pairs) := by
  rcases blk_sites _ hx hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp only [Softmax.Control.next, h]
  all_goals first
    | exact ⟨_, rfl, by intro h; dsimp only at h ⊢; revert h; decide +kernel⟩
    | (simp only [Softmax.Control.loopSite, Softmax.Control.advance]
       repeat' split
       all_goals exact ⟨_, rfl, by intro h; dsimp only at h ⊢; revert h; decide +kernel⟩)

/-- The state before a blocking event of the Softmax is a Softmax state. -/
private theorem role_at {Q L m X g k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) {σ : (thread Q L g).D}
    (hs : stateAt (thread Q L) X g k = some (some σ)) (hk : k < (X.tr g).length)
    (inv : (thread Q L g).inv σ) (hr : 574 ≤ (thread Q L g).pc σ ∧ (thread Q L g).pc σ < 2331) :
    ∃ w e s n, σ = softState w e s n := by
  by_cases h574 : (thread Q L g).pc σ = 574
  · obtain ⟨s0, n⟩ := σ
    rcases s0 with st | ⟨r, s⟩
    · exfalso
      change st.site.pc = 574 at h574
      obtain ⟨site, tm, x, w⟩ := st
      dsimp only at h574
      cases site
      case enter r => cases r <;> exact absurd h574 (by decide)
      all_goals exact absurd h574 (by decide)
    · rcases r with r | r
      · cases r with
        | prologue w =>
          rcases s with d | ⟨e, d | ⟨u, d⟩⟩
          · exfalso
            have hx : d.site ≠ .exit := fun h => by
              simp [dataExit, h] at inv
            change d.site.pc = 574 at h574
            generalize d.site = z at h574 hx
            revert h574 hx
            cases z <;> repeat' first | decide +kernel | (rename_i j; revert j)
          · exact ⟨w, e, d, n, rfl⟩
          · exfalso
            have := d.site.pc_range
            change d.site.pc = 574 at h574
            omega
        | dispatch w x =>
          exfalso
          rcases s with ⟨d, i⟩ | ⟨r, d⟩
          · change d.pc = 574 at h574
            revert h574; cases d <;> decide
          · cases r <;> change d.site.pc = 574 at h574 <;> generalize d.site = z at h574 <;>
              revert h574 <;> cases z <;> repeat' first | decide +kernel | (rename_i j; revert j)
      · exact (no_stub hp hX hk.le hs).elim
  · exact (state_role σ).softmax (by omega) hr.2

public theorem block {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f) (nu : NoUbBefore X g k)
    (hr : 574 ≤ e.pc ∧ e.pc < 2331) (hb : e.pc ∈ Lib.blockPcs) :
    Lib.BlockFacts (schedule Q L).code (CollAt Q L) X g k e := by
  obtain ⟨σ, hs, -⟩ := event_table hf hX hp he hu
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs hu
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have inv := (reached_table hf (Frame.lt_of_get hX he) nu hs).1
  obtain ⟨w, ent, d, n, rfl⟩ := role_at hp hX hs hk inv (by rw [← pc]; exact hr)
  have hx : d.site ≠ .epilogue := fun h => by
    simp [epiExit, h] at inv
  have step := Frame.stateAt_succ (C := thread Q L) (X := X) (show (X.tr g)[k]? = some e from he)
  rw [hs] at step
  change e.pc = d.site.pc at pc
  obtain ⟨d', hd', hw⟩ := next_block (ent := ent) (L := L) (g := g) d e hx (pc ▸ hb)
  simp only [softState, thread, Code.roleThread, Code.counted, Code.toMachine, Code.glue, hd',
    Option.map_some, Option.bind_some] at step
  by_cases hxd : d'.site = .epilogue
  · have en := Code.enter_some (P := Control.code ent L g)
      (R := fun _ : Unit => Epilogue.Control.code (epiEntry ent (g % L.block)) L g)
      (exit := epiExit) (d := d') (i := ()) (by simp [epiExit, hxd])
    rw [en] at step
    exact Lib.BlockFacts.of_step hs (Lib.not_coll hb pc) step
      (fun h2 => absurd (collAt_iff_warp.mp h2)
          (by
            show ¬ isWarpAt (Epilogue.Site.pc (({} : Epilogue.Control.D).site)) = true
            decide +kernel))
  · have en : (Control.code ent L g).enter
        (fun _ : Unit => Epilogue.Control.code (epiEntry ent (g % L.block)) L g) epiExit d' =
        .inl d' := Code.enter_none (by simp [epiExit, hxd])
    rw [en] at step
    exact Lib.BlockFacts.of_step hs (Lib.not_coll hb pc) step
      (fun h2 => pc ▸ hw (collAt_iff_warp.mp h2))

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
