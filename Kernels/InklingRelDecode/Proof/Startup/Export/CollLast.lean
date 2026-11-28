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
import all Kernels.InklingRelDecode.Proof.Common.Time

@[expose] public section

/-! # What follows a blocking event of the startup

A blocking event of the startup is followed by a state at no collective, except the barrier at
pc 14 and the relinquish at pc 15, which precede the shuffle at pc 17. The machine does not stop
after them. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Startup.Export
open PTX PTX.Flow PTX.Frame



private theorem succ_block {L g} (s : Startup.D) (e : Event) (hne : ∀ r, s.site ≠ .enter r)
    (hb : s.site.pc ∈ Lib.blockPcs) :
    ∃ s', Startup.succ L g s e = some (some s') ∧ (∀ r, s'.site ≠ .enter r) ∧
      (isWarpAt s'.site.pc = true → (s.site.pc, s'.site.pc) ∈ Lib.pairs) := by
  obtain ⟨site, tm, x, w⟩ := s
  cases site <;> simp only [Startup.Site.pc] at hb
  case ld0 | shfl => exact absurd hb (by decide)
  case enter r => exact absurd rfl (hne r)
  all_goals simp only [Startup.succ]
  case alloc =>
    split
    all_goals exact ⟨_, rfl, nofun, fun h =>
      absurd h (by simp only [Startup.Site.pc]; decide +kernel)⟩
  case allocWr | bar0 =>
    exact ⟨_, rfl, nofun, fun h => absurd h (by simp only [Startup.Site.pc]; decide +kernel)⟩
  case bar1 =>
    split
    · exact ⟨_, rfl, nofun, fun h => absurd h (by simp only [Startup.Site.pc]; decide +kernel)⟩
    · exact ⟨_, rfl, nofun, fun _ => by simp only [Startup.Site.pc]; decide⟩
  case relinq => exact ⟨_, rfl, nofun, fun _ => by simp only [Startup.Site.pc]; decide⟩

public theorem block {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f) (nu : NoUbBefore X g k)
    (hr : e.pc < 27) (hb : e.pc ∈ Lib.blockPcs) :
    Lib.BlockFacts (schedule Q L).code (CollAt Q L) X g k e := by
  obtain ⟨σ, hs, -⟩ := event_table hf hX hp he hu
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs hu
  obtain ⟨s, n, rfl⟩ := (state_role σ).startup (by omega)
  have inv := (reached_table hf (Frame.lt_of_get hX he) nu hs).1
  have hne : ∀ r, s.site ≠ .enter r := fun r h => by
    have := inv
    simp [Code.gatedExit_none] at this
    simp [Startup.enterOf, h] at this
  have step := Frame.stateAt_succ (C := thread Q L) (X := X) (show (X.tr g)[k]? = some e from he)
  rw [hs] at step
  change e.pc = s.site.pc at pc
  obtain ⟨s', hs', hne', hw⟩ := succ_block (L := L) (g := g) s e hne (pc ▸ hb)
  simp only [thread, Code.roleThread, Code.counted, Code.toMachine, Code.glue, hs', Option.map_some,
    Option.bind_some] at step
  have en0 : Startup.enterOf s' = none := by
    obtain ⟨site, tm', x', w'⟩ := s'
    cases site <;> first | rfl | exact absurd rfl (hne' _)
  have en : (Startup.code Q L g).enter (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s' = .inl s' :=
    Code.enter_none (Code.gatedExit_none.mpr en0)
  simp only [en] at step
  exact Lib.BlockFacts.of_step hs (Lib.not_coll hb pc) step
    (fun h2 => pc ▸ hw (collAt_iff_warp.mp h2))

private theorem cls_bar (i : Nat) : cls (.bar i) = Execution.isBarId i := by
  funext e
  obtain ⟨pc, k⟩ := e
  cases k <;> rfl

/-- A lane at the startup shuffle has made both startup rendezvous. -/
public theorem bars_shfl {Q L m X z} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (nu : NoUbBefore X z (X.tr z).length)
    (hat : Lib.StateAt (schedule Q L).code X z (X.tr z).length fun σ =>
      ((schedule Q L).code z).pc σ = 17) : (X.tr z).countP (Execution.isBarId 0) = 2 := by
  obtain ⟨σ, hs, h17⟩ := hat
  have h17' : ((thread Q L z).pc σ) = 17 := h17
  obtain ⟨s, n, rfl⟩ := (state_role σ).startup (by omega)
  have c := (startup_counts hp hX le_rfl hs nu).first
  have h := fcount hs (.bar 0)
  rw [List.take_length, cls_bar] at h
  have hsite : s.site = .shfl := by
    change s.site.pc = 17 at h17'
    obtain ⟨site, tm, x, w⟩ := s
    cases site
    case shfl => rfl
    case enter r => cases r <;> simp [Site.pc, Entry.pc] at h17'
    all_goals exact absurd h17' (by simp only [Site.pc]; decide)
  rw [hsite] at c
  exact h.symm.trans c

end PTX.Kernels.InklingRelDecode.Proof.Startup.Export
