-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LedgerInv
public import Kernels.InklingRelDecode.Proof2.Safety.RoleIter

@[expose] public section

/-!
# `RoleReads` from the second tree

`roleReads_of_p2`: `Interface.RoleReads L X` for every consistent execution, from the second
tree's reads of the role byte on its role table (`Proof2.role_byte`: at barrier-1 count 1 byte
`w - 4` of `0x01000202`, at count 4 or more byte `w - 4` of `0x03030303`); `roleIdx_i32` decodes
the byte. `pc_ldRole_state`: the first tree's state at the position of the role-byte load.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem pro_pc_ne_role (s : ProA.Site) : s.pc ≠ Worker.Site.ldRole.pc := by
  cases s
  all_goals decide +kernel

theorem dstart_pc_ne_role (s : DStart.Site) : s.pc ≠ Worker.Site.ldRole.pc := by
  cases s
  all_goals decide +kernel

theorem sm_pc_ne_role (s : Sm.Site) : s.pc ≠ Worker.Site.ldRole.pc := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem epi_pc_ne_role (s : Epi.Site) : s.pc ≠ Worker.Site.ldRole.pc := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem worker_pc_ne_role (s : Worker.Site) (h : s.pc = Worker.Site.ldRole.pc) : s = .ldRole := by
  revert h
  cases s
  all_goals first
    | (intro _; rfl)
    | (intro h; exfalso; revert h; decide +kernel)

theorem idle_pc_ne_role (s : Worker.Idle.Site) : s.pc ≠ Worker.Site.ldRole.pc := by
  cases s
  all_goals decide +kernel

theorem loader_pc_ne_role (s : Loader.Site) : s.pc ≠ Worker.Site.ldRole.pc := by
  cases s
  all_goals decide +kernel

theorem mma_pc_ne_role (s : Mma.Site) : s.pc ≠ Worker.Site.ldRole.pc := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem exit_pc_ne_role (s : WComp.ExitSite) : s.pc ≠ Worker.Site.ldRole.pc := by
  cases s
  all_goals decide +kernel

/-- **The state at the position of the role-byte load is the worker's `ldRole`.** -/
theorem pc_ldRole_state {s : TSt} (h : TSt.pc s = Worker.Site.ldRole.pc) :
    ∃ P, s = .w (.worker ⟨.ldRole, P⟩) := by
  cases s with
  | d s =>
    exfalso
    cases s with
    | dstart d => exact dstart_pc_ne_role d.site h
    | pro d => exact pro_pc_ne_role d.site h
    | sm d => exact sm_pc_ne_role d.site h
    | epi d => exact epi_pc_ne_role d.site h
  | w s =>
    cases s with
    | worker w =>
      obtain ⟨site, P⟩ := w
      have := worker_pc_ne_role site h
      subst this
      exact ⟨P, rfl⟩
    | idle d => exact absurd h (idle_pc_ne_role d.site)
    | loader d _ => exact absurd h (loader_pc_ne_role d.site)
    | mma d _ => exact absurd h (mma_pc_ne_role d.site)
    | exit x => exact absurd h (exit_pc_ne_role x.site)

/-- The decoded index of byte `j` of a word. -/
theorem roleIdx_i32 (x j : Nat) (hj : j < 4) :
    roleIdx [some (i32Byte x j)] = some (x / 256 ^ j % 256) := by
  unfold roleIdx
  rw [Proof2.rebuild_byte x j hj]
  have hl : x / 256 ^ j % 256 < 256 := Nat.mod_lt _ (by omega)
  simp [extendLoaded, Value.bitPattern, MemExt.extendBits, pure, Except.pure]
  rw [Proof.ProA.truncBits_ofNat 8 _ (by decide)]
  simp only [BitVec.toNat_ofNat]
  omega

/-- **`RoleReads` from the second tree's role-byte reads** (`Proof2.role_byte`). -/
theorem roleReads_of_p2 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) :
    RoleReads L X := by
  intro g k a bs _ _ hget
  obtain ⟨hw4, hw8, -, h1, h4⟩ := Proof2.role_byte hpre hX hget
  have hj : g % L.block / 32 - 4 < 4 := by omega
  have hlt : warpRole (g % L.block / 32) < 3 := by
    unfold warpRole
    rcases (by omega : g % L.block / 32 - 4 = 0 ∨ g % L.block / 32 - 4 = 1 ∨
      g % L.block / 32 - 4 = 2 ∨ g % L.block / 32 - 4 = 3) with h | h | h | h <;> rw [h] <;>
      norm_num
  have hfirst : b1N X g k = 1 → roleIdx bs = some (warpRole (g % L.block / 32)) := by
    intro hb
    rw [h1 hb, roleIdx_i32 _ _ hj]
    rfl
  refine ⟨fun hb => ⟨_, hlt, hfirst hb⟩, fun hb => ?_, hfirst⟩
  rw [h4 hb, roleIdx_i32 _ _ hj]
  rcases (by omega : g % L.block / 32 - 4 = 0 ∨ g % L.block / 32 - 4 = 1 ∨
    g % L.block / 32 - 4 = 2 ∨ g % L.block / 32 - 4 = 3) with h | h | h | h <;> rw [h] <;>
    norm_num

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
