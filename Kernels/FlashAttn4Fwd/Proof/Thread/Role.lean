-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Idle
public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueCluster
public import Kernels.FlashAttn4Fwd.Proof.Thread.Loader
public import Kernels.FlashAttn4Fwd.Proof.Thread.Mma
public import Kernels.FlashAttn4Fwd.Proof.Thread.Store
public import Kernels.FlashAttn4Fwd.Proof.Thread.Softmax
public import Kernels.FlashAttn4Fwd.Proof.Thread.Correction

@[expose] public section

/-! # The roles of a thread and the routing to them

After the prologue a thread runs one role, chosen by its warp index (`RoleKind.ofWarp`): the
loader (warp 14), the MMA warp (12), the epilogue store warp (13), the softmax warps (0-7), the
correction warps (8-11) and the idle warp (15). Every role starts at its own `setmaxnreg`
(`RoleKind.entry`), which the dispatch reaches with the prologue's registers live there
(`Prologue.dispatch`).

`Role` holds the state of each role (`Thread/{Idle,Loader,Mma,Store,Softmax,Correction}.lean`);
`Role.start` gives its first state. Every role's machine is composed into the thread's machine
(`Machine.lean`): the first states are those of the roles' own code machines (the MMA warp's
carries the prologue's registers of warp 12, `Mma.D.pro`), and the entry lemmas
(`Entry.lean`) turn the prologue's facts at the entry (`Prologue.factsAt L g w (rankOf L g)
k.entry`, `w` the warp) into the first state's facts. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The state of a role. -/
inductive Role where
  | idle (s : Idle.D)
  | loader (d : Loader.D)
  | mma (d : Mma.D)
  | store (d : Store.D)
  | softmax (d : Softmax.D)
  | corr (d : Correction.D)

/-- The role of a state. -/
def Role.kind : Role → RoleKind
  | .idle _ => .idle
  | .loader _ => .loader
  | .mma _ => .mma
  | .store _ => .store
  | .softmax _ => .softmax
  | .corr _ => .corr

/-- The first state of each composed role, that of its own code machine (`Loader.code`,
`Mma.code`, `Store.code`, `Softmax.code`, `Correction.code`). -/
def Role.start (L : Launch) (g : Nat) : RoleKind → Option Role
  | .idle => some (.idle Idle.start)
  | .loader => some (.loader ⟨.setMaxReg, 0, 0, 0, 1, 1⟩)
  | .mma => some (.mma ⟨.setMaxReg, 0, 0, b32 0, Prologue.valueOf L g 12 (rankOf L g)⟩)
  | .store => some (.store ⟨.setMaxReg, 0⟩)
  | .corr => some (.corr ⟨.setMaxReg, 0, 0, b32 0, 0, []⟩)
  | .softmax => some (.softmax Softmax.start)

theorem Role.start_kind {L : Launch} {g : Nat} {k : RoleKind} {r : Role}
    (h : Role.start L g k = some r) : r.kind = k := by
  cases k <;> simp only [Role.start, Option.some.injEq] at h <;> subst h <;> rfl

/-! ### Routing: the role of each warp -/

theorem RoleKind.ofWarp_loader {w : Nat} : RoleKind.ofWarp w = .loader ↔ w = 14 := by
  unfold RoleKind.ofWarp; split_ifs <;> simp_all

theorem RoleKind.ofWarp_idle {w : Nat} : RoleKind.ofWarp w = .idle ↔ w = 15 := by
  unfold RoleKind.ofWarp; split_ifs <;> simp_all

theorem RoleKind.ofWarp_mma {w : Nat} : RoleKind.ofWarp w = .mma ↔ w = 12 := by
  unfold RoleKind.ofWarp; split_ifs <;> simp_all

theorem RoleKind.ofWarp_store {w : Nat} : RoleKind.ofWarp w = .store ↔ w = 13 := by
  unfold RoleKind.ofWarp; split_ifs <;> simp_all

theorem RoleKind.ofWarp_softmax {w : Nat} : RoleKind.ofWarp w = .softmax ↔ w < 8 := by
  unfold RoleKind.ofWarp; split_ifs <;> simp_all

/-- The warps of a role. -/
def RoleKind.Warp : RoleKind → Nat → Prop
  | .loader, w => w = 14
  | .mma, w => w = 12
  | .store, w => w = 13
  | .softmax, w => w < 8
  | .corr, w => 8 ≤ w ∧ w < 12
  | .idle, w => w = 15

/-- A warp of the CTA goes to a role of its own warp index. -/
theorem RoleKind.warp_ofWarp {w : Nat} (hw : w < 16) : (RoleKind.ofWarp w).Warp w := by
  unfold RoleKind.ofWarp
  split_ifs <;> simp only [RoleKind.Warp] <;> omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof
