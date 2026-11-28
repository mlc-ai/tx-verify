-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Lemmas.Flow.Regs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Startup
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # The startup's memory accesses

`startup_mem`: the startup's (below pc 103) only memory accesses are warp 0's: the allocation's
store of the allocated column (`< 2 ^ 16`) to the four bytes of the shared word
`Region.tmemWord` (pc 91), and the read-back at pc 92. It makes no other access (`nc`, `rmw`).
`memRow_startup` is the row `MemRow.Startup`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- **The startup's memory accesses**: a write is the allocation word's store in warp 0, a read
is the read-back of the same word at pc 92 in warp 0, and there is no other access. -/
theorem startup_mem (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hpc : e.pc < 103) :
    (∀ a v, e.kind = .wr a v → warpOf L g = 0 ∧ e.pc = 91 ∧
      a = { loc := wsLoc L (g / L.block) Region.tmemWord.lo, size := 4 } ∧
      ∃ col, col < 2 ^ 16 ∧ v = (b32 col).toBytes) ∧
    (∀ a bs, e.kind = .rd a bs → warpOf L g = 0 ∧ e.pc = 92 ∧
      MemRow.WsAcc L (g / L.block) Region.tmemWord.lo 4 a) ∧
    (∀ a bs, e.kind ≠ .nc a bs) ∧ (∀ a op v, e.kind ≠ .rmw a op v) := by
  by_cases hu : ∃ f, e.kind = .ub f
  · obtain ⟨f, hf⟩ := hu
    simp [hf]
  obtain ⟨⟨site, x1, x2⟩, -, hW, hev, hx, -, hpc'⟩ :=
    startup_at hp hX hFw he (fun f h => hu ⟨f, h⟩) hpc
  cases site with
  | allocSt =>
    obtain ⟨-, -, -, hw⟩ := hW
    obtain ⟨col, hcol, hk⟩ := hev
    simp only [hk, Kind.wr.injEq, reduceCtorEq, false_implies, implies_true, ne_eq,
      not_false_eq_true, and_true]
    rintro a v ⟨rfl, rfl⟩
    exact ⟨hw, hpc', rfl, col, hcol, rfl⟩
  | ld =>
    obtain ⟨-, -, -, hw⟩ := hW
    rcases hev with ⟨a, bs, hk, hl, hs⟩ | ⟨f, hk⟩
    · simp only [hk, reduceCtorEq, false_implies, implies_true, ne_eq, not_false_eq_true,
        and_true, true_and]
      rintro a' bs' ⟨rfl, rfl⟩
      refine ⟨hw, hpc', ?_, hs⟩
      have hS := sharedBase_lt hp
      rw [hl]
      simp only [wrapAddr, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt,
        Loc.at, wsLoc, Region.lo, Loc.mk.injEq, true_and]
      omega
    · exact absurd ⟨f, hk⟩ hu
  | sh j => fin_cases j <;> obtain ⟨r, ok, hk⟩ := hev <;> simp [hk]
  | elect j => obtain ⟨_, _, -, hk⟩ := hev; simp [hk]
  | enter r => simp [Startup.exitOf] at hx
  | init n => have hk : e.kind = _ := hev; simp [hk]
  | fence => have hk : e.kind = _ := hev; simp [hk]
  | alloc => have hk : e.kind = _ := hev; simp [hk]
  | trap => have hk : e.kind = _ := hev; simp [hk]
  | relinq => have hk : e.kind = _ := hev; simp [hk]
  | bar => have hk : e.kind = _ := hev; simp [hk]

/-- **Row `MemRow.Startup`**. -/
theorem memRow_startup (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MemRow.Startup P L X := by
  intro g k e _ he hat hm
  obtain ⟨hwr, hrd, hnc, hrmw⟩ := startup_mem hp hX hFw he hat
  have hw : ∀ (h : warpOf L g = 0), MbarRow.warp L g = 0 := fun h => by
    simp only [warpOf, tidOf_eq hp] at h
    simp only [MbarRow.warp, tidOf_x_eq hp, h]
  rcases hm with ⟨a, bs, hk⟩ | ⟨a, bs, hk⟩ | ⟨a, bs, hk⟩ | ⟨a, o, n, hk⟩
  · obtain ⟨h0, h92, hws⟩ := hrd a bs hk
    exact ⟨hw h0, .inr ⟨h92, a, bs, hk, hws⟩⟩
  · exact absurd hk (hnc a bs)
  · obtain ⟨h0, -, rfl, -⟩ := hwr a bs hk
    exact ⟨hw h0, .inl ⟨_, bs, hk, rfl, rfl⟩⟩
  · exact absurd hk (hrmw a o n)

/-- **No access of the startup covers an mbarrier's bytes** (the startup part of `bytes`): its
store and its read-back name the allocation word, below the first mbarrier of the lane's CTA. -/
theorem startup_mem_noMbar (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hat : MbarRow.StartupAt e.pc) (hm : MemRow.MemEvent e) :
    ∃ a : Acc, ((∃ bs, e.kind = .rd a bs) ∨ ∃ bs, e.kind = .wr a bs) ∧ a.loc.space = .shared ∧
      a.loc.cta = g / L.block ∧ L.sharedBase ≤ a.loc.addr ∧
        a.loc.addr + a.size ≤ L.sharedBase + Region.mbars.lo := by
  obtain ⟨-, h⟩ := memRow_startup hp hX hFw hg he hat hm
  have hb : ∀ a : Acc, MemRow.WsAcc L (g / L.block) Region.tmemWord.lo 4 a →
      a.loc.space = .shared ∧ a.loc.cta = g / L.block ∧ L.sharedBase ≤ a.loc.addr ∧
        a.loc.addr + a.size ≤ L.sharedBase + Region.mbars.lo := by
    rintro a ⟨hl, hs⟩
    rw [hl, hs]
    exact ⟨rfl, rfl, by simp only [wsLoc]; omega, by simp only [wsLoc, Region.lo]; omega⟩
  rcases h with ⟨a, bs, hk, hw⟩ | ⟨-, a, bs, hk, hw⟩
  · exact ⟨a, .inr ⟨bs, hk⟩, hb a hw⟩
  · exact ⟨a, .inl ⟨bs, hk⟩, hb a hw⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
