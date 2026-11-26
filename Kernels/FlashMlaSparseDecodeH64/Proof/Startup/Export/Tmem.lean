-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Startup
public import Lemmas.Tmem.PairProtocol
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmemCnt

@[expose] public section

/-! # The startup's Tensor Memory events

`startup_tc`: a startup event (below pc 103) on Tensor Memory is warp 0's allocation of all 512
columns of CTA group 1, whose address goes to the shared word `Region.tmemWord`, or its
relinquishment of the allocation permit; `tmemRow_startup` is the row `TmemRow.Startup`.
`startup_tmemShape`: the allocation is the thread's first paired Tensor Memory operation and the
relinquishment its second (the ledger's count `Startup.RefT`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- **The startup's `tcgen05` events**: the allocation and the relinquishment, in warp 0. -/
theorem startup_tc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hpc : e.pc < 103) {c : TcKind}
    (hk : e.kind = .tc c) :
    warpOf L g = 0 ∧
      (c = .resource .one (some (wsLoc L (g / L.block) Region.tmemWord.lo)) (.alloc 512) ∨
        c = .resource .one none .relinquish) := by
  obtain ⟨⟨site, x1, x2⟩, -, hW, hev, hx, -⟩ :=
    startup_at hp hX hFw he (fun f h => by rw [hk] at h; cases h) hpc
  cases site with
  | alloc =>
    obtain ⟨-, -, -, hw⟩ := hW
    have hk' : e.kind = _ := hev
    rw [hk] at hk'
    cases hk'
    exact ⟨hw, .inl rfl⟩
  | relinq =>
    obtain ⟨-, -, -, hw⟩ := hW
    have hk' : e.kind = _ := hev
    rw [hk] at hk'
    cases hk'
    exact ⟨hw, .inr rfl⟩
  | sh j => fin_cases j <;> obtain ⟨r, ok, hk'⟩ := hev <;> rw [hk] at hk' <;> cases hk'
  | elect j => obtain ⟨_, _, -, hk'⟩ := hev; rw [hk] at hk'; cases hk'
  | allocSt => obtain ⟨col, -, hk'⟩ := hev; rw [hk] at hk'; cases hk'
  | ld => rcases hev with ⟨a, bs, hk', -⟩ | ⟨f, hk'⟩ <;> rw [hk] at hk' <;> cases hk'
  | enter r => simp [Startup.exitOf] at hx
  | init n => have hk' : e.kind = _ := hev; rw [hk] at hk'; cases hk'
  | fence => have hk' : e.kind = _ := hev; rw [hk] at hk'; cases hk'
  | trap => have hk' : e.kind = _ := hev; rw [hk] at hk'; cases hk'
  | bar => have hk' : e.kind = _ := hev; rw [hk] at hk'; cases hk'

/-- **Row `TmemRow.Startup`**. -/
theorem tmemRow_startup (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : TmemRow.Startup P L X := by
  intro g k e c _ he hat hk
  obtain ⟨hw, h⟩ := startup_tc hp hX hFw he hat hk
  refine ⟨?_, ?_⟩
  · simp only [warpOf, tidOf_eq hp] at hw
    simp only [MbarRow.warp, tidOf_x_eq hp, hw]
  · rcases h with rfl | rfl
    · exact .inl ⟨_, hk⟩
    · exact .inr hk

/-- **The startup's paired operations are its thread's first and second**: a startup event on
Tensor Memory resources has the shape (`Tmem.Pair.TmemShape`) of the thread's count of paired
operations before it. -/
theorem startup_tmemShape (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hat : MbarRow.StartupAt e.pc)
    {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request}
    (hk : e.kind = .tc (.resource grp dst act)) :
    Tmem.Pair.TmemShape (Tmem.Pair.tmemOps ((X.tr g).take k)) act := by
  obtain ⟨⟨site, x1, x2⟩, hT, hE, hx⟩ :=
    startup_tmem hp hX hFw he (fun f h => by rw [hk] at h; cases h) hat
  cases site with
  | sh j => fin_cases j <;> simp [Startup.Ev, hk] at hE
  | enter r => simp [Startup.exitOf] at hx
  | alloc =>
    obtain ⟨h0, -⟩ := hT
    simp only [Startup.Ev, hk, Kind.tc.injEq, TcKind.resource.injEq] at hE
    rw [h0, hE.2.2]
    rfl
  | relinq =>
    obtain ⟨h1, -⟩ := hT
    simp only [Startup.Ev, hk, Kind.tc.injEq, TcKind.resource.injEq] at hE
    rw [h1, hE.2.2]
    rfl
  | _ => simp [Startup.Ev, hk] at hE

/-- **Warp 0 reaches barrier 0 after its allocation and relinquishment**: a startup barrier-0
event of a lane of warp 0 follows two paired operations of its thread. -/
theorem startup_bar0_tmem (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hat : MbarRow.StartupAt e.pc)
    {cnt : Option Nat} {mode : BarMode} (hk : e.kind = .bar 0 cnt mode)
    (hw : MbarRow.warp L g = 0) : Tmem.Pair.tmemOps ((X.tr g).take k) = 2 := by
  have hw' : warpOf L g = 0 := by
    simp only [MbarRow.warp, tidOf_x_eq hp] at hw
    simp only [warpOf, tidOf_eq hp, hw]
  obtain ⟨⟨site, x1, x2⟩, sh, hT, hW, hE, hx⟩ :=
    startup_tmemW hp hX hFw he (fun f h => by rw [hk] at h; cases h) hat
  cases site with
  | sh j => fin_cases j <;> simp [Startup.Ev, hk] at hE
  | enter r => simp [Startup.exitOf] at hx
  | bar =>
    obtain ⟨-, -, hx2⟩ := hW
    simp only [Startup.RefT] at hT
    simp only at hx2
    rw [hT, hx2, Startup.warpW_ne hp, hw']
    rfl
  | _ => simp [Startup.Ev, hk] at hE

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
