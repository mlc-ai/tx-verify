-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarInit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View

@[expose] public section

/-! # The startup's elections

Over the startup's events (no barrier-0 event before them):

* `startup_elect`: an election elects among the full warp, at pc 16 or 31;
* `startup_elect_warp0`: only warp 0 reaches them;
* `startup_won`: a lane that won the election at pc 31 initializes the first mbarrier of the
  order (`MbarFam.ofInit 0`) as its next event (or its next event is undefined behaviour). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- A startup event that is an election is fired from an election site, at its pc. -/
private theorem elect_site {d : Startup.D} {mk inst ld : Nat} (hev : Startup.Ev L g d e)
    (hk : e.kind = .elect mk inst ld) (hx : Startup.exitOf d = none) :
    ∃ j, d.site = .elect j ∧ e.pc = (Startup.Site.elect j).pc ∧ mk = 2 ^ 32 - 1 := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | elect j =>
    obtain ⟨inst', ld', hpc, hk'⟩ := hev
    rw [hk] at hk'
    cases hk'
    exact ⟨j, rfl, hpc, rfl⟩
  | sh j =>
    exfalso
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨r, ok, hk'⟩ := hev <;>
      rw [hk] at hk' <;> cases hk'
  | allocSt =>
    obtain ⟨col, -, hk'⟩ := hev
    rw [hk] at hk'; cases hk'
  | ld =>
    exfalso
    rcases hev with ⟨a, bs, hk', -⟩ | ⟨f, hk'⟩ <;> rw [hk] at hk' <;> cases hk'
  | enter r => simp [Startup.exitOf] at hx
  | init n => simp only [Startup.Ev] at hev; rw [hk] at hev; cases hev
  | fence => simp only [Startup.Ev] at hev; rw [hk] at hev; cases hev
  | alloc => simp only [Startup.Ev] at hev; rw [hk] at hev; cases hev
  | trap => simp only [Startup.Ev] at hev; rw [hk] at hev; cases hev
  | relinq => simp only [Startup.Ev] at hev; rw [hk] at hev; cases hev
  | bar => simp only [Startup.Ev] at hev; rw [hk] at hev; cases hev

/-- **The startup's elections elect among the full warp.** -/
theorem startup_elect (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) {mk inst ld : Nat}
    (hk : e.kind = .elect mk inst ld) (h0 : ((X.tr g).take k).countP isBar0 = 0) :
    mk = 2 ^ 32 - 1 ∧ (e.pc = 16 ∨ e.pc = 31) := by
  obtain ⟨d, -, hev, hx⟩ := startup_view hp hX hFw he (fun f h => by rw [hk] at h; cases h) h0
  obtain ⟨j, -, hpc, hmk⟩ := elect_site hev hk hx
  refine ⟨hmk, ?_⟩
  rw [hpc]
  fin_cases j
  · exact .inl rfl
  · exact .inr rfl

/-- **A lane that won the second election initializes next.** -/
theorem startup_won (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) {mk inst : Nat}
    (hk : e.kind = .elect mk inst (PTX.laneOf L g)) (hpc : e.pc = 31)
    (h0 : ((X.tr g).take k).countP isBar0 = 0) {e' : Event}
    (he' : X.get (g, k + 1) = some e') :
    e'.kind = .mbInit (mbarLoc L (g / L.block) (MbarFam.ofInit 0)) (MbarFam.ofInit 0).count ∨
      ∃ f, e'.kind = .ub f := by
  by_cases hub : ∃ f, e'.kind = .ub f
  · exact .inr hub
  have hub' : ∀ f, e'.kind ≠ .ub f := fun f h => hub ⟨f, h⟩
  obtain ⟨⟨s, n⟩, hσ, hJ, hi, hev⟩ := ev_state hp hX hFw he (fun f h => by rw [hk] at h; cases h)
  have hb := state_count hσ .bar0
  simp only at hb
  rcases s with d | ⟨i | r, d'⟩
  · have hx : Startup.exitOf d = none := by
      have := hi.2
      simpa [Code.gatedExit, startupEnter] using this
    obtain ⟨j, hsite, hpcj, -⟩ := elect_site hev hk hx
    have hj : j = 1 := by
      fin_cases j
      · rw [hpc] at hpcj; cases hpcj
      · rfl
    subst hj
    obtain ⟨site, x1, x2⟩ := d
    simp only at hsite
    subst hsite
    have hnext := Frame.stateAt_succ (C := thread P L) (X := X) (g := g) (k := k) he
    rw [hσ] at hnext
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    have hs : Frame.stateAt (thread P L) X g (k + 1) = some (some
        (.inl ⟨.init 0, x1, x2⟩, Code.bump cls n ⟨pc, .elect mk inst (PTX.laneOf L g)⟩)) := by
      rw [hnext]
      simp [Code.toMachine, Startup.succ, Code.enter, Code.gatedExit,
        startupEnter, Startup.exitOf]
    obtain ⟨-, -, hev'⟩ := Frame.RoleTable.ev_atU (T := table P L)
      (fun _ _ => thread_sound hp) hX (shapeOk hp _).toShapeOkU
      (follow_iff.mp hFw) (Frame.lt_of_get hX he') he' hs hub'
    exact .inl hev'
  · have h1 : 1 ≤ n .bar0 := by cases i <;> exact hJ.1
    rw [hb] at h1
    exact absurd h0 (by simpa [cls] using Nat.pos_iff_ne_zero.mp h1)
  · exact hJ.elim

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
