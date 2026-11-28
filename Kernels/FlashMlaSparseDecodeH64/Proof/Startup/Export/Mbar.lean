-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarInit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Startup
public import Lemmas.Kernel.Safety.Classes
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # The startup's mbarrier and barrier-0 rows

Over the events of a launched thread before which it passed no barrier-0 event (the startup's,
`startup_view`):

* `startup_mbInit`: an mbarrier initialization is the `j`-th of the order `MbarFam.ofInit`, at
  the family's object of the thread's CTA with its count, where `j` is the number of the thread's
  initializations before it;
* `startup_bar0`: an event on barrier 0 is `bar.sync 0` of the whole CTA, after `0` or all `23`
  initializations of the thread;

and every other startup event is neither (`kind_cases`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- The startup's events by kind: an initialization at its site with the count before it, the
barrier at its site, or an event of another kind. -/
private theorem kind_cases {d : Startup.D} {mi : Nat} (hev : Startup.Ev L g d e)
    (hJ : Startup.Ref d mi 0) (hx : Startup.exitOf d = none) :
    (∃ n : Fin 23, e.kind = .mbInit (mbarLoc L (g / L.block) (MbarFam.ofInit n))
        (MbarFam.ofInit n).count ∧ mi = n.val ∧ d.site = .init n) ∨
      (e.kind = .bar 0 none .sync ∧ (mi = 0 ∨ mi = 23)) ∨
      ((∀ l c, e.kind ≠ .mbInit l c) ∧ (∀ cnt md, e.kind ≠ .bar 0 cnt md) ∧
        ∀ l, ¬ Frame.MbarOf e l) := by
  obtain ⟨site, x1, x2⟩ := d
  have other : ∀ k : Kind, e.kind = k → (∀ l c, k ≠ .mbInit l c) → (∀ cnt md, k ≠ .bar 0 cnt md) →
      (∀ pc l, ¬ Frame.MbarOf ⟨pc, k⟩ l) →
      (∀ l c, e.kind ≠ .mbInit l c) ∧ (∀ cnt md, e.kind ≠ .bar 0 cnt md) ∧
        ∀ l, ¬ Frame.MbarOf e l := by
    intro k hk h1 h2 h3
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    exact ⟨h1, h2, h3 pc⟩
  cases site with
  | sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨r, ok, hk⟩ := hev <;>
      exact .inr (.inr (other _ hk (by simp) (by simp) (by simp [Frame.MbarOf])))
  | elect j =>
    obtain ⟨inst, ld, -, hk⟩ := hev
    exact .inr (.inr (other _ hk (by simp) (by simp) (by simp [Frame.MbarOf])))
  | init n => exact .inl ⟨n, hev, hJ.1, rfl⟩
  | fence => exact .inr (.inr (other _ hev (by simp) (by simp) (by simp [Frame.MbarOf])))
  | alloc => exact .inr (.inr (other _ hev (by simp) (by simp) (by simp [Frame.MbarOf])))
  | allocSt =>
    obtain ⟨col, -, hk⟩ := hev
    exact .inr (.inr (other _ hk (by simp) (by simp) (by simp [Frame.MbarOf])))
  | ld =>
    rcases hev with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩
    · exact .inr (.inr (other _ hk (by simp) (by simp) (by simp [Frame.MbarOf])))
    · exact .inr (.inr (other _ hk (by simp) (by simp) (by simp [Frame.MbarOf])))
  | trap => exact .inr (.inr (other _ hev (by simp) (by simp) (by simp [Frame.MbarOf])))
  | relinq => exact .inr (.inr (other _ hev (by simp) (by simp) (by simp [Frame.MbarOf])))
  | bar => exact .inr (.inl ⟨hev, hJ.1⟩)
  | enter r => simp [Startup.exitOf] at hx

/-- **The startup's initializations.** -/
theorem startup_mbInit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) {l : Loc} {c : Nat}
    (hk : e.kind = .mbInit l c) (h0 : ((X.tr g).take k).countP isBar0 = 0) :
    ∃ j : Fin 23, l = mbarLoc L (g / L.block) (MbarFam.ofInit j) ∧ c = (MbarFam.ofInit j).count ∧
      ((X.tr g).take k).countP isMbInit = j.val := by
  obtain ⟨d, hJ, hev, hx⟩ := startup_view hp hX hFw he (fun f h => by rw [hk] at h; cases h) h0
  rcases kind_cases hev hJ hx with ⟨n, hk', hn, -⟩ | ⟨hk', -⟩ | ⟨h1, -, -⟩
  · rw [hk] at hk'
    cases hk'
    exact ⟨n, rfl, rfl, hn⟩
  · rw [hk] at hk'; cases hk'
  · exact absurd hk (h1 l c)

/-- **The startup's barrier-0 event** is `bar.sync 0` of the whole CTA, after `0` or `23`
initializations of the thread. -/
theorem startup_bar0 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) {cnt : Option Nat} {mode : BarMode}
    (hk : e.kind = .bar 0 cnt mode) (h0 : ((X.tr g).take k).countP isBar0 = 0) :
    cnt = none ∧ mode = .sync ∧
      (((X.tr g).take k).countP isMbInit = 0 ∨ ((X.tr g).take k).countP isMbInit = 23) := by
  obtain ⟨d, hJ, hev, hx⟩ := startup_view hp hX hFw he (fun f h => by rw [hk] at h; cases h) h0
  rcases kind_cases hev hJ hx with ⟨n, hk', -⟩ | ⟨hk', hn⟩ | ⟨-, h2, -⟩
  · rw [hk] at hk'; cases hk'
  · rw [hk] at hk'
    cases hk'
    exact ⟨rfl, rfl, hn⟩
  · exact absurd hk (h2 cnt mode)

/-- **The startup names an mbarrier only by an initialization.** -/
theorem startup_mbarOf (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) {l : Loc} (hm : Frame.MbarOf e l)
    (h0 : ((X.tr g).take k).countP isBar0 = 0) : ∃ c, e.kind = .mbInit l c := by
  have hub : ∀ f, e.kind ≠ .ub f := by
    intro f hk
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    simp [Frame.MbarOf] at hm
  obtain ⟨d, hJ, hev, hx⟩ := startup_view hp hX hFw he hub h0
  rcases kind_cases hev hJ hx with ⟨n, hk', -⟩ | ⟨hk', -⟩ | ⟨-, -, h3⟩
  · obtain ⟨pc, kd⟩ := e
    simp only at hk'
    subst hk'
    exact ⟨_, by simp only [Frame.MbarOf] at hm; rw [hm]⟩
  · obtain ⟨pc, kd⟩ := e
    simp only at hk'
    subst hk'
    simp [Frame.MbarOf] at hm
  · exact absurd hm (h3 l)

/-- **Row `MbarRow.Startup`**: a startup event (below pc 103) that names an mbarrier is the
thread's `j`-th initialization, of family `MbarFam.ofInit j` with its count, in warp 0. -/
theorem mbarRow_startup (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MbarRow.Startup P L X := by
  intro g k e l _ he hpc hm
  have hub : ∀ f, e.kind ≠ .ub f := by
    intro f hk
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    simp [Frame.MbarOf] at hm
  obtain ⟨d, hR, hW, hev, hx, -⟩ := startup_at hp hX hFw he hub hpc
  rcases kind_cases hev hR hx with ⟨n, hk, hn, hs⟩ | ⟨hk, -⟩ | ⟨-, -, h3⟩
  · simp only [Startup.RefW, hs] at hW
    obtain ⟨-, -, -, hw0⟩ := hW
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    simp only [Frame.MbarOf] at hm
    exact ⟨hw0, n, hn.symm, hm, by rw [hm]⟩
  · obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    simp [Frame.MbarOf] at hm
  · exact absurd hm (h3 l)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
