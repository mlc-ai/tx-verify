-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarInit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep

@[expose] public section

/-! # A startup initialization follows a won election

`startup_init_won`: an mbarrier initialization of a launched lane at a startup pc (below 103) has
no barrier-0 event before it, and an earlier event of the lane is the election at pc 31 that the
lane won (it returned the lane's own index). This is the history half of the row
`InitRows.won` (`Protocol/Mbar/InitFirst.lean`).

Proof: the initialization is fired from a startup state at an initialization site
(`startup_state`); going back along the thread machine (`Frame.stateAt_succ`), the state before
an initialization site is a startup state at an initialization site or at the second election,
which went there only for the lane's own index (`succ_init`); a fragment never returns to the
startup and a stub state has no invariant. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- A startup step into an initialization site comes from an initialization site or from the
second election, won by the lane. -/
private theorem succ_init {d d' : Startup.D} (hs : Startup.succ L g d e = some (some d'))
    {i : Fin 23} (hi : d'.site = .init i) :
    (∃ i', d.site = .init i') ∨
      (d.site = .elect 1 ∧ ∃ mk inst, e.kind = .elect mk inst (PTX.laneOf L g)) := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | init i' => exact .inl ⟨i', rfl⟩
  | elect j =>
    simp only [Startup.succ] at hs
    split at hs
    · next mk inst ld hk =>
      fin_cases j
      · obtain rfl := Option.some.inj (Option.some.inj hs)
        simp at hi
      · simp only at hs
        split_ifs at hs with hl
        · exact .inr ⟨rfl, mk, inst, by rw [hk, hl]⟩
        · obtain rfl := Option.some.inj (Option.some.inj hs)
          simp at hi
    · cases hs
  | sh j =>
    exfalso
    simp only [Startup.succ] at hs
    split at hs
    · obtain ⟨x, rfl⟩ := word32_some hs
      fin_cases j
      · simp at hi
      · simp only at hi
        split_ifs at hi
    · cases hs
  | ld =>
    exfalso
    simp only [Startup.succ] at hs
    split at hs
    · split at hs
      · unfold Startup.afterLd at hs
        split at hs
        · split_ifs at hs <;> (obtain rfl := Option.some.inj (Option.some.inj hs); simp at hi)
        · cases hs
      · cases hs
    · cases hs
  | alloc =>
    exfalso
    simp only [Startup.succ] at hs
    split_ifs at hs <;> (obtain rfl := Option.some.inj (Option.some.inj hs); simp at hi)
  | bar =>
    exfalso
    simp only [Startup.succ, Startup.enterOf] at hs
    split_ifs at hs <;> (obtain rfl := Option.some.inj (Option.some.inj hs); simp at hi)
  | enter q => simp [Startup.succ] at hs
  | trap => simp [Startup.succ] at hs
  | fence =>
    obtain rfl := Option.some.inj (Option.some.inj hs)
    simp at hi
  | allocSt =>
    obtain rfl := Option.some.inj (Option.some.inj hs)
    simp at hi
  | relinq =>
    obtain rfl := Option.some.inj (Option.some.inj hs)
    simp at hi

/-- **The history of a startup state of a class `Q`**: when every successor into `Q` is a step
from `Q` or the second election's step (whose result satisfies `W`), a state of `Q` follows an
election at pc 31 with a result of `W`. -/
private theorem startup_hist (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hg : g < L.threads) (Q : Startup.D → Prop) (W : Nat → Prop)
    (hQ : ∀ d d' e, Startup.succ L g d e = some (some d') → Q d' →
      Q d ∨ (d.site = .elect 1 ∧ ∃ mk inst ld, e.kind = .elect mk inst ld ∧ W ld))
    (h0 : ¬ Q ⟨.sh 0, 0, 0⟩) :
    ∀ k (d : Startup.D) (n : Cls → Nat),
      Frame.stateAt (thread P L) X g k = some (some (.inl d, n)) → Q d →
      ∃ j < k, ∃ mk inst ld, X.get (g, j) = some ⟨31, .elect mk inst ld⟩ ∧ W ld := by
  intro k
  induction k with
  | zero =>
    intro d n hσ hi
    rw [Frame.stateAt_zero, thread_init] at hσ
    simp only [Option.some.injEq, Prod.mk.injEq, Sum.inl.injEq] at hσ
    obtain ⟨rfl, -⟩ := hσ
    exact (h0 hi).elim
  | succ k ih =>
    intro d n hσ hi
    rcases hk : (X.tr g)[k]? with _ | e
    · have hlen : (X.tr g).length ≤ k := List.getElem?_eq_none_iff.mp hk
      have h' : Frame.stateAt (thread P L) X g (k + 1) = Frame.stateAt (thread P L) X g k := by
        unfold Frame.stateAt
        rw [List.take_of_length_le hlen, List.take_of_length_le (by omega)]
      obtain ⟨j, hj, hw⟩ := ih d n (h' ▸ hσ) hi
      exact ⟨j, by omega, hw⟩
    · rw [Frame.stateAt_succ hk] at hσ
      obtain ⟨τ, hτ, hn⟩ := Option.bind_eq_some_iff.mp hσ
      rcases τ with _ | ⟨s, n'⟩
      · cases hn
      have hn' : (thread P L g).next (s, n') e = some (some (.inl d, n)) := hn
      rcases s with d' | ⟨i | r, d'⟩
      · rw [next_startup] at hn'
        rcases h : Startup.succ L g d' e with _ | _ | d''
        · rw [h] at hn'; cases hn'
        · rw [h] at hn'; cases hn'
        rw [h] at hn'
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hn'
        obtain ⟨h1, -⟩ := hn'
        have hd : d'' = d := by
          unfold Code.enter at h1
          split at h1
          · cases h1
          · exact Sum.inl.inj h1
        subst hd
        rcases hQ d' d'' e h hi with hi' | ⟨hs1, mk, inst, ld, hel, hW⟩
        · obtain ⟨j, hj, hw⟩ := ih d' n' hτ hi'
          exact ⟨j, by omega, hw⟩
        · have he : X.get (g, k) = some e := hk
          obtain ⟨σ, hσ', -, -, hev⟩ :=
            ev_state hp hX hFw he (fun f h => by rw [hel] at h; cases h)
          rw [hτ] at hσ'
          obtain rfl := Option.some.inj (Option.some.inj hσ')
          obtain ⟨site, x1, x2⟩ := d'
          simp only at hs1
          subst hs1
          obtain ⟨-, -, hpc, -⟩ := (hev : Startup.Ev L g ⟨.elect 1, x1, x2⟩ e)
          obtain ⟨pc, kd⟩ := e
          simp only at hpc hel
          subst hpc hel
          exact ⟨k, by omega, mk, inst, ld, he, hW⟩
      · rw [next_frag] at hn'
        rcases h : (frag P L g i).next d' e with _ | _ | d'' <;> rw [h] at hn' <;> simp at hn'
      · exact ((follow_iff.mp hFw g hg k).2 _ hτ).elim

/-- The history of a startup state at an initialization site: an earlier event is the election
at pc 31 that the lane won. -/
private theorem hist (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hg : g < L.threads) :
    ∀ k (d : Startup.D) (n : Cls → Nat),
      Frame.stateAt (thread P L) X g k = some (some (.inl d, n)) → (∃ i, d.site = .init i) →
      ∃ j < k, ∃ mk inst, X.get (g, j) = some ⟨31, .elect mk inst (PTX.laneOf L g)⟩ := by
  intro k d n hσ hi
  obtain ⟨j, hj, mk, inst, ld, hget, hld⟩ := startup_hist hp hX hFw hg
    (fun d => ∃ i, d.site = .init i) (fun ld => ld = PTX.laneOf L g)
    (fun d d' e hs ⟨i, hi⟩ => by
      rcases succ_init hs hi with h | ⟨h, mk, inst, hk⟩
      · exact .inl h
      · exact .inr ⟨h, mk, inst, _, hk, rfl⟩)
    (by rintro ⟨i, hi⟩; cases hi) k d n hσ hi
  subst hld
  exact ⟨j, hj, mk, inst, hget⟩

/-- The startup states after the second election: the sites of the election's two outcomes, and
the barrier of a lane on the path of the elections (`x2 = 0`). -/
private def PostElect (d : Startup.D) : Prop :=
  (∃ i, d.site = .init i) ∨ d.site = .fence ∨ d.site = .alloc ∨ d.site = .allocSt ∨
    d.site = .ld ∨ d.site = .relinq ∨ (d.site = .bar ∧ d.x2 = 0)

/-- A step into `PostElect` is a step from it or the second election. -/
private theorem postElect_pred {d d' : Startup.D} {e : Event}
    (hs : Startup.succ L g d e = some (some d')) (hi : PostElect d') :
    PostElect d ∨ (d.site = .elect 1 ∧ ∃ mk inst ld, e.kind = .elect mk inst ld ∧ True) := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | init i => exact .inl (.inl ⟨i, rfl⟩)
  | fence => exact .inl (.inr (.inl rfl))
  | alloc => exact .inl (.inr (.inr (.inl rfl)))
  | allocSt => exact .inl (.inr (.inr (.inr (.inl rfl))))
  | ld => exact .inl (.inr (.inr (.inr (.inr (.inl rfl)))))
  | relinq => exact .inl (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  | trap => simp [Startup.succ] at hs
  | enter q => simp [Startup.succ] at hs
  | bar =>
    exfalso
    simp only [Startup.succ, Startup.enterOf] at hs
    split_ifs at hs <;> (obtain rfl := Option.some.inj (Option.some.inj hs); simp [PostElect] at hi)
  | elect j =>
    simp only [Startup.succ] at hs
    split at hs
    · next mk inst ld hk =>
      fin_cases j
      · obtain rfl := Option.some.inj (Option.some.inj hs)
        simp [PostElect] at hi
      · exact .inr ⟨rfl, mk, inst, ld, hk, trivial⟩
    · cases hs
  | sh j =>
    exfalso
    simp only [Startup.succ] at hs
    split at hs
    · obtain ⟨x, rfl⟩ := word32_some hs
      fin_cases j
      · simp [PostElect] at hi
      · simp only at hi
        split_ifs at hi with hne
        · have hx : x = 0 := by simpa [PostElect] using hi
          subst hx
          revert hne
          decide
        · simp [PostElect] at hi
    · cases hs

/-- **The barrier of a warp-0 lane follows an election at pc 31**: the startup's first barrier-0
event of a lane of warp 0 comes after the second election. -/
theorem startup_bar_elect (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hg : g < L.threads) (he : X.get (g, k) = some e) {cnt : Option Nat}
    {mode : BarMode} (hk : e.kind = .bar 0 cnt mode)
    (h0 : ((X.tr g).take k).countP isBar0 = 0) (hw : warpOf L g = 0) :
    ∃ j < k, ∃ mk inst ld, X.get (g, j) = some ⟨31, .elect mk inst ld⟩ := by
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  have h0' : ((X.tr g).take k).countP (cls .bar0) = 0 := h0
  obtain ⟨⟨s, n⟩, hσ, hJ, hi, hev⟩ := ev_state hp hX hFw he hub
  have hb := state_count hσ .bar0
  simp only at hb
  rcases s with d | ⟨i | r, d'⟩
  · obtain ⟨-, hW, -⟩ := hJ
    have hs := state_count hσ .shfl
    simp only at hs
    obtain ⟨site, x1, x2⟩ := d
    have hev' : Startup.Ev L g ⟨site, x1, x2⟩ e := hev
    have hx : Startup.exitOf ⟨site, x1, x2⟩ = none := by
      simpa [Code.gatedExit, startupEnter] using hi.2
    cases site with
    | bar =>
      simp only [Startup.RefW] at hW
      obtain ⟨-, -, hx2'⟩ := hW
      have hx2 : x2 = 0 := by rw [hx2']; simp [warpW, hw]
      obtain ⟨j, hj, mk, inst, ld, hget, -⟩ := startup_hist hp hX hFw hg PostElect (fun _ => True)
        (fun d d' e hs hi => by
          rcases postElect_pred hs hi with h | ⟨h1, mk, inst, ld, h2, h3⟩
          · exact .inl h
          · exact .inr ⟨h1, mk, inst, ld, h2, h3⟩)
        (by simp [PostElect]) k ⟨.bar, x1, x2⟩ n hσ
        (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, hx2⟩))))))
      exact ⟨j, hj, mk, inst, ld, hget⟩
    | sh j => fin_cases j <;> simp [Startup.Ev, hk] at hev'
    | enter q => simp [Startup.exitOf] at hx
    | _ => simp [Startup.Ev, hk] at hev'
  · exfalso
    have hJ' : 1 ≤ n .bar0 := by cases i <;> exact hJ.1
    omega
  · exact hJ.elim

/-- **An initialization at a startup pc follows a won election at pc 31**, with no barrier-0
event before it. -/
theorem startup_init_won (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hg : g < L.threads) (he : X.get (g, k) = some e) {l : Loc} {c : Nat}
    (hk : e.kind = .mbInit l c) (hpc : e.pc < 103) :
    ((X.tr g).take k).countP isBar0 = 0 ∧
      ∃ j < k, ∃ mk inst, X.get (g, j) = some ⟨31, .elect mk inst (PTX.laneOf L g)⟩ := by
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  obtain ⟨-, -, -, -, -, h0, -⟩ := startup_at hp hX hFw he hub hpc
  obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, -, hE, hx, -⟩ := startup_state hJ hi hev hpc' hpc
  refine ⟨h0, hist hp hX hFw hg k d n hσ ?_⟩
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | init i => exact ⟨i, rfl⟩
  | sh j => fin_cases j <;> simp [Startup.Ev, hk] at hE
  | enter q => simp [Startup.exitOf] at hx
  | _ => simp [Startup.Ev, hk] at hE

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
