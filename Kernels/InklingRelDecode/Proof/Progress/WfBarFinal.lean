-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WfBarSteps
public import Kernels.InklingRelDecode.Proof.Progress.WfFinal

@[expose] public section

/-!
# A blocked `bar.sync` of the last generation steps

The last generation of named barrier 0 is joined by the default partition's `bar.sync 0` (source
ordinal `2 + #(bar.sync 0, 128)`) and the workers' (source ordinal 2), so "every participant has
made the arrival of the blocked thread's ordinal" is the wrong release criterion there. The
criterion is: *every lane of the CTA has made its last-generation arrival*, a `bar.sync` on the
barrier without a count of source ordinal at least `start` (`FinalArr`). If a lane has not, it is
pending (the `time` facts `hlag`, `hafter`) and earlier. Otherwise a maximal execution with the
same traces releases the thread (`NamedBar.sync_release_final`), given that the lanes of a warp
agree on the ordinal of their last-generation arrival (`hlock`, from `BarMismatch`) and that a
thread has one last-generation arrival (`hone`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
open Classical

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A last-generation arrival of thread `y`**: a `bar.sync` on `id` without a count whose source
ordinal is at least `start`. -/
def FinalArr (X : Execution) (id start y j : Nat) : Prop :=
  ∃ pc m, X.get (y, j) = some ⟨pc, .bar id none m⟩ ∧
    start ≤ ((X.tr y).take j).countP (Execution.isBarId id)

/-- **A blocked `bar.sync` of the last generation steps.** -/
theorem bar_steps_final {D : Finset Nat} {cD : Option Nat} {start nD id : Nat}
    (hD : D ⊆ Finset.range (CtaBarrier.warps L.block)) (hcard : D.card = nD)
    (hnD : nD ≠ CtaBarrier.warps L.block) (hcD : CtaBarrier.target L.block cD = .ok nD)
    (hS : NamedBar.PhSources L X D cD start id)
    (hG : NamedBar.Shape L none (Finset.range (CtaBarrier.warps L.block)) id)
    (hs : SafeGoal kernel asms L mem0) (hmax : Maximal L kernel asms mem0 X) {g pc : Nat}
    (hp : Frame.Pending L X g) (hnr : ¬ Step.Released L X g) (hlen : 0 < (X.tr g).length)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) id none pc)
    (hstartG : start ≤ ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id))
    (hone : ∀ j, FinalArr X id start g j → j = (X.tr g).length - 1)
    (hlock : ∀ y y' j j', y < L.threads → y' < L.threads → y / L.block = g / L.block →
      y' / L.block = g / L.block → y % L.block / 32 = y' % L.block / 32 →
      FinalArr X id start y j → FinalArr X id start y' j' →
      ((X.tr y).take j).countP (Execution.isBarId id) =
        ((X.tr y').take j').countP (Execution.isBarId id))
    {d : TSt} (hd : St Q L X g ((X.tr g).length - 1) = some (some d))
    (hafter : (∃ d', St Q L X g ((X.tr g).length - 1 + 1) = some (some d') ∧ T g d < T g d') ∨
      St Q L X g ((X.tr g).length - 1 + 1) = none)
    (hlag : ∀ y, y < L.threads → y / L.block = g / L.block → (∀ j, ¬ FinalArr X id start y j) →
      (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ Sched.threadTime (timed T Q L) X y ≤ T g d) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlen
  have hb : 0 < L.block := NamedBar.block_pos_of_thread_lt hg
  have hc := NamedBar.cta_lt hg
  have hgt : T g d < Sched.threadTime (timed T Q L) X g :=
    Sched.threadTime_after (M := timed T Q L) hlen hd hafter
  by_cases hA : ∃ y, y < L.block ∧ ∀ j, ¬ FinalArr X id start (g / L.block * L.block + y) j
  · obtain ⟨y, hy, hno⟩ := hA
    have hyt := NamedBar.cta_thread_lt hc hy
    have hdiv := (NamedBar.lane_cta (c := g / L.block) hb hy).1
    obtain ⟨hnx, hlt⟩ := hlag _ hyt hdiv hno
    exact Sched.earlier_steps hmax hnr (pending_of_noExit hX hyt hnx) (by omega)
  · push Not at hA
    -- every lane has a last-generation arrival; the lanes of a warp agree on its ordinal
    let Gw : Nat → Nat := fun w =>
      if h : ∃ j, FinalArr X id start (g / L.block * L.block + w * 32) j then
        ((X.tr (g / L.block * L.block + w * 32)).take h.choose).countP (Execution.isBarId id)
      else 0
    have hlane : ∀ y, y < L.block → ∃ j pc m,
        X.get (g / L.block * L.block + y, j) = some ⟨pc, .bar id none m⟩ ∧
        ((X.tr (g / L.block * L.block + y)).take j).countP (Execution.isBarId id) =
          Gw (y / 32) := by
      intro y hy
      obtain ⟨j, hj⟩ := hA y hy
      have hr : y / 32 * 32 < L.block := by omega
      have hex : ∃ j', FinalArr X id start (g / L.block * L.block + y / 32 * 32) j' := hA _ hr
      obtain ⟨pcj, mj, hget, hord0⟩ := hj
      refine ⟨j, pcj, mj, hget, ?_⟩
      have hGw : Gw (y / 32) = ((X.tr (g / L.block * L.block + y / 32 * 32)).take
          hex.choose).countP (Execution.isBarId id) := by
        simp only [Gw, hex, ↓reduceDIte]
      rw [hGw]
      have hyt := NamedBar.cta_thread_lt hc hy
      have hrt := NamedBar.cta_thread_lt hc hr
      have hdiv := (NamedBar.lane_cta (c := g / L.block) hb hy).1
      have hdivr := (NamedBar.lane_cta (c := g / L.block) hb hr).1
      have hmod := (NamedBar.lane_cta (c := g / L.block) hb hy).2
      have hmodr := (NamedBar.lane_cta (c := g / L.block) hb hr).2
      exact hlock _ _ _ _ hyt hrt hdiv hdivr (by rw [hmod, hmodr]; omega) ⟨pcj, mj, hget, hord0⟩
        hex.choose_spec
    have hgl : g % L.block < L.block := Nat.mod_lt _ hb
    have hgeq : g / L.block * L.block + g % L.block = g := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod g L.block
    have hFg : FinalArr X id start g ((X.tr g).length - 1) := ⟨pc, .sync, hlast, hstartG⟩
    have hGg : Gw (g % L.block / 32) =
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) := by
      have hr : g % L.block / 32 * 32 < L.block := by omega
      have hex : ∃ j', FinalArr X id start (g / L.block * L.block + g % L.block / 32 * 32) j' :=
        hA _ hr
      have hGw : Gw (g % L.block / 32) =
          ((X.tr (g / L.block * L.block + g % L.block / 32 * 32)).take
            hex.choose).countP (Execution.isBarId id) := by
        simp only [Gw, hex, ↓reduceDIte]
      rw [hGw]
      have hrt := NamedBar.cta_thread_lt hc hr
      have hdivr := (NamedBar.lane_cta (c := g / L.block) hb hr).1
      have hmodr := (NamedBar.lane_cta (c := g / L.block) hb hr).2
      exact hlock _ _ _ _ hrt hg hdivr rfl (by rw [hmodr]; omega) hex.choose_spec hFg
    have hstart : ∀ w ∈ Finset.range (CtaBarrier.warps L.block), start ≤ Gw w := by
      intro w hw
      have hwb := hG.bound w hw
      have hr : w * 32 < L.block := by omega
      have hex : ∃ j', FinalArr X id start (g / L.block * L.block + w * 32) j' := hA _ hr
      have hGw : Gw w = ((X.tr (g / L.block * L.block + w * 32)).take
          hex.choose).countP (Execution.isBarId id) := by
        simp only [Gw, hex, ↓reduceDIte]
      rw [hGw]
      obtain ⟨-, -, -, h2⟩ := hex.choose_spec
      exact h2
    obtain ⟨Y, hY, htr, hrel⟩ := NamedBar.sync_release_final hmax asms_wfStep
      (fun Y hY => fault_unsafe hs hY) hD hcard hnD hcD hS hG hg hlast hGg hstart hlane
      (fun j pc' m h1 h2 => hone j ⟨pc', m, h1, h2⟩)
    exact Sched.same_trace_steps hp hne hnr hY htr hrel

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
