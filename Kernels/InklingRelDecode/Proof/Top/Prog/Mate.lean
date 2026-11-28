-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.Classes
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Lemmas.Kernel.Progress.WarpReady
import Lemmas.Tcgen05.TcCollectiveOrdinaryWaiting
import Lemmas.Snoc.SnocAsync

/-! # A released lane of a warp releases a lane that made no fewer events of the same blocking kind

A `bar.sync` is recorded by its warp's arrival, a warp-collective `tcgen05` event waits for every
lane of its warp: the lane with the released one's ordinal event is released with it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow

variable {L : Launch} {m : Mem0} {X : Execution} {x y : Nat}

/-- A blocking event of a lane is ready when the lane has a later event or is released. -/
public theorem Prog.ready_of_count (hX : Consistent L kernel Assumptions.all m X) {j : Nat}
    {e : Event} (hj : X.get (x, j) = some e) (hb : e.kind.resume = .blocking false)
    (hrel : Step.Released L X x) : Ready L X (x, j) := by
  have hl : j < (X.tr x).length := (List.getElem?_eq_some_iff.mp hj).1
  rcases Nat.lt_or_ge (j + 1) (X.tr x).length with h1 | h1
  · refine hX.dependency.ready _ ?_
    simp only [Returned, hj]
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp_all [Kind.resume]
  · obtain rfl : j = (X.tr x).length - 1 := by omega
    exact hrel.ready _ _ hj hb

/-- **A lane with a barrier event that has made no fewer events on the barrier than a released
lane of its warp is released.** -/
public theorem Prog.mate_bar (hX : Consistent L kernel Assumptions.all m X) (hb : L.block = 256)
    (hsw : SameWarp L x y) {id pc : Nat} {c : Option Nat}
    (hy : X.get (y, (X.tr y).length - 1) = some ⟨pc, .bar id c .sync⟩)
    (hn : ((X.tr y).take ((X.tr y).length - 1)).countP (Execution.isBarId id) <
      (X.tr x).countP (Execution.isBarId id))
    (hrel : Step.Released L X x) : Step.Released L X y := by
  obtain ⟨j, ex, hj, hq, ho⟩ := NamedBar.exists_ordinal (Execution.isBarId id) (X.tr x) hn
  obtain ⟨px, kx⟩ := ex
  have hex : X.get (x, j) = some ⟨px, kx⟩ := hj
  have hkx : ∃ cx mx, kx = .bar id cx mx := by
    simp only [Execution.isBarId] at hq
    cases kx <;> simp at hq
    case bar id' cx mx => exact ⟨cx, mx, by rw [hq]⟩
  obtain ⟨cx, mx, rfl⟩ := hkx
  obtain ⟨rfl, -⟩ := Lib.recorded_bar hX hb hex
  have rdy := Prog.ready_of_count hX hex rfl hrel
  have hnx : ∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩ := by
    intro k pc' hk
    have := Execution.exit_last hX hsw.1.2.1 hk
    have hl : k = (X.tr y).length - 1 := by omega
    rw [hl, hy] at hk
    cases hk
  have := Sched.bar_ready_lane hX hsw.1.1 hsw hex rdy hy (by simpa using ho.symm) hnx
  exact ⟨fun _ _ hget _ => by rw [hy] at hget; cases hget; exact this⟩

/-- **A released event's lanes**: every lane of its warp has made the event of its ordinal. -/
public theorem Prog.tc_all {j k pc : Nat} {t : TcKind} (hsw : SameWarp L x y)
    (he : X.get (x, j) = some ⟨pc, .tc t⟩) (hc : isTcColl ⟨pc, .tc t⟩ = true)
    (hk : X.TcK (x, j) k) (hr : Ready L X (x, j)) :
    ∀ h, h < L.threads → SameWarp L y h → ∃ j', X.TcK (h, j') k := by
  intro h' _ hw'
  have hw : SameWarp L h' x := sameWarp_symm (Step.sameWarp_trans hsw hw')
  obtain ⟨z, -, i, rfl, hi⟩ := hr (.node _) (tcNeed_mem he hc
    (mem_warpLanes_of_sameWarp hw))
  exact ⟨i, hk.2 ▸ hi⟩
