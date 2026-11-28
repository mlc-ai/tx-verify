-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Export.BarLoop
public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.Export.BarVisit
import Kernels.InklingRelDecode.Proof.Protocol.Shared.RescaleInduction
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchLater
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchExit
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Kernels.InklingRelDecode.Proof.Lib.BarZero
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleChain
import Lemmas.Flow.NthEv

@[expose] public section

/-! # The loop generations of barrier 0: a data lane with no more events is no later

The data lanes of a CTA agree on which of their barrier-zero events are optional rendezvous
(`Uniform`, from `rescale_agree`). So a lane with no more barrier-zero events than a lane at a
half-CTA rendezvous has no more fixed ones either, and no more optional ones than it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Bar
open PTX PTX.Flow PTX.Sched Protocol.Shared Export

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The optional rendezvous of a prefix, by ordinal: the lane with fewer barrier-zero events has
the optional rendezvous of the other's earlier ones, and the others in its window. -/
private theorem window {x y jx jy : Nat}
    (hle : ((X.tr y).take jy).countP (Execution.isBarId 0) ≤
      ((X.tr x).take jx).countP (Execution.isBarId 0))
    (same : ∀ n < ((X.tr x).take jx).countP (Execution.isBarId 0),
      ordEv X (Execution.isBarId 0) rescaleBar y n = ordEv X (Execution.isBarId 0) rescaleBar x n) :
    ∃ W, ((X.tr x).take jx).countP rescaleBar = ((X.tr y).take jy).countP rescaleBar + W ∧
      W ≤ ((X.tr x).take jx).countP (Execution.isBarId 0) -
        ((X.tr y).take jy).countP (Execution.isBarId 0) ∧
      (W = ((X.tr x).take jx).countP (Execution.isBarId 0) -
        ((X.tr y).take jy).countP (Execution.isBarId 0) →
        ∀ n, ((X.tr y).take jy).countP (Execution.isBarId 0) ≤ n →
          n < ((X.tr x).take jx).countP (Execution.isBarId 0) →
          ordEv X (Execution.isBarId 0) rescaleBar x n = true) := by
  have hq : ∀ e, rescaleBar e = true → Execution.isBarId 0 e = true := fun e h => by
    simpa [rescaleBar] using (Bool.and_eq_true_iff.mp h).1
  rw [countP_ordinal hq, countP_ordinal hq]
  generalize ((X.tr x).take jx).countP (Execution.isBarId 0) = Nx at *
  generalize ((X.tr y).take jy).countP (Execution.isBarId 0) = Ny at *
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [List.range_add, List.countP_append]
  have eq : (List.range Ny).countP (ordEv X (Execution.isBarId 0) rescaleBar y) =
      (List.range Ny).countP (ordEv X (Execution.isBarId 0) rescaleBar x) :=
    List.countP_congr fun n hn => by rw [same n (by have := List.mem_range.mp hn; omega)]
  refine ⟨(List.range d).countP (fun k => ordEv X (Execution.isBarId 0) rescaleBar x (Ny + k)),
    by rw [eq, List.countP_map]; rfl, ?_, fun hW n h1 h2 => ?_⟩
  · rw [Nat.add_sub_cancel_left]
    exact List.countP_le_length.trans (by simp)
  · rw [Nat.add_sub_cancel_left] at hW
    have all := List.countP_eq_length.mp (hW.trans (by simp))
    have := all (n - Ny) (List.mem_range.mpr (by omega))
    simpa [Nat.add_sub_cancel' h1] using this

/-- **Two visits of the optional rendezvous are not at consecutive ordinals of a lane**, when the
earlier ordinal's event is a visit by the lane's agreement with another. -/
private theorem consecutive {Q L m X g j k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (nug : NoUbLane X g)
    (he : X.get (g, j) = some ⟨2326, k⟩)
    (hN : 1 ≤ ((X.tr g).take j).countP (Execution.isBarId 0))
    (hv : ordEv X (Execution.isBarId 0) rescaleBar g
      (((X.tr g).take j).countP (Execution.isBarId 0) - 1) = true) : False := by
  obtain ⟨i1, e1, hlt, get1, bar1, cnt1⟩ := exists_nthEv (X := X) (p := Execution.isBarId 0)
    (g := g) (k := j) (n := ((X.tr g).take j).countP (Execution.isBarId 0) - 1) (by omega)
  have eq := ordEv_eq (q := rescaleBar) get1 bar1
  rw [cnt1, hv] at eq
  have pc : e1.pc = 2326 := by
    simpa [rescaleBar] using (Bool.and_eq_true_iff.mp eq.symm).2
  obtain ⟨p1, k1⟩ := e1
  change p1 = 2326 at pc
  subst pc
  exact no_two_visits hp hX hf nug get1 he hlt (by omega)

/-- The comparison of a data lane's prefix with a half-CTA rendezvous of another, with no more
barrier-zero events: no later, and equal only at the rendezvous's site with the whole window of
ordinals between them optional. -/
private theorem lag_at {g j y pc t} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (safe : ¬Race L X)
    (nu : ∀ y, NoUbLane X y) (hy : y < L.threads) (cta : y / L.block = g / L.block)
    (lg : g % L.block < 128) (ly : y % L.block < 128)
    (he : X.get (g, j) = some ⟨pc, .bar 0 (some 128) .sync⟩) (hh : pc ∈ BarRow.halfZeroSites)
    (same : ∀ n < ((X.tr g).take j).countP (Execution.isBarId 0),
      ordEv X (Execution.isBarId 0) rescaleBar y n = ordEv X (Execution.isBarId 0) rescaleBar g n)
    (ht : t ≤ (X.tr y).length) (hal : TcAlive Q L X y t)
    (hN : ((X.tr y).take t).countP (Execution.isBarId 0) ≤
      ((X.tr g).take j).countP (Execution.isBarId 0)) :
    timeAt (schedule Q L) X y t ≤ timeAt (schedule Q L) X g j ∧
      (timeAt (schedule Q L) X y t = timeAt (schedule Q L) X g j →
        (∀ e, X.get (y, t) = some e → e.pc = pc) ∧
        ∀ n, ((X.tr y).take t).countP (Execution.isBarId 0) ≤ n →
          n < ((X.tr g).take j).countP (Execution.isBarId 0) →
          ordEv X (Execution.isBarId 0) rescaleBar g n = true) := by
  obtain ⟨W, hW1, hW2, hW3⟩ := window hN same
  have vy := count_rescale_nu hp hX ((nu y).before t)
  have vg := count_rescale hp hX he
  have hV : ((X.tr y).take t).countP (Execution.isBarId 0) +
        ((X.tr g).take j).countP (fun e => e.pc == 2326) ≤
      ((X.tr g).take j).countP (Execution.isBarId 0) +
        ((X.tr y).take t).countP (fun e => e.pc == 2326) := by
    rw [vy, vg]; omega
  rcases loop_cmp hp hX hf hy (nu y) cta ly he hh ht hal hV with ⟨l1, l2⟩ | ⟨p2326, eq, post⟩
  · refine ⟨l1, fun h => ?_⟩
    obtain ⟨e1, e2⟩ := l2 h
    rw [vy, vg] at e2
    exact ⟨e1, hW3 (by omega)⟩
  · exfalso
    subst p2326
    rw [vy, vg] at eq
    have hW : W = ((X.tr g).take j).countP (Execution.isBarId 0) -
        ((X.tr y).take t).countP (Execution.isBarId 0) := by omega
    have nug := nu g
    by_cases lt : ((X.tr y).take t).countP (Execution.isBarId 0) <
        ((X.tr g).take j).countP (Execution.isBarId 0)
    · refine consecutive hp hX hf nug he (by omega) ?_
      exact hW3 hW _ (by omega) (by omega)
    · have heq : ((X.tr y).take t).countP (Execution.isBarId 0) =
          ((X.tr g).take j).countP (Execution.isBarId 0) := by omega
      rcases post with ⟨u, kd, gu, hc⟩ | ⟨v, a, b, c, r, ok, gv, skip, cv⟩
      · have bar : Execution.isBarId 0 ⟨2326, kd⟩ = true := by
          rw [Lib.zero_event hX hp.block gu ((nu y).kind gu)]
          show Lib.zeroSite 2326 = true
          decide +kernel
        have o := ordEv_eq (q := rescaleBar) gu bar
        have n1 : ((X.tr y).take u).countP (Execution.isBarId 0) =
            ((X.tr g).take j).countP (Execution.isBarId 0) - 1 := by omega
        rw [n1] at o
        have o' : ordEv X (Execution.isBarId 0) rescaleBar y
            (((X.tr g).take j).countP (Execution.isBarId 0) - 1) = true := by
          rw [o]; simp [rescaleBar, bar]
        refine consecutive hp hX hf nug he (by omega) ?_
        rw [← same _ (by omega)]
        exact o'
      · obtain ⟨kx, ax, bx, cx, recv, okx, hk, gsx, skipF, cnt⟩ := Softmax.Export.rescale_source
          hp hX he
        have uni : ∀ {x kx ax bx cx rx okx},
            X.get (x, kx) = some ⟨2255, .shfl .bfly ax bx cx rx okx⟩ → x % L.block < 128 →
            Uniform L X (x / L.block) (barOrdinal X x kx) := fun gs lane =>
          rescale_agree hp hX hf safe gs (fun _ => nofun)
            (by show Lib.afterFinal 2255 = 0; decide) (by show Lib.finalSync 2255 = false; decide)
            lane
        have uniX := uni gsx lg
        have uniY := uni gv ly
        have agree := decision_agree hp hX hf safe gsx gv lg ly cta
          (by simp only [barOrdinal] at cnt ⊢; omega)
          (fun h' ch lh n' lt => uniX h' g ch lh rfl lg n'
            (by simp only [barOrdinal] at lt ⊢; omega))
          (fun h' ch lh n' lt => uniY h' y ch lh rfl ly n'
            (by simp only [barOrdinal] at lt ⊢; omega))
        rw [skipF, skip] at agree
        exact Bool.noConfusion agree

private theorem half_early : ∀ p ∈ BarRow.halfZeroSites,
    Lib.afterFinal p = 0 ∧ Lib.finalSync p = false ∧ Lib.zeroSite p = true := by decide

/-- **A data lane with no more barrier-zero events than precede a half-CTA rendezvous has not
exited and is no later than it.** -/
public theorem loop_lag {g j y pc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (safe : ¬Race L X)
    (nu : ∀ y, NoUbLane X y) (hy : y < L.threads) (cta : y / L.block = g / L.block)
    (lg : g % L.block < 128) (ly : y % L.block < 128)
    (he : X.get (g, j) = some ⟨pc, .bar 0 (some 128) .sync⟩)
    (hle : (X.tr y).countP (Execution.isBarId 0) ≤
      ((X.tr g).take j).countP (Execution.isBarId 0)) :
    (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧
      threadTime (schedule Q L) X y ≤ timeAt (schedule Q L) X g j := by
  have hh : pc ∈ BarRow.halfZeroSites := by
    obtain ⟨_, r⟩ := Lib.recorded_bar hX hp.block he
    rcases r with one | full | half
    · cases one.1
    · exact absurd full.2.1 (by simp)
    · exact half.2.2
  obtain ⟨early, other, zero⟩ := half_early pc hh
  have uni := rescale_agree hp hX hf safe he (by simp) early other lg
  have same : ∀ n < ((X.tr g).take j).countP (Execution.isBarId 0),
      ordEv X (Execution.isBarId 0) rescaleBar y n =
        ordEv X (Execution.isBarId 0) rescaleBar g n :=
    fun n hn => uni y g cta ly rfl lg n hn
  refine ⟨fun k pc' ex => ?_, ?_⟩
  · have lt := exit_ordinal hp hX he (by simp) early other ex lg ly cta.symm
    have := List.Sublist.countP_le (p := Execution.isBarId 0) (List.take_sublist k (X.tr y))
    simp only [barOrdinal] at lt
    omega
  · rw [Sched.threadTime_eq_timeAt]
    rcases tc_time_cases hf hy (X.tr y).length with hal | h0 | ⟨hpos, hal, hteq⟩
    · exact (lag_at hp hX hf safe nu hy cta lg ly he hh same le_rfl hal
        (by rwa [List.take_length])).1
    · rw [h0]; exact Nat.zero_le _
    · have hN' : ((X.tr y).take ((X.tr y).length - 1)).countP (Execution.isBarId 0) ≤
          ((X.tr g).take j).countP (Execution.isBarId 0) :=
        (List.Sublist.countP_le (List.take_sublist _ _)).trans (by simpa using hle)
      obtain ⟨l1, l2⟩ := lag_at hp hX hf safe nu hy cta lg ly he hh same (by omega) hal hN'
      rw [hteq]
      by_cases hlt : timeAt (schedule Q L) X y ((X.tr y).length - 1) <
          timeAt (schedule Q L) X g j
      · omega
      · obtain ⟨pcs, win⟩ := l2 (by omega)
        obtain ⟨ev, gev⟩ : ∃ ev, X.get (y, (X.tr y).length - 1) = some ev :=
          ⟨_, List.getElem?_eq_getElem (show (X.tr y).length - 1 < (X.tr y).length by omega)⟩
        have evpc := pcs ev gev
        have bar : Execution.isBarId 0 ev = true := by
          rw [Lib.zero_event hX hp.block gev ((nu y).kind gev), evpc]
          exact zero
        have step := countP_take_succ (p := Execution.isBarId 0) gev bar
        rw [Nat.sub_add_cancel (by omega), List.take_length] at step
        have all := win _ le_rfl (by omega)
        have o := ordEv_eq (q := rescaleBar) gev bar
        rw [same _ (by omega), all] at o
        have p2326 : pc = 2326 := by
          have h2 : (Execution.isBarId 0 ev && ev.pc == 2326) = true := o.symm
          have h3 := beq_iff_eq.mp ((Bool.and_eq_true _ _).mp h2).2
          rw [← evpc]; exact h3
        subst p2326
        exfalso
        exact consecutive hp hX hf (nu g) he (by omega) (win _ (by omega) (by omega))

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Bar
