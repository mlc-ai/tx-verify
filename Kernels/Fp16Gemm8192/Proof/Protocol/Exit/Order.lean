-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.RingRecords
public import Lemmas.Protocol.ClusterTrace
public import Lemmas.Kernel.ExitChain

@[expose] public section

/-! # The exit order

An event of a thread before its exit arrival happens before every exit in its cluster. The exit
wait of the exiting thread observes phase one, so every cluster thread's second arrival precedes
it. An event before a thread's second arrival is ordered before that arrival, and the arrival is
ordered before the exit wait, which is program-ordered before the exit. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow PTX.ClusterPhase PTX.ClusterTrace

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem clArrives_eq_countP (es : List Event) :
    clArrives es = es.countP ClusterTrace.isArr := rfl

/-- The exit wait of a trace prefix: its index lies before the prefix's end, and the thread
had exactly two cluster arrivals before it. -/
theorem exit_wait_of {T : List Event} {k : Nat} (h : ExitWaited (T.take k)) :
    ∃ j pc al, j < k ∧ T[j]? = some ⟨pc, .cluster (.wait al)⟩ ∧
      (T.take j).countP ClusterTrace.isArr = 2 := by
  obtain ⟨j, pc, al, hj, hc⟩ := h
  have hlen := (List.getElem?_eq_some_iff.mp hj).1
  simp only [List.length_take] at hlen
  have hjk : j < k := by omega
  refine ⟨j, pc, al, hjk, ?_, ?_⟩
  · rw [List.getElem?_take_of_lt hjk] at hj
    exact hj
  · have h1 : (T.take k).take j = T.take j := by
      rw [List.take_take, Nat.min_eq_left hjk.le]
    unfold clArrives at hc
    rw [h1] at hc
    exact hc

/-- An event that is not a cluster arrival is not counted as one. -/
theorem isArr_false_of_not {ev : Event} (hnot : ∀ rel al, ev.kind ≠ .cluster (.arrive rel al)) :
    ClusterTrace.isArr ev = false := by
  cases h : ClusterTrace.isArr ev with
  | false => rfl
  | true =>
    obtain ⟨rel, al, hk⟩ := ClusterTrace.isArr_kind h
    exact absurd hk (hnot rel al)

/-- A cluster arrival event of a thread releases. -/
theorem arrival_release {e : EvId} {pc : Nat} {rel al : Bool} (ht : ThreadFacts L X)
    (hX : Consistent L kernel Prod mem0 X)
    (hget : X.get e = some ⟨pc, .cluster (.arrive rel al)⟩) : rel = true := by
  have hg : e.1 < L.threads := Frame.lt_of_get hX (g := e.1) (k := e.2) hget
  obtain ⟨d, hd⟩ := Frame.event_state ht.sound hX ht.tracked hget nofun
  exact ((ht.cluster (g := e.1) (k := e.2) hg hget hd).2.1 rel al rfl).1

/-- An event of a thread with at most one cluster arrival up to it is before the thread's second
arrival. -/
theorem lt_of_second {e y z : EvId} {evY evZ : Event} (hy : X.get y = some evY)
    (hz : X.get z = some evZ) (hthY : y.1 = e.1) (hthZ : z.1 = e.1)
    (hYa : ClusterTrace.isArr evY = true) (hZa : ClusterTrace.isArr evZ = true) (hzy : z.2 < y.2)
    (hcount : ((X.tr e.1).take (e.2 + 1)).countP ClusterTrace.isArr ≤ 1) : e.2 < y.2 := by
  have hY' : (X.tr e.1)[y.2]? = some evY := by rw [← hthY]; exact hy
  have hZ' : (X.tr e.1)[z.2]? = some evZ := by rw [← hthZ]; exact hz
  by_contra hle
  have h1 := ClusterTrace.countP_take_lt (p := ClusterTrace.isArr) hzy hZ' hZa
  have h2 := ClusterTrace.countP_take_succ_of hY' hYa
  have h3 := ClusterTrace.countP_take_mono (xs := X.tr e.1) (p := ClusterTrace.isArr)
    (show y.2 + 1 ≤ e.2 + 1 by omega)
  omega

/-- **The exit arrival and wait, past an exit wait.** For an event `e` of a thread with at most one
cluster arrival up to it and an event `f` of its cluster made past its thread's exit wait: a release
arrival of `e`'s thread after `e` and the exit wait of `f`'s thread before `f` belong to one phase.
-/
theorem exitWaited_arrival (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {e f : EvId} {evf : Event}
    (hcount_e : ((X.tr e.1).take (e.2 + 1)).countP ClusterTrace.isArr ≤ 1)
    (hf : X.get f = some evf) (hEWf : ExitWaited ((X.tr f.1).take f.2))
    (hsame : SameCluster L e.1 f.1) :
    ∃ (y : EvId) (j : Nat), y.1 = e.1 ∧ e.2 < y.2 ∧
      ClusterBarrier.ArrivalOf L.block L.clusterSize.val
        (X.clusters (L.clusterOfCta (f.1 / L.block))) y 1 true ∧
      ClusterBarrier.WaitOf L.block L.clusterSize.val
        (X.clusters (L.clusterOfCta (f.1 / L.block))) (f.1, j) 1 ∧
      (∃ pc al, X.get (f.1, j) = some ⟨pc, .cluster (.wait al)⟩) ∧
      j < f.2 ∧ f.2 < (X.tr f.1).length := by
  have hfx : f.2 < (X.tr f.1).length := len_of_get hf
  have hone := hpre.oneDimLaunch.1
  have hsz : ∀ k, L.clusterSizeAt k = L.clusterSize.val := Launch.oneDim_clusterSizeAt hone
  have hcb := ClusterBlocking.of_consistent hX
  obtain ⟨j, pcj, alj, hjf, hwj, hcountj⟩ := exit_wait_of hEWf
  obtain ⟨c, hc⟩ : ∃ c, L.clusterOfCta (f.1 / L.block) = c := ⟨_, rfl⟩
  have hcE' : L.clusterOfCta (e.1 / L.block) = c := hsame.2.2.trans hc
  have hwget : X.get (f.1, j) = some ⟨pcj, .cluster (.wait alj)⟩ := hwj
  have hrecW : ClusterRecorded L X (f.1, j) :=
    hcb (f.1, j) pcj (.wait alj) hwget (by show j + 1 < (X.tr f.1).length; omega)
  obtain ⟨φ, i, s, t, cta, warp, lanes, lh, hi, hs, hwl, hφ, hp⟩ :=
    hX.cluster.waitOf_recorded hwget hrecW
  rw [hsz] at hs hp
  have hi' : (X.clusters c)[i]? = some (.wait cta warp lanes) := by
    rw [← hc]
    exact hi
  have hs' : ClusterBarrier.At L.block L.clusterSize.val (X.clusters c) i s := by
    rw [← hc]
    exact hs
  have hB : 0 < L.block := by
    rw [hpre.block]
    decide
  have hK : 0 < L.block * L.clusterSize.val := Nat.mul_pos hB L.clusterSize.pos
  -- the exit wait observes phase one
  have hφ1 : φ = 1 :=
    wait_phase_one hX.cluster hcb hX.object hc.symm hi' (by rw [hsz]; exact hs') hwl hφ
      (by rw [hsz]; exact hp) ⟨pcj, alj, hwget⟩ hcountj
  subst hφ1
  have hWait : ClusterBarrier.WaitOf L.block L.clusterSize.val (X.clusters c) (f.1, j) 1 :=
    ⟨i, s, t, cta, warp, lanes, lh, hi', hs', hwl, hφ, hp⟩
  -- the event's cluster coordinates
  have hsplit : e.1 = c * (L.block * L.clusterSize.val) + e.1 % (L.block * L.clusterSize.val) := by
    have := global_local_split L hone e.1
    rw [hcE'] at this
    exact this
  have hconc : ∃ (y : EvId) (pc : Nat) (al : Bool), y.1 = e.1 ∧ e.2 < y.2 ∧
      X.get y = some ⟨pc, .cluster (.arrive true al)⟩ ∧
      ClusterBarrier.ArrivalOf L.block L.clusterSize.val (X.clusters c) y 1 true := by
    by_cases hex : e.1 % (L.block * L.clusterSize.val) ∈ s.exited
    · -- the event's thread exited before the wait: its exit record is in the prefix
      have hs0 : ClusterBarrier.run L.block L.clusterSize.val {} ((X.clusters c).take i) =
          .done s := hs'
      rcases run_exited_source hs0 hex with h0 | ⟨xr, hxr⟩
      · simp at h0
      obtain ⟨qx, hqxi, hqx⟩ := exists_idx_of_mem_take hxr
      have hcl' : c < L.nclusters := by
        by_contra hn
        rw [hX.cluster.2.1 c (by omega)] at hi'
        simp at hi'
      have hsx := (hX.cluster.2.2 c hcl').2.1 _ (List.mem_of_getElem? hqx)
      obtain ⟨-, hxt0, pcx, hxget⟩ :
          e.1 % (L.block * L.clusterSize.val) < L.block * L.clusterSizeAt c ∧
            xr.1 = L.clusterStart c * L.block + e.1 % (L.block * L.clusterSize.val) ∧
            ∃ pc, X.get xr = some ⟨pc, .exit⟩ := hsx
      have hxt : xr.1 = c * (L.block * L.clusterSize.val) +
          e.1 % (L.block * L.clusterSize.val) := by
        rw [hxt0, Launch.oneDim_clusterStart hone, Nat.mul_assoc, Nat.mul_comm L.clusterSize.val]
      have hxget' : X.get (xr.1, xr.2) = some ⟨pcx, .exit⟩ := hxget
      have hthx : xr.1 < L.threads := Frame.lt_of_get hX hxget'
      obtain ⟨dx, hdx⟩ := Frame.event_state ht.sound hX ht.tracked hxget' nofun
      have hEWx := ((ht.cluster (g := xr.1) (k := xr.2) hthx hxget' hdx).2.2 rfl).2
      obtain ⟨j2, -, -, hj2, -, hcountx⟩ := exit_wait_of hEWx
      have hxM : xr.2 < (X.tr xr.1).length := len_of_get hxget'
      have hcount2 : 2 ≤ ((X.tr xr.1).take xr.2).countP ClusterTrace.isArr := by
        have := ClusterTrace.countP_take_mono (p := ClusterTrace.isArr) (xs := X.tr xr.1)
          (show j2 ≤ xr.2 by omega)
        omega
      have hxe : xr.1 = e.1 := by omega
      have hcx : c = L.clusterOfCta (xr.1 / L.block) := by
        rw [hxe, hcE']
      obtain ⟨a, rel, al, pca, ha1, ha2, hage, hA⟩ :=
        ClusterTrace.arrival_second hX.cluster hcb hX.object hcx hxM hcount2
      have hrel : rel = true := arrival_release ht hX hage
      subst hrel
      have hae : a.1 = e.1 := by omega
      obtain ⟨z, pcz, relz, alz, hz1, hz2, hzget⟩ :=
        ClusterTrace.prior_arrival hX.cluster hX.object hA
      have hlt : e.2 < a.2 :=
        lt_of_second hage hzget (by omega) (by omega)
          (ClusterTrace.isArr_of_kind rfl) (ClusterTrace.isArr_of_kind rfl) hz2 hcount_e
      exact ⟨a, pca, al, hae, hlt, hage, by rw [hsz] at hA; exact hA⟩
    · -- the event's thread is live at the wait: its phase-one arrival is recorded before it
      obtain ⟨y, rel0, hy1, hyA0⟩ := nth_arrival_before_wait hX.cluster hone hi' hs' hwl hφ hp
        (Nat.mod_lt _ hK) hex
      have hyA : ClusterBarrier.ArrivalOf L.block L.clusterSize.val (X.clusters c) y 1 rel0 := by
        have := hyA0.append (ys := (X.clusters c).drop i)
        rwa [List.take_append_drop] at this
      obtain ⟨pc0, al0, hget0⟩ := hX.cluster.arrival_present hyA
      have hrel0 : rel0 = true := arrival_release ht hX hget0
      subst hrel0
      have hy1' : y.1 = e.1 := by omega
      obtain ⟨z, pcz, relz, alz, hz1, hz2, hzget⟩ :=
        ClusterTrace.prior_arrival hX.cluster hX.object (by rw [hsz]; exact hyA)
      have hlt : e.2 < y.2 :=
        lt_of_second hget0 hzget (by omega) (by omega)
          (ClusterTrace.isArr_of_kind rfl) (ClusterTrace.isArr_of_kind rfl) hz2 hcount_e
      exact ⟨y, pc0, al0, hy1', hlt, hget0, hyA⟩
  obtain ⟨y, pc, al, hy1, hey, hyget, hyA⟩ := hconc
  rw [← hc] at hyA hWait
  exact ⟨y, j, hy1, hey, hyA, hWait, ⟨pcj, alj, hwget⟩, hjf, hfx⟩

/-- **The exit order, past an exit wait.** An event of a thread with at most one cluster arrival up
to it happens before every event of its cluster made past its thread's exit wait. -/
theorem exitWaited_order (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {e f : EvId} {evf : Event}
    (hcount_e : ((X.tr e.1).take (e.2 + 1)).countP ClusterTrace.isArr ≤ 1)
    (hf : X.get f = some evf) (hEWf : ExitWaited ((X.tr f.1).take f.2))
    (hsame : SameCluster L e.1 f.1) : baseCausality L X e f := by
  obtain ⟨y, j, hy1, hey, hyA, hWait, -, hjf, hfx⟩ :=
    exitWaited_arrival hpre hX ht hcount_e hf hEWf hsame
  exact baseCausality_of_arrival_wait hX.cluster hpre.oneDimLaunch.1 hsame hyA hy1 hey hWait rfl
    hjf hfx

/-- **The exit dependency, past an exit wait.** A successful poll of a thread with at most one
cluster arrival up to it precedes, in the dependency order, every event of its cluster made past
its thread's exit wait: the poll's return resumes the thread's exit arrival, which the exit wait
observes. -/
theorem exitWaited_enables (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {w f : EvId} {evf : Event} {pc q : Nat} {m : Loc} {acq : Bool}
    {sc : MbarScope} (hw : X.get w = some ⟨pc, .wait m q true acq sc⟩)
    (hcount_w : ((X.tr w.1).take (w.2 + 1)).countP ClusterTrace.isArr ≤ 1)
    (hf : X.get f = some evf) (hEWf : ExitWaited ((X.tr f.1).take f.2))
    (hsame : SameCluster L w.1 f.1) :
    Relation.TransGen (DepStep L kernel X) (.thread w, true) (.thread f, false) := by
  obtain ⟨y, j, hy1, hwy, hyA, hWait, ⟨pcj, alj, hwj⟩, hjf, hfx⟩ :=
    exitWaited_arrival hpre hX ht hcount_w hf hEWf hsame
  obtain ⟨apc, aal, hage⟩ := hX.cluster.arrival_present hyA
  have hyl : y.2 < (X.tr y.1).length := len_of_get hage
  obtain ⟨ex, hspin⟩ := ht.wait_spins (Frame.lt_of_get hX hw) hw
  have hres : Resumes kernel X w y := Resumes.of_spin hw hspin hy1.symm hwy hyl
  have hsz := Launch.oneDim_clusterSizeOf hpre.oneDimLaunch.1 (f.1 / L.block)
  exact depStep_of_arrival_wait hres hwj (by rw [hsz]; exact hyA) (by rw [hsz]; exact hWait) rfl
    hjf hfx

/-- **The exit order.** An event of a thread before its exit arrival, other than a cluster
arrival, happens before every exit in its cluster. -/
theorem exitOrder (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : ExitOrder L X := by
  intro e f ev d pcf hev hd hcl hnot hf hsame
  have hg : e.1 < L.threads := Frame.lt_of_get hX hev
  have hh : f.1 < L.threads := Frame.lt_of_get hX hf
  obtain ⟨hcE, -, -⟩ := ht.cluster (g := e.1) (k := e.2) hg hev hd
  have hcount_e : ((X.tr e.1).take (e.2 + 1)).countP ClusterTrace.isArr ≤ 1 := by
    rw [ClusterTrace.countP_take_succ_not (show (X.tr e.1)[e.2]? = some ev from hev)
      (isArr_false_of_not hnot), ← clArrives_eq_countP, hcE]
    exact hcl
  obtain ⟨df, hdf⟩ := Frame.event_state ht.sound hX ht.tracked hf nofun
  exact exitWaited_order hpre hX ht hcount_e hf
    ((ht.cluster (g := f.1) (k := f.2) hh hf hdf).2.2 rfl).2 hsame

/-- **The exit dependency.** A successful poll of a thread before its exit arrival precedes, in
the dependency order, every exit in its cluster. -/
theorem exitEnables (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {w f : EvId} {d : ThreadD} {pc q pcf : Nat} {m : Loc} {acq : Bool}
    {sc : MbarScope} (hw : X.get w = some ⟨pc, .wait m q true acq sc⟩)
    (hd : Frame.stateAt (code L) X w.1 w.2 = some (some d)) (hcl : d.clPhase ≤ 1)
    (hf : X.get f = some ⟨pcf, .exit⟩) (hsame : SameCluster L w.1 f.1) :
    Relation.TransGen (DepStep L kernel X) (.thread w, true) (.thread f, false) := by
  have hg : w.1 < L.threads := Frame.lt_of_get hX hw
  have hh : f.1 < L.threads := Frame.lt_of_get hX hf
  obtain ⟨hcE, -, -⟩ := ht.cluster (g := w.1) (k := w.2) hg hw hd
  have hcount_w : ((X.tr w.1).take (w.2 + 1)).countP ClusterTrace.isArr ≤ 1 := by
    rw [ClusterTrace.countP_take_succ_not (show (X.tr w.1)[w.2]? = some _ from hw)
      (isArr_false_of_not (fun rel al h => by cases h)), ← clArrives_eq_countP, hcE]
    exact hcl
  obtain ⟨df, hdf⟩ := Frame.event_state ht.sound hX ht.tracked hf nofun
  exact exitWaited_enables hpre hX ht hw hcount_w hf
    ((ht.cluster (g := f.1) (k := f.2) hh hf hdf).2.2 rfl).2 hsame
