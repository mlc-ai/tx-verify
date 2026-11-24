-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.Exit.Order

@[expose] public section

/-! # Once a thread of a cluster has exited, every thread of it has made both arrivals

A thread's exit follows its exit wait on the cluster barrier, which observes phase one. The wait
completes only after every live lane of the cluster has a phase-one arrival recorded before it
(`nth_arrival_before_wait`), and a lane that exited before the wait has its own exit wait on its
trace (`ThreadFacts.cluster`). Two arrival records of a lane are two cluster arrivals of its thread
(`prior_arrival`), and a thread never has more than two (`clArrives_take_le`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow PTX.ClusterPhase PTX.ClusterTrace

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A thread has at most two cluster arrivals on every prefix of its trace. -/
theorem clArrives_take_le (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g : Nat}
    (hg : g < L.threads) (k : Nat) :
    clArrives ((X.tr g).take k) ≤ 2 := by
  induction k with
  | zero => simp [clArrives]
  | succ k ih =>
    rw [clArrives_eq_countP] at ih ⊢
    cases hr : (X.tr g)[k]? with
    | none =>
      rw [List.take_add_one, hr]
      simpa using ih
    | some e =>
      by_cases ha : ClusterTrace.isArr e = true
      · obtain ⟨rel, al, hk⟩ := ClusterTrace.isArr_kind ha
        have hget : X.get (g, k) = some e := hr
        obtain ⟨d, hd⟩ :=
          Frame.event_state ht.sound hX ht.tracked hget (by rintro pc f rfl; cases hk)
        have hcl := ht.cluster (g := g) (k := k) hg hget hd
        have hcl' : clArrives ((X.tr g).take k) = d.clPhase := hcl.1
        have hle : d.clPhase ≤ 1 := (hcl.2.1 rel al hk).2
        rw [clArrives_eq_countP] at hcl'
        rw [ClusterTrace.countP_take_succ_of hr ha]
        omega
      · rw [ClusterTrace.countP_take_succ_not hr (by simpa using ha)]
        exact ih

/-- Two arrival records of a thread, at positions `a < b` of its trace, are two of its cluster
arrivals. -/
theorem two_of_arrivals {g a b : Nat} {ea eb : Event} (hab : a < b)
    (ha : (X.tr g)[a]? = some ea) (hb : (X.tr g)[b]? = some eb)
    (hpa : ClusterTrace.isArr ea = true) (hpb : ClusterTrace.isArr eb = true) :
    2 ≤ clArrives (X.tr g) := by
  rw [clArrives_eq_countP]
  have hlt : b < (X.tr g).length := (List.getElem?_eq_some_iff.mp hb).1
  have h1 := ClusterTrace.countP_take_lt (xs := X.tr g) (p := ClusterTrace.isArr) hab ha hpa
  have h2 := ClusterTrace.countP_take_succ_of hb hpb
  have h3 := ClusterTrace.countP_take_mono (xs := X.tr g) (p := ClusterTrace.isArr)
    (show b + 1 ≤ (X.tr g).length by omega)
  rw [List.take_length] at h3
  omega

/-- A completed exit wait of a thread gives every thread of its cluster two cluster arrivals. -/
theorem two_arrivals_of_wait (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {h j pcj : Nat} {alj : Bool}
    (hwget : X.get (h, j) = some ⟨pcj, .cluster (.wait alj)⟩) (hjl : j + 1 < (X.tr h).length)
    (hcountj : ((X.tr h).take j).countP ClusterTrace.isArr = 2)
    {g : Nat} (hsame : L.clusterOfCta (g / L.block) = L.clusterOfCta (h / L.block)) :
    2 ≤ clArrives (X.tr g) := by
  have hB : 0 < L.block := by
    rw [hpre.block]
    decide
  have hK : 0 < L.block * L.clusterSize.val := Nat.mul_pos hB L.clusterSize.pos
  have hone := hpre.oneDimLaunch.1
  have hsz : ∀ k, L.clusterSizeAt k = L.clusterSize.val := Launch.oneDim_clusterSizeAt hone
  have hcb := ClusterBlocking.of_consistent hX
  have hrecW : ClusterRecorded L X (h, j) :=
    hcb (h, j) pcj (.wait alj) hwget (by show j + 1 < (X.tr h).length; exact hjl)
  obtain ⟨φ, i, s, t, cta, warp, lanes, lh, hi, hs, hwl, hφ, hp⟩ :=
    hX.cluster.waitOf_recorded hwget hrecW
  rw [hsz] at hs hp
  obtain ⟨c, hc⟩ : ∃ c, L.clusterOfCta (h / L.block) = c := ⟨_, rfl⟩
  have hi' : (X.clusters c)[i]? = some (.wait cta warp lanes) := by
    rw [← hc]
    exact hi
  have hs' : ClusterBarrier.At L.block L.clusterSize.val (X.clusters c) i s := by
    rw [← hc]
    exact hs
  -- the exit wait observes phase one
  have hφ1 : φ = 1 :=
    wait_phase_one hX.cluster hcb hX.object hc.symm hi' (by rw [hsz]; exact hs') hwl hφ
      (by rw [hsz]; exact hp) ⟨pcj, alj, hwget⟩ hcountj
  subst hφ1
  have hgc : L.clusterOfCta (g / L.block) = c := hsame.trans hc
  have hsplit : g = c * (L.block * L.clusterSize.val) + g % (L.block * L.clusterSize.val) := by
    have := global_local_split L hone g
    rw [hgc] at this
    exact this
  have hcl' : c < L.nclusters := by
    by_contra hn
    rw [hX.cluster.2.1 c (by omega)] at hi'
    simp at hi'
  by_cases hex : g % (L.block * L.clusterSize.val) ∈ s.exited
  · -- the lane exited before the wait: its exit event is on its own trace, after its exit wait
    have hs0 : ClusterBarrier.run L.block L.clusterSize.val {} ((X.clusters c).take i) =
        .done s := hs'
    rcases run_exited_source hs0 hex with h0 | ⟨xr, hxr⟩
    · simp at h0
    obtain ⟨qx, hqxi, hqx⟩ := ClusterTrace.exists_idx_of_mem_take hxr
    have hsx := (hX.cluster.2.2 c hcl').2.1 _ (List.mem_of_getElem? hqx)
    obtain ⟨-, hxt0, pcx, hxget⟩ : g % (L.block * L.clusterSize.val) < L.block * L.clusterSizeAt c ∧
        xr.1 = L.clusterStart c * L.block + g % (L.block * L.clusterSize.val) ∧
        ∃ pc, X.get xr = some ⟨pc, .exit⟩ := hsx
    have hxt : xr.1 = c * (L.block * L.clusterSize.val) + g % (L.block * L.clusterSize.val) := by
      rw [hxt0, Launch.oneDim_clusterStart hone, Nat.mul_assoc, Nat.mul_comm L.clusterSize.val]
    have hxget' : X.get (xr.1, xr.2) = some ⟨pcx, .exit⟩ := hxget
    have hthx : xr.1 < L.threads := Frame.lt_of_get hX hxget'
    obtain ⟨dx, hdx⟩ := Frame.event_state ht.sound hX ht.tracked hxget' nofun
    have hEWx := ((ht.cluster (g := xr.1) (k := xr.2) hthx hxget' hdx).2.2 rfl).2
    obtain ⟨j2, -, -, hj2, -, hcountx⟩ := exit_wait_of hEWx
    have hxM : xr.2 < (X.tr xr.1).length := len_of_get hxget'
    have hxe : xr.1 = g := hxt.trans hsplit.symm
    rw [← hxe, clArrives_eq_countP]
    have h3 := ClusterTrace.countP_take_mono (xs := X.tr xr.1) (p := ClusterTrace.isArr)
      (show j2 ≤ (X.tr xr.1).length by omega)
    rw [List.take_length] at h3
    omega
  · -- the lane is live at the wait: its phase-one arrival is recorded before the wait
    obtain ⟨y, rel0, hy1, hyA0⟩ := nth_arrival_before_wait hX.cluster hone hi' hs' hwl hφ hp
      (Nat.mod_lt g hK) hex
    have hyA : ClusterBarrier.ArrivalOf L.block L.clusterSize.val (X.clusters c) y 1 rel0 := by
      have := hyA0.append (ys := (X.clusters c).drop i)
      rwa [List.take_append_drop] at this
    obtain ⟨pc0, al0, hget0⟩ := hX.cluster.arrival_present hyA
    have hrel0 : rel0 = true := arrival_release ht hX hget0
    subst hrel0
    obtain ⟨z, pcz, relz, alz, hz1, hz2, hzget⟩ := prior_arrival hX.cluster hX.object
      (by rw [hsz]; exact hyA)
    have hyg : y.1 = g := hy1.trans hsplit.symm
    have hzg : z.1 = g := hz1.trans hyg
    have hyR : (X.tr g)[y.2]? = some ⟨pc0, .cluster (.arrive true al0)⟩ :=
      trace_get hyg hget0
    have hzR : (X.tr g)[z.2]? = some ⟨pcz, .cluster (.arrive relz alz)⟩ :=
      trace_get hzg hzget
    exact two_of_arrivals hz2 hzR hyR (isArr_of_kind rfl) (isArr_of_kind rfl)

/-- **Every thread of a cluster has made both its cluster arrivals once a thread of it has
exited.** -/
theorem clusterExitAll (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : ClusterExitAll L X := by
  intro h pc hh hlast g hg hsame
  have hne : X.tr h ≠ [] := by
    intro he
    rw [he] at hlast
    simp at hlast
  have hget : X.get (h, (X.tr h).length - 1) = some ⟨pc, .exit⟩ := by
    change (X.tr h)[(X.tr h).length - 1]? = _
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  have hpos : 0 < (X.tr h).length := List.length_pos_of_ne_nil hne
  obtain ⟨d, hd⟩ := Frame.event_state ht.sound hX ht.tracked hget nofun
  have hEW := ((ht.cluster (g := h) (k := (X.tr h).length - 1) hh hget hd).2.2 rfl).2
  obtain ⟨j, pcj, alj, hjk, hwj, hcountj⟩ := exit_wait_of hEW
  have hwget : X.get (h, j) = some ⟨pcj, .cluster (.wait alj)⟩ := hwj
  have h2 := two_arrivals_of_wait hpre hX ht hwget (by omega) hcountj hsame
  have h3 := clArrives_take_le hX ht hg (X.tr g).length
  rw [List.take_length] at h3
  omega

end
end PTX.Kernels.Fp16Gemm8192.Proof
