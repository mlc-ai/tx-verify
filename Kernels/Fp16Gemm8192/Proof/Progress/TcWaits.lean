-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.BarLag
public import Kernels.Fp16Gemm8192.Proof.Progress.BarPart
public import Kernels.Fp16Gemm8192.Proof.Progress.ClusterWaits
public import Kernels.Fp16Gemm8192.Proof.Progress.TcTime
public import Lemmas.Step.Issue

@[expose] public section

/-! # Progress at a blocked warp-collective `tcgen05` wait

A pending consumer whose last event is a Tensor Memory load or the wait for one (a data event) that
is not released. The event is its `k`-th warp-collective `tcgen05` event, so what it lacks to be
ready is that every lane of its warp has executed its `k`-th collective (`tcNeeds`, DEP-ORDER).
Some lane of the warp has made at most `k` collectives (`tc_lane`). The lane is a thread of the
cluster of the thread, which has not exited, so it is not canceled and pending. Its next event is
earlier in the rank table:

* in the prologue or at the register request it is before every task;
* in its task loop, its collectives made, less its paired Tensor Memory operations (the same for
  the warp), are fewer than the thread's, and a consumer's grow with its time (`tc_vtime_lt`);
* in its exit stage its accumulator polls are fewer than the thread's response polls, so it has
read,
  as its last response, a response claiming no CTA after a poll that the thread also made and read
  as claiming (`exit_excluded`): a contradiction. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A data event is a warp-collective one, and no event the last-event releases concern. -/
theorem isTcData_facts {e : Event} (h : isTcData e = true) :
    isTcColl e = true ∧ (∀ op, e.kind ≠ .cluster op) ∧
      (∀ inc n inst, e.kind ≠ .setMaxReg inc n inst) ∧
      (∀ grp dst act, e.kind ≠ .tc (.resource grp dst act)) ∧ (∀ id cnt, e.kind ≠ .bar id cnt) := by
  obtain ⟨pc, k⟩ := e
  cases k <;> try (simp [isTcData] at h; done)
  rename_i kk
  cases kk <;> simp [isTcData, isTcColl] at h ⊢

/-- A trace's collectives, with the last event one of them. -/
theorem countTc_last {es : List Event} {e : Event} (hl : es[es.length - 1]? = some e)
    (hb : isTcColl e = true) :
    es.countP isTcColl = (es.take (es.length - 1)).countP isTcColl + 1 := by
  have hlt : es.length - 1 < es.length := (List.getElem?_eq_some_iff.mp hl).1
  conv_lhs => rw [← List.take_append_drop (es.length - 1) es]
  rw [List.drop_eq_getElem_cons hlt, List.drop_eq_nil_of_le (by omega)]
  have he : es[es.length - 1] = e := (List.getElem?_eq_some_iff.mp hl).2
  rw [he]
  simp [List.countP_append, hb]

/-- A lane of the warp of a thread is a thread. -/
theorem lt_threads_of_mem_warpLanes {g h : Nat} (hg : g < L.threads) (hm : h ∈ warpLanes L g) :
    h < L.threads := by
  have hb : 0 < L.block := by
    rcases Nat.eq_zero_or_pos L.block with h0 | h0
    · simp [Launch.threads, h0] at hg
    · exact h0
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
  rw [List.mem_range] at hl
  unfold warpSize at hl
  rw [lt_min_iff] at hl
  have e1 : g / L.block * L.block + g % L.block = g := Nat.div_add_mod' g L.block
  have e2 := Nat.div_add_mod (g % L.block) 32
  have hr := Nat.mod_lt g hb
  have hc : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb).mpr hg
  have hcb : (g / L.block + 1) * L.block ≤ L.grid * L.block := Nat.mul_le_mul_right _ hc
  rw [Nat.add_mul, Nat.one_mul] at hcb
  unfold warpLane laneOf
  show _ < L.grid * L.block
  generalize g / L.block * L.block = A at e1 hcb
  omega

/-- **A lane that has not reached the collective.** A thread whose last event is a data event and
that is not released has a lane in its warp with fewer collectives: otherwise each lane of the warp
has its collective of the same ordinal, which fills every need of the event (`tcNeeds`). -/
theorem tc_lane {g : Nat} (hg : g < L.threads) {e : Event}
    (hlast : X.get (g, (X.tr g).length - 1) = some e)
    (hd : isTcData e = true) (hnr : ¬ Step.Released L X g) :
    ∃ h, h < L.threads ∧ SameWarp L g h ∧
      (X.tr h).countP isTcColl < (X.tr g).countP isTcColl := by
  obtain ⟨hcoll, -, -, -, -⟩ := isTcData_facts hd
  have hl' : (X.tr g)[(X.tr g).length - 1]? = some e := hlast
  have hN := countTc_last hl' hcoll
  by_contra hcon
  push Not at hcon
  apply hnr
  refine ⟨fun pc k hq hk => ?_⟩
  clear hk
  rw [hlast] at hq
  obtain rfl := Option.some.inj hq
  have hneeds : Needs L X (g, (X.tr g).length - 1) = tcNeeds L X (g, (X.tr g).length - 1) := by
    simp only [Needs, hlast]
    cases k <;> simp [isTcData] at hd
    rename_i t
    cases t <;> first | rfl | simp at hd
  intro n hn
  rw [hneeds] at hn
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hn
  have hht := lt_threads_of_mem_warpLanes hg hh
  have hsw := sameWarp_of_mem_warpLanes hh hht hg
  have hle := hcon h hht (sameWarp_symm hsw)
  obtain ⟨j, e', hj, hq', hord⟩ := NamedBar.exists_ordinal isTcColl (X.tr h)
    (r := ((X.tr g).take ((X.tr g).length - 1)).countP isTcColl) (by omega)
  exact ⟨.thread (h, j), ⟨e', hj⟩, j, rfl, ⟨e', hj, hq'⟩, hord⟩

/-- **Progress at a blocked warp-collective `tcgen05` wait.** A pending consumer whose last event is
a Tensor Memory load or a wait, not released, passes to a lane of its warp that has made fewer
collectives: pending, and earlier in the rank table. -/
theorem tc_wait_steps (ht : ThreadFacts L X) (hub : ¬ HasUb X)
    (hmax : Maximal L kernel Prod mem0 X) (hagree : AllResponsesAgree L X)
    (hexit : ClusterExitAll L X) {g : Nat} (hp : Frame.Pending L X g) {c : Consumer.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c)))) {e : Event}
    (hlast : X.get (g, (X.tr g).length - 1) = some e) (hd : isTcData e = true)
    (hnr : ¬ Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hlen : 0 < (X.tr g).length := by
    have := len_of_get hlast
    simp only at this
    omega
  have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlen
  obtain ⟨d0, hd0⟩ := Frame.state_of_noUb ht.sound hX ht.tracked hub hlast
  have hσ1 : Frame.stateAt (code L) X g ((X.tr g).length - 1 + 1) = some (some (.inr (.cons c))) :=
    by
    rw [show (X.tr g).length - 1 + 1 = (X.tr g).length by omega]
    exact hσ
  obtain ⟨hxg, hs0⟩ := ht.cons_after_tc hg hlast hd hd0 hσ1
  have hcl1 : clArrives (X.tr g) = 1 := by
    rw [ht.cl_phase hg hσ]
    exact clPhase_of_loop hxg
  obtain ⟨h, hh, hsw, hlt⟩ := tc_lane hg hlast hd hnr
  obtain ⟨⟨-, -, hcta⟩, hwarp⟩ := hsw
  have hclu : L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block) := by rw [hcta]
  have hnoexit : ∀ pc, (X.tr h).getLast? ≠ some ⟨pc, .exit⟩ := by
    intro pc hl
    have := hexit h pc hh hl g hg hclu.symm
    omega
  refine .inr ⟨X, .thread h, hmax, ⟨hh, not_canceled_of_peer hX hg hne hclu, hnoexit⟩, ?_⟩
  have hub' : ∀ (y : Nat), ∀ k pc f, X.get (y, k) ≠ some ⟨pc, .ub f⟩ :=
    fun y k pc f hk => hub ⟨(y, k), pc, f, hk⟩
  have hrg : rank L X (.thread g) = threadTime L X g + 1 := by simp [rank, hnr]
  have hrh := rank_thread_le (L := L) (X := X) (g := h)
  suffices htt : threadTime L X h < threadTime L X g by omega
  -- the thread's time and counts
  have hgt : threadTime L X g = Consumer.vtime (consCount L g (X.tr g)) c := threadTime_of hσ hxg
  obtain ⟨-, -, hTg⟩ := ht.cons_bars hg hσ
  have hbig := tc_vtime_big hxg hs0 hTg
  have hcg := ht.cons_tc hg hσ
  have hmg : tmemOps (X.tr g) =
      if decide (g % L.block / 32 = 0) then 1 else 0 := by
    have := ht.tmem_ops hg (hub' g) hσ
    rw [List.take_length] at this
    rw [this]
    exact tmemOps_cons_loop _ hxg
  have hpos := tcPos_le c
  have hw0 : decide (h % L.block / 32 = 0) = decide (g % L.block / 32 = 0) := by rw [hwarp]
  have hwg := ht.role_warp hg (le_refl _) hσ
  simp only [roleWarp] at hwg
  cases hσh : Frame.stateAt (code L) X h (X.tr h).length with
  | none =>
    have : threadTime L X h = 0 := by simp [threadTime, hσh]
    omega
  | some σ =>
    cases σ with
    | none => exact absurd hσh (ht.tracked h _ hh)
    | some dh =>
      cases dh with
      | inl p =>
        have := threadTime_of (L := L) (X := X) hσh (show ThreadD.exitOff (Sum.inl p) =
          none from rfl)
        have h56 := Prologue.site_vtime_le p.site
        simp only [ThreadD.vtime] at this
        omega
      | inr r =>
        have hrw := ht.role_warp hh (le_refl _) hσh
        cases r with
        | loader l => simp only [roleWarp] at hrw; omega
        | mma m => simp only [roleWarp] at hrw; omega
        | sched s => simp only [roleWarp] at hrw; omega
        | cons ch =>
          have hch := ht.cons_tc hh hσh
          have hmh := ht.tmem_ops hh (hub' h) hσh
          rw [List.take_length] at hmh
          rw [hw0] at hmh
          by_cases hxh : Consumer.exitOff ch = none
          · obtain ⟨-, -, hTh⟩ := ht.cons_bars hh hσh
            have hmh' : tmemOps (X.tr h) = tmemOps (X.tr g) := by
              rw [hmh, hmg]
              exact tmemOps_cons_loop _ hxh
            have hht : threadTime L X h = Consumer.vtime (consCount L h (X.tr h)) ch :=
              threadTime_of hσh hxh
            by_cases hsh : ch.site = .setMaxReg
            · rw [hht]
              simp only [Consumer.vtime, hsh]
              omega
            · rw [hht, hgt]
              refine tc_vtime_lt hxg hs0 hTg hxh hsh hTh (a := (X.tr g).countP isTcColl -
                tmemOps (X.tr g))
                (a' := (X.tr h).countP isTcColl - tmemOps (X.tr h)) ?_ ?_ ?_
              · have := Nat.mul_le_mul_left 32 (show Consumer.holds c ≤ consCount L g (X.tr g) by
                  unfold Consumer.D.started at hTg; omega)
                omega
              · have := Nat.mul_le_mul_left 32 (show Consumer.holds ch ≤ consCount L h (X.tr h) by
                omega)
                omega
              · omega
          · exfalso
            obtain ⟨hx1, hx2, -⟩ := exit_counts ch hxh
            have hp0 := tcPos_exit hxh
            have hge := tmemOps_cons_ge (decide (g % L.block / 32 = 0)) ch
            have hct := ht.cons_tiles hg (hub' g) hσ
            have hho := holds_le_tileOpen c
            refine exit_excluded ht hagree hg hh (by omega) hσ hσh hxh ?_ hub
            rw [hx2] at hch
            omega

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
