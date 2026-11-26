-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Schedule.Instance
public import Kernels.FlashKdaFwd.Proof.Schedule.Sites
public import Kernels.FlashKdaFwd.Proof.Ref.Kinds.Event
public import Lemmas.Protocol.NamedBarReady
public import Lemmas.Protocol.NamedBarArrive
public import Lemmas.Step.CtaBarNamed

@[expose] public section

/-!
# The premises about a lane that is behind: `barLag`, `coll`, `matrix`

Three premises of the dispatcher (`Premises2`, `Dispatch.lean`) have the same shape: a thread
`g` is at an event that several threads perform together (a `bar.sync`, a shuffle or an
election, a warp matrix event), and a participant `h` that has made no more events of that
kind than `g` must be at an earlier time (strictly, unless it is at the same event). Each is
proved here from the ledgers of the reference layer's contract (`RefProgress`,
`Contract.lean`: the count of the kind as a function of the position), the static site facts
(`Sites.lean`: the count orders the positions) and the time table's arithmetic.

* More arithmetic of the time table: `timeAt_lt_start`, `timeAt_lt_pc`, `timeAt_lt_tile`,
  `timeAt_le_sub`, `timeAt_lt_sub`.
* `live_of_maximal`: **in a maximal execution a pending thread has a machine state.** A
  pending thread whose machine has stopped is released (`RefProgress.deadReleased`) and then
  performs the undefined behaviour its run has reached, a counted extension. So "the time of
  thread `h`" below is always the time of a state.
* `pending_of_noExit`: a launched thread without an exit event is pending.
* `prem_barLag`: `Premises2.barLag`. For barrier 0 the position of `g`'s arrival is one of
  the nine `bar.sync 0` (the protocol layer's `BarFacts.bar0_pc`), and a thread with no more
  arrivals is at or before it (`bar0`); these positions are in the startup and the epilogue,
  where the time is a function of the position. For the named barrier (2913) the ledger
  `bar8` gives the tile; a compute thread of the same tile is in the compute loop (`region`)
  at or before 2913; one in the epilogue would have made every named barrier, more than `g`.
* `collReleased_of`: **two lanes of a warp at one collective are released together**, the
  library's `WarpCollRel.released`, derived (it is no field of the contract: it needs the
  safety goal). A lane's last event blocks only if it is
  a `bar.sync 0` of the startup (85 or 110, directly before a shuffle or an election); the
  other lane, at the same position, has made the same number of `bar.sync 0`, and its arrival
  of that ordinal is passed or, the lane being released, ready: either way the barrier's
  generation is released (`NamedBar.Sources.ready_released`,
  `Lemmas/Protocol/NamedBarReady.lean`), and an arrival of a released generation is ready.
* `prem_coll`: `CollLead` (`Proof/Progress/Lead.lean`). Shapes and "a stopped machine is
  released" are fields of the contract; `exit` and `lag` come from the ledger `coll`, the
  field `collAt` and `Sites.lean`; `released` is `collReleased_of`.
* `prem_matrix`: the library's `Sched.MatrixFacts`. Shape and "the event before never blocks"
  are fields; `exit` and `lag` come from the ledger `matrix` (182 per finished tile plus
  `matBefore`), `tile_matrix`, and `mat_order`.

`hT` says that the tile count the reference layer chose for a thread is the count of its
block (`Protocol.ctaTiles`): the times of two threads of a block are compared.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Sched PTX.Flow PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Protocol
open PTX.Kernels.FlashKdaFwd.Proof.Thread (Site)

noncomputable section

/-! ### More arithmetic of the time table -/

/-- In the startup a later instruction is later, whatever the tile numbers. -/
theorem timeAt_lt_start {T T' t t' pc pc' sub sub' : Nat} (h : pc < pc') (hpc : pc' ≤ 1402)
    (hs : sub ≤ 3) : timeAt T t pc sub < timeAt T' t' pc' sub' := by
  unfold timeAt
  rw [ite_eq_left (by omega), ite_eq_left hpc]
  omega

/-- A later instruction is later, when the two positions are in one tile if both are in the
tile loops. -/
theorem timeAt_lt_pc {T t t' pc pc' sub sub' : Nat} (h : pc < pc') (hs : sub ≤ 3)
    (ht : 1402 < pc → pc' ≤ 3112 → t = t') : timeAt T t pc sub < timeAt T t' pc' sub' := by
  have hm : min t T ≤ T := Nat.min_le_right _ _
  have hm' : min t' T ≤ T := Nat.min_le_right _ _
  by_cases h1 : 1402 < pc ∧ pc' ≤ 3112
  · obtain rfl := ht h1.1 h1.2
    unfold timeAt band slot
    generalize min t T = m at hm
    split_ifs <;> omega
  · unfold timeAt band slot
    generalize min t T = m at hm
    generalize min t' T = m' at hm'
    split_ifs <;> omega

/-- A position of the startup or of the tile loops at an earlier tile is before every position
of a later tile's slot and before the epilogue. -/
theorem timeAt_lt_tile {T t t' pc pc' sub sub' : Nat} (hpc : pc ≤ 3112) (hs : sub ≤ 3)
    (ht : t < t') (ht' : t' ≤ T) (hpc' : 1402 < pc') :
    timeAt T t pc sub < timeAt T t' pc' sub' := by
  have h1 := timeAt_lt_of_tile_lt (T := T) (pc := pc) (sub := sub) hpc hs ht ht'
  have h2 : slot * (t' + 1) ≤ timeAt T t' pc' sub' := by
    by_cases h3 : pc' ≤ 3112
    · unfold timeAt
      rw [ite_eq_right (by omega), ite_eq_left h3, Nat.min_eq_left ht']
      omega
    · have := timeAt_end_ge (T := T) (t := t') (pc := pc') (sub := sub') (by omega)
      have h4 : slot * (t' + 1) ≤ slot * (T + 2) := Nat.mul_le_mul_left _ (by omega)
      omega
  omega

/-- At one instruction the first event is the earliest; outside the tile loops whatever the
tile numbers. -/
theorem timeAt_le_sub {T t t' pc sub : Nat} (ht : 1402 < pc → pc ≤ 3112 → t = t') :
    timeAt T t pc 0 ≤ timeAt T t' pc sub := by
  by_cases h1 : 1402 < pc ∧ pc ≤ 3112
  · obtain rfl := ht h1.1 h1.2
    unfold timeAt band
    split_ifs <;> omega
  · unfold timeAt
    split_ifs <;> omega

/-- In the compute loop a later sub-step of one instruction is later. -/
theorem timeAt_lt_sub {T t pc sub sub' : Nat} (h1 : 2106 ≤ pc) (h2 : pc ≤ 2944)
    (h : sub < sub') : timeAt T t pc sub < timeAt T t pc sub' := by
  unfold timeAt band
  split_ifs <;> omega

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {I : Nums}

/-! ### Pending threads of a maximal execution -/

/-- A launched thread without an exit event is pending. -/
theorem pending_of_noExit (hX : Consistent L kernel Assumptions.all mem0 X) {h : Nat}
    (hh : h < L.threads) (hne : ∀ k pc, X.get (h, k) ≠ some ⟨pc, .exit⟩) :
    Frame.Pending L X h :=
  ⟨hh, codeOk.notCanceled hX h, fun pc hl => hne _ pc (exit_get hl)⟩

/-- **In a maximal execution a pending thread has a machine state**: were its machine
stopped, the thread would be released and would perform the undefined behaviour it has
reached. -/
theorem live_of_maximal (hsound : ∀ g < L.threads, (Thread.code L g).Sound)
    (hs : SafeGoal kernel Assumptions.all L mem0) (R : RefProgress L mem0 X I)
    (hmax : Maximal L kernel Assumptions.all mem0 X) {h : Nat} (hp : Frame.Pending L X h) :
    ∃ d, Frame.stateAt (Thread.code L) X h (X.tr h).length = some (some d) := by
  have hX := hmax.1
  have hub := safe_noUb (hs.2 X hX)
  cases hσ : Frame.stateAt (Thread.code L) X h (X.tr h).length with
  | none =>
    exfalso
    have hrel := R.deadReleased hp hσ
    obtain ⟨u, hrun⟩ := Frame.run_some hX hub hp
    have hne : X.tr h ≠ [] := by
      rintro hnil
      rw [hnil, List.length_nil, Frame.stateAt_zero] at hσ
      cases hσ
    obtain ⟨Y, hY, hle, hlt⟩ := Step.dead_counted_extension hX hp.1 hne hrel
      (fun _ _ => asmOk.step.snoc hX rfl rfl) hrun (Frame.end_dead hsound hp.1 hrun hσ)
    have := hmax.2 Y hY hle
    omega
  | some o =>
    cases o with
    | none => exact absurd hσ (R.tracked h _ hp.1)
    | some d => exact ⟨d, rfl⟩

/-- The time of a thread with a machine state is the time of the state. -/
theorem threadTime_eq {h : Nat} {d : Thread.D}
    (hσ : Frame.stateAt (Thread.code L) X h (X.tr h).length = some (some d)) :
    threadTime (timed L I) X h = time I h d := by
  unfold threadTime
  rw [hσ]

/-- The ledgers at the end of a thread's trace count its whole trace. -/
theorem take_all (X : Execution) (h : Nat) : (X.tr h).take (X.tr h).length = X.tr h :=
  List.take_length

/-! ### `barLag` -/

/-- The positions of `bar.sync 0` are in the startup or in the epilogue. -/
theorem bar0Pcs_range : ∀ p ∈ bar0Pcs, p ≤ 1402 ∨ 3113 ≤ p := by decide

set_option maxRecDepth 100000 in
/-- **`Premises2.barLag`**: a participant lane that has made no more arrivals on the barrier
than thread `g` had made before its arrival has not exited and is no later than `g`'s state at
the arrival. -/
theorem prem_barLag (hpre : Pre P L mem0)
    (hsound : ∀ g < L.threads, (Thread.code L g).Sound)
    (hs : SafeGoal kernel Assumptions.all L mem0)
    (hT : ∀ g, I.tiles g = ctaTiles P (g / L.block)) (R : RefProgress L mem0 X I)
    (F : Facts P L X) (hmax : Maximal L kernel Assumptions.all mem0 X) {g y j pc id : Nat}
    {cnt : Option Nat} {d : Thread.D} (hg : g < L.threads) (hy : y < L.threads)
    (hcta : y / L.block = g / L.block) (hG : barG id (y % L.block / 32))
    (he : X.get (g, j) = some ⟨pc, .bar id cnt .sync⟩)
    (hσ : Frame.stateAt (Thread.code L) X g j = some (some d))
    (hle : (X.tr y).countP (Execution.isBarId id) ≤
      ((X.tr g).take j).countP (Execution.isBarId id)) :
    (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧
      threadTime (timed L I) X y ≤ time I g d := by
  have hX := hmax.1
  have hb := hpre.block
  have hpart : id = 8 → y % L.block < 128 := by
    rintro rfl
    rcases hG with ⟨h0, -⟩ | ⟨-, hw⟩
    · cases h0
    · omega
  have hne := barLag_not_exited F.bars hg hy hcta hpart he hle
  refine ⟨hne, ?_⟩
  obtain ⟨dy, hσy⟩ := live_of_maximal hsound hs R hmax (pending_of_noExit hX hy hne)
  rw [threadTime_eq hσy]
  have hpc : pc = d.site.pc := Frame.event_pc hsound hX he hσ
  have hTy : I.tiles y = I.tiles g := by rw [hT, hT, hcta]
  have hsub := sub_le dy.site
  unfold time
  rw [hTy]
  obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl, hgc⟩⟩ := F.bars.shape hg he
  · -- barrier 0: the arrival is at one of the nine positions
    have hpos := F.bars.bar0_pc hg he
    have hcg := R.bar0 hg hσ
    have hcy := R.bar0 hy hσy
    rw [take_all] at hcy
    rw [hcy, hcg] at hle
    have hmem : d.site.pc ∈ bar0Pcs := by
      rw [← hpc]
      exact List.mem_of_getElem? hpos
    have hpcle : dy.site.pc ≤ d.site.pc := by
      by_contra hlt
      have := filter_lt_succ_le hmem (Nat.lt_of_not_le hlt)
      unfold bar0Of at hle
      omega
    have hrange := bar0Pcs_range _ hmem
    rcases Nat.lt_or_eq_of_le hpcle with hlt | heq
    · exact (timeAt_lt_pc hlt hsub (by omega)).le
    · have h0 : dy.site.sub = 0 := sub_of_bar_pc (.inl (heq ▸ hmem))
      rw [h0, heq]
      exact timeAt_le_sub (by omega)
  · -- the named barrier: at 2913, in a tile
    have hyc := hpart rfl
    have hpc8 := F.bars.bar8_pc hg he
    have hd : d.site.pc = 2913 := by rw [← hpc, hpc8]
    have hcg := R.bar8 hg hσ hgc
    have hcy := R.bar8 hy hσy hyc
    rw [take_all] at hcy
    rw [hcy, hcg, hd] at hle
    have hlt : ((X.tr g).take j).countP (Execution.isBarId 8) + 1 ≤
        (X.tr g).countP (Execution.isBarId 8) := by
      have h1 := countP_take_succ (p := Execution.isBarId 8) he (by simp [Execution.isBarId])
      have h2 := (List.take_sublist (j + 1) (X.tr g)).countP_le (p := Execution.isBarId 8)
      omega
    have hT8 := F.bars.bar8_le hg hgc
    rw [← hT g] at hT8
    rw [hcg, hd] at hlt
    have htg : I.tile g d < I.tiles g := by
      unfold bar8Of at hlt
      rw [ite_eq_right (by omega)] at hlt
      omega
    have hgle := R.tile_le hg hσ
    unfold bar8Of at hle
    rw [ite_eq_right (by omega : ¬ (2913 < 2913 ∧ 2913 ≤ 2944))] at hle
    rw [hd]
    by_cases h1 : dy.site.pc ≤ 1402
    · exact (timeAt_lt_pc (by omega) hsub (by omega)).le
    by_cases h2 : 3113 ≤ dy.site.pc
    · have hty := R.tile_end hy hσy h2
      rw [ite_eq_right (by omega), hty, hTy] at hle
      omega
    obtain ⟨hr1, -, hr3⟩ := R.region hy hσy
    have h3 : 2105 < dy.site.pc := by
      by_contra h
      have := hr1 (by omega) (by omega)
      omega
    have h4 : dy.site.pc ≤ 2944 := by
      by_contra h
      have := hr3 (by omega) (by omega)
      omega
    by_cases h5 : 2913 < dy.site.pc
    · rw [ite_eq_left ⟨h5, h4⟩] at hle
      exact (timeAt_lt_tile (by omega) hsub (by omega) hgle (by omega)).le
    · rw [ite_eq_right (by omega)] at hle
      rcases Nat.lt_or_eq_of_le hle with hlt' | heq'
      · exact (timeAt_lt_tile (by omega) hsub hlt' hgle (by omega)).le
      · rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt h5) with hlt'' | heq''
        · exact (timeAt_lt_pc hlt'' hsub fun _ _ => heq').le
        · have h0 : dy.site.sub = 0 := sub_of_bar_pc (.inr heq'')
          rw [h0, heq'', heq']
          exact timeAt_le_sub fun _ _ => rfl

/-! ### Shuffles and elections -/

/-- The two bulk-group waits are in the store leader's loop and in the epilogue. -/
theorem bulkWait_pc : ∀ j : Fin 2, 3093 ≤ (Site.bulkWait j).pc := by decide +kernel

/-- A collective position is in the startup, at or before the election at 312. -/
theorem collAll_le : ∀ p ∈ collAll, p ≤ 312 := by decide

set_option maxRecDepth 100000 in
/-- **Two lanes of a warp at one collective are released together** (`WarpCollRel.released`).
`hbar0`, `hcoll`, `hcollAt` are the contract's fields `bar0`, `coll`, `collAt`. -/
theorem collReleased_of (hpre : Pre P L mem0)
    (hsound : ∀ g < L.threads, (Thread.code L g).Sound)
    (hs : SafeGoal kernel Assumptions.all L mem0) (F : Facts P L X)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (htr : Frame.Tracked (Thread.code L) X)
    (hbar0 : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
      Frame.stateAt (Thread.code L) X g k = some (some d) →
      ((X.tr g).take k).countP (Execution.isBarId 0) = bar0Of d.site.pc)
    (hcoll : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
      Frame.stateAt (Thread.code L) X g k = some (some d) →
      ((X.tr g).take k).countP isWarpColl = collOf (g % L.block / 32) d.site.pc)
    (hcollAt : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
      Frame.stateAt (Thread.code L) X g k = some (some d) → siteCls d.site = .coll →
      d.site.pc ∈ collPcs (g % L.block / 32))
    {g h : Nat} {d d' : Thread.D} (hg : g < L.threads) (hw : SameWarp L g h)
    (hσ : Frame.stateAt (Thread.code L) X g (X.tr g).length = some (some d))
    (hk : siteCls d.site = .coll)
    (hσ' : Frame.stateAt (Thread.code L) X h (X.tr h).length = some (some d'))
    (hk' : siteCls d'.site = .coll)
    (hcnt : (X.tr h).countP isWarpColl = (X.tr g).countP isWarpColl)
    (hrel : Step.Released L X g) : Step.Released L X h := by
  have hb := hpre.block
  have hh := hw.1.2.1
  have hub := safe_noUb (hs.2 X hX)
  refine ⟨fun pc k hq hres => ?_⟩
  -- the state before the last event of `h`, and the positions of the two lanes
  obtain ⟨d0, hd0⟩ := Frame.state_of_noUb hsound hX htr hub hq
  have hpc0 : pc = d0.site.pc := Frame.event_pc hsound hX hq hd0
  have hlen : (X.tr h).length - 1 + 1 = (X.tr h).length := by
    have hq' : (X.tr h)[(X.tr h).length - 1]? = some ⟨pc, k⟩ := hq
    have := (List.getElem?_eq_some_iff.mp hq').1
    omega
  have hcg := hcoll hg hσ
  have hch := hcoll hh hσ'
  rw [take_all] at hcg hch
  have hatg := hcollAt hg hσ hk
  have hath := hcollAt hh hσ' hk'
  have hc0 := hcoll hh hd0
  rw [← hw.2] at hch hath hc0
  have hpceq : d'.site.pc = d.site.pc :=
    Nat.le_antisymm (pc_le_of_collOf hatg (by omega)) (pc_le_of_collOf hath (by omega))
  have h312 := collAll_le _ (collPcs_sub _ _ hath)
  have hmono := (List.take_sublist ((X.tr h).length - 1) (X.tr h)).countP_le (p := isWarpColl)
  have hpc0le : d0.site.pc ≤ d'.site.pc := pc_le_of_collOf hath (by omega)
  cases k with
  | bar id cnt m =>
    obtain ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl, -⟩⟩ := F.bars.shape hh hq
    swap
    · have := F.bars.bar8_pc hh hq
      omega
    -- a `bar.sync 0`: both lanes have made as many, and the generation is released
    have hn := hbar0 hh hd0
    have hsucc := countP_take_succ (p := Execution.isBarId 0) hq (by simp [Execution.isBarId])
    rw [hlen, take_all] at hsucc
    have hbh := hbar0 hh hσ'
    have hbg := hbar0 hg hσ
    rw [take_all] at hbh hbg
    rw [hpceq] at hbh
    obtain ⟨j, pcj, hjlt, hbar, hord⟩ := F.bars.nth_bar0 hX (g := g) (k := (X.tr g).length)
      (q := ((X.tr h).take ((X.tr h).length - 1)).countP (Execution.isBarId 0))
      (by rw [take_all]; omega)
    have hrelg : CtaBarrier.Released L.block (X.barriers (g / L.block)) 0
        (((X.tr g).take j).countP (Execution.isBarId 0)) := by
      by_cases hlast : j + 1 < (X.tr g).length
      · exact (F.bars.sources0 hb).passed_released hX (shape0 hb) hbar hlast
      · have hj : j = (X.tr g).length - 1 := by omega
        exact (F.bars.sources0 hb).ready_released hX (shape0 hb) hbar
          (by rw [hj]; exact hrel.ready pcj _ (hj ▸ hbar) rfl)
    unfold bar0Before at hord
    simp only at hord
    rw [hord, hw.1.2.2] at hrelg
    have hkey := (F.bars.sources0 hb).key_of_released hX (shape0 hb) hq hh hrelg
    have hmod : (0 + 16 * ((X.tr h).take ((X.tr h).length - 1)).countP (Execution.isBarId 0))
        % 16 = 0 := by omega
    have hdiv : (0 + 16 * ((X.tr h).take ((X.tr h).length - 1)).countP (Execution.isBarId 0))
        / 16 = ((X.tr h).take ((X.tr h).length - 1)).countP (Execution.isBarId 0) := by omega
    refine NamedBar.ready_of_released hX.ctaBar hq ⟨hkey.1, ⟨none, pc, ?_⟩, hkey.2.2⟩ ?_
    · rw [hmod]
      exact hq
    · unfold CtaBarDone
      rw [hmod, hdiv]
      exact hrelg
  | bulkWait md n =>
    obtain ⟨j, hj⟩ := Ref.bulkWait_site hsound hX hq hd0 rfl
    have := bulkWait_pc j
    rw [← hj] at this
    omega
  | _ => first | exact (codeOk.no_kind hX rfl hq).elim | cases hres

/-- **`Premises2.coll`**: the facts of the warp collectives. -/
theorem prem_coll (hpre : Pre P L mem0) (hsound : ∀ g < L.threads, (Thread.code L g).Sound)
    (hs : SafeGoal kernel Assumptions.all L mem0) (R : RefProgress L mem0 X I)
    (F : Facts P L X) (hX : Consistent L kernel Assumptions.all mem0 X) :
    CollLead mem0 (timed L I) X (wkey L) (fun g d => cls g d = .coll) where
  rel :=
    { shape := R.collShape
      released := fun hg hw hσ hk hσ' hk' hc hrel =>
        .inl (collReleased_of hpre hsound hs F hX R.tracked R.bar0 R.coll R.collAt hg hw hσ hk
          hσ' hk' hc hrel)
      exit := by
        refine ⟨fun k => (collPcs k.2).length, fun {g d} hg hσ hk => ?_,
          fun {g k pc d} hg hσ he => ?_⟩
        · have hc := R.coll hg hσ
          rw [take_all] at hc
          rw [hc]
          exact collOf_lt_length (coll_pc hk).1
        · have hc := R.coll hg hσ
          rw [hc, R.exitAt hg hσ he, collOf_exit]
          exact le_rfl
      dead := R.deadReleased
      lag := by
        intro g h d hg hh hw hσ hk hle hnot hlive
        obtain ⟨dh, hσh⟩ : ∃ dh, Frame.stateAt (Thread.code L) X h (X.tr h).length =
            some (some dh) := by
          cases hq : Frame.stateAt (Thread.code L) X h (X.tr h).length with
          | none => exact absurd hq hlive
          | some o =>
            cases o with
            | none => exact absurd hq (R.tracked h _ hh)
            | some dh => exact ⟨dh, rfl⟩
        rw [threadTime_eq hσh]
        have hcg := R.coll hg hσ
        have hch := R.coll hh hσh
        rw [take_all] at hcg hch
        rw [← hw.2] at hch
        rw [hcg, hch] at hle
        have hat := R.collAt hg hσ hk
        have hpcle := pc_le_of_collOf hat hle
        have hall := collPcs_sub _ _ hat
        have h312 : d.site.pc ≤ 312 := by
          revert hall
          generalize d.site.pc = p
          revert p
          decide
        rcases Nat.lt_or_eq_of_le hpcle with hlt | heq
        · exact timeAt_lt_start hlt (by omega) (sub_le _)
        · exfalso
          refine hnot ⟨?_, dh, hσh, coll_of_pc (heq ▸ hall)⟩
          rw [hcg, hch, heq] }
  kind := R.collKind

/-! ### Warp matrix events -/

/-- The matrix events of a compute thread at the exit: 182 per tile. -/
theorem matrix_at_exit (R : RefProgress L mem0 X I) {g k pc : Nat} {d : Thread.D}
    (hg : g < L.threads) (hc : g % L.block < 128)
    (hσ : Frame.stateAt (Thread.code L) X g k = some (some d))
    (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    ((X.tr g).take k).countP isMatrix = 182 * I.tiles g := by
  have hpc := R.exitAt hg hσ he
  rw [R.matrix hg hσ hc, R.tile_end hg hσ (by omega)]
  unfold matBefore
  rw [ite_eq_left (by omega), Nat.add_zero]

/-- The matrix events of a compute thread at a matrix event: fewer than 182 per tile. -/
theorem matrix_lt (R : RefProgress L mem0 X I) {g : Nat} {d : Thread.D} (hg : g < L.threads)
    (hσ : Frame.stateAt (Thread.code L) X g (X.tr g).length = some (some d))
    (hk : siteCls d.site = .matrix) :
    g % L.block < 128 ∧ (X.tr g).countP isMatrix = 182 * I.tile g d + matBefore d.site ∧
      matBefore d.site < 182 ∧ I.tile g d < I.tiles g := by
  obtain ⟨hc, ht⟩ := R.tile_matrix hg hσ hk
  have hm := R.matrix hg hσ hc
  rw [take_all] at hm
  exact ⟨hc, hm, matBefore_lt hk, ht⟩

set_option maxRecDepth 100000 in
/-- **`Premises2.matrix`**: the facts of the warp matrix events. -/
theorem prem_matrix (hpre : Pre P L mem0)
    (hsound : ∀ g < L.threads, (Thread.code L g).Sound)
    (hs : SafeGoal kernel Assumptions.all L mem0)
    (hT : ∀ g, I.tiles g = ctaTiles P (g / L.block)) (R : RefProgress L mem0 X I)
    (hmax : Maximal L kernel Assumptions.all mem0 X) :
    MatrixFacts (timed L I) X (wkey L) (fun g d => cls g d = .matrix) where
  shape := by
    refine ⟨fun _ n => matOp (n % 182), fun _ _ => matOp_laneClosed _,
      fun {g d t m} hg hσ hk hat hout => ?_⟩
    rcases R.matrixShape hg hσ hk hat hout with hub | ⟨pc, op, own, k, hget, hpc, hm⟩
    · exact .inl hub
    · have hop : matOp ((X.tr g).countP isMatrix % 182) = (pc, op) := by
        unfold matOp
        rw [List.getD_eq_getElem?_getD, hget]
        rfl
      refine .inr ?_
      dsimp only
      rw [hop]
      exact ⟨hpc, own, k, hm⟩
  last := ⟨fun _ _ => none, fun {g d} hg hσ hk => R.matrixPrev hg hσ hk⟩
  exit := by
    have hb := hpre.block
    refine ⟨fun k => if k.2 < 4 then 182 * ctaTiles P k.1 else 0, fun {g d} hg hσ hk => ?_,
      fun {g k pc d} hg hσ he => ?_⟩
    · obtain ⟨hc, hm, hlt, ht⟩ := matrix_lt R hg hσ hk
      have hw : (wkey L g).2 < 4 := by
        unfold wkey
        simp only
        omega
      dsimp only
      rw [ite_eq_left hw, hm]
      have h1 : (wkey L g).1 = g / L.block := rfl
      rw [h1, ← hT g]
      have : 182 * (I.tile g d + 1) ≤ 182 * I.tiles g := Nat.mul_le_mul_left _ ht
      omega
    · dsimp only
      by_cases hw : (wkey L g).2 < 4
      · have hc : g % L.block < 128 := by
          unfold wkey at hw
          simp only at hw
          omega
        rw [ite_eq_left hw, matrix_at_exit R hg hc hσ he]
        have h1 : (wkey L g).1 = g / L.block := rfl
        rw [h1, ← hT g]
      · rw [ite_eq_right hw]
        exact Nat.zero_le _
  lag := by
    intro g h d hg hh hw hσ hk hle hnot
    have hX := hmax.1
    have hub := safe_noUb (hs.2 X hX)
    have hb := hpre.block
    obtain ⟨hc, hm, hlt, ht⟩ := matrix_lt R hg hσ hk
    have hch : h % L.block < 128 := by
      have h1 := hw.2
      have h2 : g % L.block < 192 := by rw [hb]; exact Nat.mod_lt _ (by decide)
      have h3 : h % L.block < 192 := by rw [hb]; exact Nat.mod_lt _ (by decide)
      omega
    have hTh : I.tiles h = I.tiles g := by rw [hT, hT, hw.1.2.2]
    -- the lane behind has not exited: at the exit it would have made every matrix event
    have hne : ∀ k pc, X.get (h, k) ≠ some ⟨pc, .exit⟩ := by
      intro k pc hx
      obtain ⟨dx, hdx⟩ := Frame.state_of_noUb hsound hX R.tracked hub hx
      have h1 := matrix_at_exit R hh hch hdx hx
      have h2 := (List.take_sublist k (X.tr h)).countP_le (p := isMatrix)
      have : 182 * (I.tile g d + 1) ≤ 182 * I.tiles g := Nat.mul_le_mul_left _ ht
      rw [hTh] at h1
      omega
    obtain ⟨dh, hσh⟩ := live_of_maximal hsound hs R hmax (pending_of_noExit hX hh hne)
    rw [threadTime_eq hσh]
    have hmh := R.matrix hh hσh hch
    rw [take_all] at hmh
    have hr := matrix_pc_range hk
    have hgle := R.tile_le hg hσ
    have hsub := sub_le dh.site
    unfold time
    rw [hTh]
    by_cases h1 : dh.site.pc ≤ 1402
    · exact timeAt_lt_pc (by omega) hsub (by omega)
    by_cases h2 : 3113 ≤ dh.site.pc
    · exfalso
      have hty := R.tile_end hh hσh h2
      have : 182 * (I.tile g d + 1) ≤ 182 * I.tiles g := Nat.mul_le_mul_left _ ht
      rw [hty, hTh] at hmh
      omega
    have h3 : I.tile h dh ≤ I.tile g d := by
      by_contra hgt
      have : 182 * (I.tile g d + 1) ≤ 182 * I.tile h dh := Nat.mul_le_mul_left _ (by omega)
      omega
    rcases Nat.lt_or_eq_of_le h3 with hlt' | heq'
    · exact timeAt_lt_tile (by omega) hsub hlt' hgle (by omega)
    · rw [heq'] at hmh ⊢
      rcases mat_order hk (by omega) (by omega : matBefore dh.site ≤ matBefore d.site) with
        hpc | ⟨hpc, hcls | hs'⟩
      · exact timeAt_lt_pc hpc hsub fun _ _ => rfl
      · exfalso
        refine hnot ⟨?_, dh, hσh, hcls⟩
        rw [hm, hmh, matBefore_eq_of_pc hk hcls hpc]
      · rw [hpc]
        exact timeAt_lt_sub hr.1 (by omega) hs'

end

end PTX.Kernels.FlashKdaFwd.Proof.Progress
