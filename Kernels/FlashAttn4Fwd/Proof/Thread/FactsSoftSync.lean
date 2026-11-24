-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftEvents
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreOut
public import Kernels.FlashAttn4Fwd.Proof.Interface.TmemRoute
public import Kernels.FlashAttn4Fwd.Proof.Interface.Exit
public import Kernels.FlashAttn4Fwd.Proof.Interface.Older

@[expose] public section

/-! # The softmax warps' statistics barriers, credits, S-full polls and P-ready arrivals

From the site events and `Softmax.Counts`: a softmax thread's events on its statistics barrier
are its named-barrier arrivals at the `gen` sites, each after one more successful credit poll
than earlier arrivals (`Softmax.credit`); its polls carry the parity of their counts
(`soft_wait`); its P-ready arrival of a tile follows the tile's S-full poll; at its exit it has
made the counted events of every item of its cluster. No other role polls a credit or S-full
barrier (`soft_obj_poll`: the loader polls ring empty barriers, the MMA warp its sites'
barriers, the store warp the staged barriers, the correction warps the O-full and free
barriers, the idle warp nothing). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A credit or S-full barrier: an object only softmax threads poll. -/
def SoftPollObj (L : Launch) (m : Loc) : Prop :=
  ∃ c st, st < 2 ∧ (m = statsBar L c st ∨ m = sFullBar L c st)

theorem softPollObj_fbar {L : Launch} {m : Loc} (h : SoftPollObj L m) :
    ∃ c b, m = FBar.loc L c b ∧ ((∃ st, b = .stats st) ∨ ∃ st, b = .sFull st) := by
  obtain ⟨c, st, hst, rfl | rfl⟩ := h
  · exact ⟨c, .stats ⟨st, hst⟩, statsBar_eq L c ⟨st, hst⟩, .inl ⟨_, rfl⟩⟩
  · exact ⟨c, .sFull ⟨st, hst⟩, sFullBar_eq L c ⟨st, hst⟩, .inr ⟨_, rfl⟩⟩

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **Only softmax threads poll a credit or S-full barrier.** -/
theorem soft_obj_poll {g i pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (hg : g < L.threads) (he : X.get (g, i) = some ⟨pc, .wait m p ok acq sc⟩)
    (hm : SoftPollObj L m) : warpOf L g < 8 := by
  obtain ⟨r, t, ins, u, hσ, hJ, hat, hi, hc, hf⟩ :=
    role_event hpre hX ht he (fun h => by rcases h with ⟨f, h⟩ | h <;> cases h) (fun h => h)
  have hw := Cross.role_of_state hpre hX hg hσ
  have hk : (⟨pc, .wait m p ok acq sc⟩ : Event).kind = .wait m p ok acq sc := rfl
  obtain ⟨c, b, hmb, hb⟩ := softPollObj_fbar hm
  cases r with
  | softmax d => exact hi.warp
  | store d =>
    exfalso
    obtain ⟨st0, -, hm', -⟩ := Store.ev_wait (Store.shape hpre hat hi hc hf)
    rw [hm', Store.stagedAt_eq, stagedBar_fbar L _ st0.isLt] at hmb
    obtain ⟨rfl, -⟩ := FBar.loc_inj hmb
    rcases hb with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
  | loader d =>
    exfalso
    obtain ⟨b', hb', hm', -⟩ := Loader.wait_fact hpre hg hJ hi
      ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩ hc hf hk
    rw [hmb] at hm'
    obtain ⟨rfl, -⟩ := FBar.loc_inj hm'
    rcases hb with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [FBar.isEmpty] at hb'
  | mma d =>
    exfalso
    obtain ⟨B, hpb, hm', -⟩ := wait_ev (Mma.site_event hpre hg hat.2.2.2.2 hc hf) hk
    rw [hmb] at hm'
    obtain ⟨hB, -⟩ := FBar.loc_inj hm'
    obtain ⟨site, i, tt, base, pro⟩ := d
    rcases hb with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> subst hB <;> cases site <;> simp [Mma.pollBar] at hpb
  | corr d =>
    exfalso
    obtain ⟨hw8, hw12⟩ := hw
    obtain ⟨d', -, -, -, -, h⟩ := corr_wait hpre hX ht hw8 hw12 he
    obtain ⟨c', st', hst', hm'⟩ := hm
    rcases hm' with rfl | rfl <;>
      rcases h with ⟨st, -, hm, -⟩ | ⟨st, -, hm, -⟩ | ⟨-, hm, -⟩ <;>
      simp only [statsBar, sFullBar, Correction.ownLoc, Correction.sb, Loc.mk.injEq] at hm <;>
      omega
  | idle s =>
    exfalso
    obtain ⟨p', b', off, par, sc0, hop, -⟩ := fires_wait_flags hf hk
    exact (Idle.site_not_poll s.site).1 (OpPcsFast.mem kernel_poll_pcs hc (by rw [hop]; rfl))

/-- **`StatsFacts.bar_form`, softmax part.** -/
theorem Facts.Soft.bar_form {g i pc id : Nat} {cnt : Option Nat} {m : BarMode}
    (hw : warpOf L g < 8) (he : X.get (g, i) = some ⟨pc, .bar id cnt m⟩) :
    (id = 2 ∧ cnt = some 416) ∨
      (cnt = some 64 ∧ ((warpOf L g < 8 ∧ id = warpOf L g + 3 ∧ m = .arrive) ∨
        (8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ (id = warpOf L g - 5 ∨ id = warpOf L g - 1) ∧
          m = .sync))) := by
  rcases soft_bar hpre hX ht hw he with h | ⟨h1, h2, h3⟩
  · exact .inl h
  · exact .inr ⟨h1, .inl ⟨hw, h3, h2⟩⟩

/-- **`StatsFacts.soft_credit`**: a softmax thread's event on its statistics barrier follows one
more successful credit poll of its stage than its earlier events on the barrier. -/
theorem StatsFacts_soft_credit {g i pc id : Nat} {cnt : Option Nat} {m : BarMode}
    (_hg : g < L.threads) (hw : warpOf L g < 8) (he : X.get (g, i) = some ⟨pc, .bar id cnt m⟩)
    (hid : id ≠ 2) :
    okPolls (statsBar L (ctaOf L g) (warpOf L g / 4)) ((X.tr g).take i) =
      barOrd X g i id + 1 := by
  rcases soft_bar hpre hX ht hw he with ⟨h, -⟩ | ⟨-, -, rfl⟩
  · exact absurd h hid
  obtain ⟨d, t, ins, o, -, hc, hi, -, -, -, hev⟩ :=
    soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
  rw [soft_barOrd hpre hX ht hw i (by omega)]
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  cases site <;> simp only [Softmax.Ev, Kind.bar.injEq, reduceCtorEq, exists_false] at hev
  · omega
  case gen j =>
    have h := Softmax.credit hi hc j rfl
    rw [soft_statsId] at h
    show okPolls (Softmax.ownLoc L g (240 + 8 * Softmax.stOf L g)) _ = _
    rw [← h]
  · omega

end

/-- The S-full polls of the generation `(n + 1) i + r` of an item. -/
theorem genTiles_item (n i r : Nat) (hr : r ≤ n) :
    genTiles n ((n + 1) * i + r) = n * i + min (r + 1) n := by
  unfold genTiles
  rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.mul_add_mod,
    Nat.mod_eq_of_lt (by omega)]
  simp

/-- The softmax thread's credit barrier. -/
theorem soft_statsBar (L : Launch) (g : Nat) :
    statsBar L (ctaOf L g) (warpOf L g / 4) = Softmax.ownLoc L g (240 + 8 * Softmax.stOf L g) :=
  rfl

/-- The softmax thread's S-full barrier. -/
theorem soft_sFullBar (L : Launch) (g : Nat) :
    sFullBar L (ctaOf L g) (warpOf L g / 4) = Softmax.ownLoc L g (128 + 8 * Softmax.stOf L g) :=
  rfl

/-- The softmax thread's P-ready barrier of the leader. -/
theorem soft_pReadyBar (L : Launch) (g : Nat) :
    pReadyBar L (leadCta (ctaOf L g)) (warpOf L g / 4) =
      Softmax.leadLoc L g (144 + 8 * Softmax.stOf L g) := by
  rw [soft_leadLoc]; rfl

/-- The softmax thread's second P-ready barrier of the leader. -/
theorem soft_pReady2Bar (L : Launch) (g : Nat) :
    pReady2Bar L (leadCta (ctaOf L g)) (warpOf L g / 4) =
      Softmax.leadLoc L g (160 + 8 * Softmax.stOf L g) := by
  rw [soft_leadLoc]; rfl

/-- The softmax's S-full polls are sites of the cluster-scope assumption. -/
theorem soft_sW_cluster (lp : Bool) : (Softmax.Site.sW lp).pc ∈ Assumptions.clusterMbarSites := by
  cases lp <;> decide

/-- The softmax's remote arrivals are sites of the cluster-scope assumption. -/
theorem soft_arr_cluster (lp : Bool) : (Softmax.Site.pArr lp).pc ∈ Assumptions.clusterMbarSites ∧
    (Softmax.Site.p2Arr lp).pc ∈ Assumptions.clusterMbarSites := by
  cases lp <;> decide

/-- The successor of a softmax state along its event. -/
theorem soft_succ {g k : Nat} {d : Softmax.D} {e : Event}
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.softmax d))))
    (he : X.get (g, k) = some e) :
    Frame.stateAt (code L) X g (k + 1) =
      (Softmax.next L g d e).map (Option.map (.inr ∘ .softmax)) := by
  have he' : (X.tr g)[k]? = some e := he
  rw [Frame.stateAt_succ he', hσ]
  rfl

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **`StatsFacts.credit_poll`**: a poll of a credit barrier is a softmax thread's of the
barrier's CTA and stage, with the parity of its earlier successful polls plus one; it
acquires. -/
theorem StatsFacts_credit_poll {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}
    (hg : g < L.threads) (hst : st < 2)
    (he : X.get (g, i) = some ⟨pc, .wait (statsBar L c st) p ok acq sc⟩) :
    warpOf L g < 8 ∧ warpOf L g / 4 = st ∧ c = ctaOf L g ∧
      p % 2 = (okPolls (statsBar L c st) ((X.tr g).take i) + 1) % 2 ∧
      (ok = true → acq = true) := by
  have hw := soft_obj_poll hpre hX ht hg he ⟨c, st, hst, .inl rfl⟩
  obtain ⟨d, -, -, -, -, h⟩ := soft_wait hpre hX ht hw he
  have hat := Static.wait_attr hX he
  have : Softmax.stOf L g = warpOf L g / 4 := rfl
  rcases h with ⟨w, -, hm, hp⟩ | ⟨lp, -, hm, -⟩
  · have hm' := hm
    simp only [statsBar, Softmax.ownLoc, Softmax.sb, Loc.mk.injEq] at hm'
    obtain ⟨-, hc, hoff⟩ := hm'
    refine ⟨hw, ?_, hc, hp, fun _ => hat.1⟩
    have : Softmax.stOf L g = warpOf L g / 4 := rfl
    omega
  · simp only [statsBar, Softmax.ownLoc, Softmax.sb, Loc.mk.injEq] at hm
    omega

/-- **`SFullFacts.s_poll`**: a poll of an S-full barrier is a softmax thread's of the barrier's
CTA and stage, with the parity of its earlier successful polls; a successful one acquires at
cluster scope. -/
theorem SFullFacts_s_poll {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}
    (hg : g < L.threads) (hst : st < 2)
    (he : X.get (g, i) = some ⟨pc, .wait (sFullBar L c st) p ok acq sc⟩) :
    ctaOf L g = c ∧ warpOf L g < 8 ∧ warpOf L g / 4 = st ∧
      p % 2 = okPolls (sFullBar L c st) ((X.tr g).take i) % 2 ∧
      (ok = true → acq = true ∧ sc = .cluster) := by
  have hw := soft_obj_poll hpre hX ht hg he ⟨c, st, hst, .inr rfl⟩
  obtain ⟨d, -, -, -, hpc, h⟩ := soft_wait hpre hX ht hw he
  have hat := Static.wait_attr hX he
  have : Softmax.stOf L g = warpOf L g / 4 := rfl
  rcases h with ⟨w, -, hm, -⟩ | ⟨lp, hs, hm, hp⟩
  · simp only [sFullBar, Softmax.ownLoc, Softmax.sb, Loc.mk.injEq] at hm
    omega
  · have hm' := hm
    simp only [sFullBar, Softmax.ownLoc, Softmax.sb, Loc.mk.injEq] at hm'
    obtain ⟨-, hc, hoff⟩ := hm'
    refine ⟨hc.symm, hw, ?_, hp, fun _ => ⟨hat.1, hat.2 ?_⟩⟩
    · have : Softmax.stOf L g = warpOf L g / 4 := rfl
      omega
    · rw [← hpc, hs]
      exact soft_sW_cluster lp

/-- **`PReadyFacts.p_arrive`, softmax part.** -/
theorem Facts.Soft.p_arrive {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}
    (hw : warpOf L g < 8) (hst : st < 2)
    (he : X.get (g, i) = some ⟨pc, .arrive (pReadyBar L c st) tx cnt rel sc⟩) :
    leadCta (ctaOf L g) = c ∧
      ((warpOf L g < 8 ∧ warpOf L g / 4 = st) ∨ (8 ≤ warpOf L g ∧ warpOf L g < 12)) ∧
      tx = 0 ∧ cnt = 1 ∧ rel = true ∧ sc = .cluster := by
  obtain ⟨d, -, -, -, hpc, htx, hcnt, h⟩ := soft_arrive hpre hX ht hw he
  have hat := Static.arrive_attr hX he
  have : Softmax.stOf L g = warpOf L g / 4 := rfl
  rcases h with ⟨lp, hs, hm⟩ | ⟨lp, -, hm⟩
  · simp only [pReadyBar, Softmax.leadLoc, Softmax.sb, Loc.mk.injEq] at hm
    refine ⟨by simp only [leadCta]; omega, .inl ⟨hw, ?_⟩, htx, hcnt, hat.1, hat.2 ?_⟩
    · have : Softmax.stOf L g = warpOf L g / 4 := rfl
      omega
    · rw [← hpc, hs]
      exact (soft_arr_cluster lp).1
  · simp only [pReadyBar, Softmax.leadLoc, Softmax.sb, Loc.mk.injEq] at hm
    omega

/-- **`RouteFacts.soft_p`**: a softmax arrival on its stage's P-ready barrier follows its S-full
poll of the tile. -/
theorem RouteFacts_soft_p {g i pc tx cnt : Nat} {rel : Bool} {sc : MbarScope}
    (_hg : g < L.threads) (hw : warpOf L g < 8)
    (he : X.get (g, i) = some ⟨pc,
      .arrive (pReadyBar L (leadCta (ctaOf L g)) (warpOf L g / 4)) tx cnt rel sc⟩) :
    pArr L X g (warpOf L g / 4) i + 1 ≤ sPolls L X g (warpOf L g / 4) i := by
  obtain ⟨d, -, hc, hi, -, -, -, h⟩ := soft_arrive hpre hX ht hw he
  unfold pArr sPolls
  rw [soft_pReadyBar, soft_sFullBar, hc.pReady, hc.score]
  have ht0 := hi.tile0
  rcases h with ⟨lp, hs, -⟩ | ⟨lp, -, hm⟩
  · obtain ⟨site, ii, tt, w, mm, l⟩ := d
    simp only at hs ht0 ⊢
    subst hs
    cases lp <;>
      simp [Softmax.pPos, Softmax.sPos, Softmax.tileNo, Softmax.Site.tile0,
        Softmax.Site.inTrip, Softmax.Site.tile0Ld, Softmax.Site.afterP] at ht0 ⊢
    omega
  · rw [← soft_pReady2Bar] at hm
    simp only [pReadyBar, pReady2Bar, Loc.mk.injEq] at hm
    omega

/-- **`ExitFacts.soft_exit`**: at its exit a softmax thread has polled its stage's S-full
barrier for every score tile of an item of its cluster. -/
theorem ExitFacts_soft_exit {g k pc u : Nat} (_hg : g < L.threads) (hw : warpOf L g < 8)
    (he : X.get (g, k) = some ⟨pc, .exit⟩) (hu : workOf L g (u / kvBlocks P) < totOf L) :
    u < okPolls (sFullBar L (ctaOf L g) (warpOf L g / 4)) ((X.tr g).take k) := by
  obtain ⟨d, -, hc, hi, hs⟩ := soft_exit_state hpre hX ht hw he
  rw [soft_sFullBar, hc.score]
  have hti := (hi.tail (.inr (.inr hs))).1
  have hu' := (soft_lt_items hpre).mpr hu
  have hn := soft_trips_pos hpre
  rw [soft_trips_eq hpre] at hn ⊢
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs hti ⊢
  subst hs hti
  simp only [Softmax.sPos, Softmax.Site.tile0Ld, Softmax.Site.tile0, Softmax.Site.inTrip,
    Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  rw [Nat.div_lt_iff_lt_mul (by omega)] at hu'
  rw [Nat.mul_comm]
  exact hu'

/-- **`OlderFacts.soft_stats_exit`**: at its exit a softmax thread has made `kvBlocks + 1`
arrivals on its statistics barrier per item of its cluster. -/
theorem OlderFacts_soft_stats_exit {g k pc u : Nat} (_hg : g < L.threads) (hw : warpOf L g < 8)
    (he : X.get (g, k) = some ⟨pc, .exit⟩) (hu : workOf L g u < totOf L) :
    (kvBlocks P + 1) * (u + 1) ≤ barOrd X g k (warpOf L g + 3) := by
  obtain ⟨d, -, hc, hi, hs⟩ := soft_exit_state hpre hX ht hw he
  rw [soft_barOrd_gen hpre hX ht hw hc, ← soft_trips_eq hpre]
  have hti := (hi.tail (.inr (.inr hs))).1
  have hu' := (soft_lt_items hpre).mpr hu
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs hti ⊢
  subst hs hti
  simp only [Softmax.genPos, Softmax.Site.tile0, Softmax.Site.inTrip, Bool.false_eq_true,
    Bool.or_self, reduceCtorEq, decide_false, ↓reduceIte, Nat.add_zero]
  exact Nat.mul_le_mul_left _ hu'

/-- The S-full polls before an arrival on the statistics barrier are those before the event
preceding it. -/
theorem soft_gen_prev {g a : Nat} {e : Event} {d : Softmax.D} {j : Fin 3} (hw : warpOf L g < 8)
    (he : X.get (g, a) = some e)
    (hσ : Frame.stateAt (code L) X g (a + 1) = some (some (.inr (.softmax d))))
    (hs : d.site = .gen j) :
    okPolls (sFullBar L (ctaOf L g) (warpOf L g / 4)) ((X.tr g).take (a + 1)) =
      okPolls (sFullBar L (ctaOf L g) (warpOf L g / 4)) ((X.tr g).take a) := by
  have he' : (X.tr g)[a]? = some e := he
  rw [List.take_add_one, he', Option.toList_some, okPolls_snoc]
  suffices h : okPoll (sFullBar L (ctaOf L g) (warpOf L g / 4)) e = false by simp [h]
  obtain ⟨epc, ek⟩ := e
  cases ek with
  | wait m p ok acq sc =>
    cases ok
    · simp [okPoll, sourceWaitSuccess]
    · obtain ⟨d', hσ', -, -, -, h⟩ := soft_wait hpre hX ht hw he
      rcases h with ⟨w, -, hm, -⟩ | ⟨lp, hs', hm, -⟩
      · subst hm
        simp only [okPoll, sourceWaitSuccess, decide_eq_false_iff_not]
        rw [soft_sFullBar]
        simp only [Softmax.ownLoc, Loc.mk.injEq]
        omega
      · rw [soft_succ hσ' he] at hσ
        simp only [Softmax.next, hs', ↓reduceIte, Option.map,
          Option.some.injEq, Function.comp, Sum.inr.injEq, Role.softmax.injEq] at hσ
        subst hσ
        simp at hs
  | _ => simp [okPoll, sourceWaitSuccess]

/-- **`RouteFacts.soft_gen`**: a softmax arrival of ordinal `G` on its statistics barrier
follows `genTiles n G` S-full polls, with an event between. -/
theorem RouteFacts_soft_gen {g a pc id : Nat} {cnt : Option Nat} {m : BarMode}
    (_hg : g < L.threads) (hw : warpOf L g < 8) (he : X.get (g, a) = some ⟨pc, .bar id cnt m⟩)
    (hid : id ≠ 2) :
    ∃ e < a, genTiles (kvTiles L) (barOrd X g a id) ≤ sPolls L X g (warpOf L g / 4) e := by
  rcases soft_bar hpre hX ht hw he with ⟨h, -⟩ | ⟨-, -, rfl⟩
  · exact absurd h hid
  obtain ⟨d, t, ins, o, hσ, hc, hi, -, -, -, hev⟩ :=
    soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
  have hla := hi.last
  have htr := hi.trip
  have ht0 := hi.tile0
  have hS := hc.score
  have hG := soft_barOrd_gen hpre hX ht hw hc
  have hst := hc.stats
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  cases site <;> simp only [Softmax.Ev, Kind.bar.injEq, reduceCtorEq, exists_false] at hev
  · omega
  case gen j =>
    -- the arrival is not the thread's first event
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := by
      rcases a with _ | a'
      · simp only [List.take_zero, okPolls, List.countP_nil] at hst
        rcases Softmax.fin3_cases j with rfl | rfl | rfl <;>
          simp [Softmax.statsPos, Softmax.Site.inItem, Softmax.Site.tile0] at hst <;> omega
      · exact ⟨a', rfl⟩
    obtain ⟨x, hx⟩ : ∃ x, X.get (g, a') = some x :=
      ⟨_, List.getElem?_eq_getElem (by
        show a' < (X.tr g).length
        have h := (List.getElem?_eq_some_iff.mp he).1
        simp only at h
        omega)⟩
    refine ⟨a', by omega, ?_⟩
    unfold sPolls
    rw [← soft_gen_prev hpre hX ht hw hx hσ rfl, soft_sFullBar, hS, hG]
    simp only at hla htr ht0
    rw [show kvTiles L = Softmax.trips L from rfl]
    have hn := soft_trips_pos hpre
    rcases Softmax.fin3_cases j with rfl | rfl | rfl
    · have h0 := ht0 rfl
      have h1 : Softmax.genPos ⟨.gen 0, ii, tt, w, mm, l⟩ = 0 := by
        simp [Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.afterGen]
      have h2 : Softmax.sPos ⟨.gen 0, ii, tt, w, mm, l⟩ = 1 := by
        simp [Softmax.sPos, Softmax.Site.tile0Ld, Softmax.Site.tile0]
      rw [h1, h2, genTiles_item _ _ _ (by omega)]
      omega
    · have h0 := htr rfl
      have h1 : Softmax.genPos ⟨.gen 1, ii, tt, w, mm, l⟩ = tt + 1 := by
        simp [Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.inTrip,
          Softmax.Site.afterGen]
      have h2 : Softmax.sPos ⟨.gen 1, ii, tt, w, mm, l⟩ = 2 + tt := by
        simp [Softmax.sPos, Softmax.Site.tile0Ld, Softmax.Site.tile0, Softmax.Site.inTrip]
      rw [h1, h2, genTiles_item _ _ _ (by omega)]
      omega
    · have h0 := hla (.inr rfl)
      have h1 : Softmax.genPos ⟨.gen 2, ii, tt, w, mm, l⟩ = tt + 1 := by
        simp [Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.inTrip,
          Softmax.Site.afterGen]
      have h2 : Softmax.sPos ⟨.gen 2, ii, tt, w, mm, l⟩ = 1 + tt := by
        simp [Softmax.sPos]
      rw [h1, h2, genTiles_item _ _ _ (by omega)]
      omega
  · omega

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
