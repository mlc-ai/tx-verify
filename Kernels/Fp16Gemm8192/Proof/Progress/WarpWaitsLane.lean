-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.ClusterStage
public import Kernels.Fp16Gemm8192.Proof.Progress.TmemLanes
public import Kernels.Fp16Gemm8192.Proof.Progress.TmemWaits
public import Lemmas.Step.WarpElect
public import Lemmas.Step.WarpBar
public import Lemmas.Step.ExitLast
public import Lemmas.Step.WarpShfl
public import Lemmas.Step.SetMaxNReg
public import Lemmas.Flow.ElectActor
public import Lemmas.Order.ElectOrdinal
public import Lemmas.Order.WarpBarOrdinal

@[expose] public section

/-! # The lanes of a warp at a collective site

For a pending thread `g` at a collective site (`ThreadD.coll`), whose last event is released:

* no lane of its warp has made an event of an instance of the site (`coll_matched`): the instance
  would hold `g`'s event too (DEP-WARP-SHUFFLE, DEP-WARP-ELECT, DEP-WARP-BARRIER), and `g` has made
  none;
* a lane that stopped before the site or is at an earlier site is pending and ranks below `g`
  (`lane_lower`);
* a lane at the site is released (`lane_released`): it has made no event before the site, or the
  shuffle, or its register request, granted to the whole warp with `g`'s, or warp 0's allocation,
  covered for the whole pair with `g`'s and made by every lane as one warp-collective instance. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every lane of a warp is a member of the full mask. -/
theorem member_full {lane : Nat} (hl : lane < 32) : electMember fullMask lane := by
  refine ⟨hl, ?_⟩
  have h32 : (4294967295 : Nat) = 2 ^ 32 - 1 := by norm_num
  rw [fullMask, h32, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hl

theorem laneOf_lt (L : Launch) (g : Nat) : laneOf L g < 32 := Nat.mod_lt _ (by norm_num)

/-- **No lane has made an event of an instance of the site.** The instance would hold an event of
`g`, which has made none. -/
theorem coll_matched (ht : ThreadFacts L X) (hX : Consistent L kernel Prod mem0 X) {g h : Nat}
    (hg : g < L.threads) {d : ThreadD} {s : CollSite}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hs : d.coll = some s)
    (hw : SameWarp L g h) {j : Nat} {e : Event} (he : X.get (h, j) = some e) (hm : s.Matches e)
    (hrun : ∃ t, Run kernel Prod L g {} (X.tr g) (some t)) :
    False := by
  have hwhg : SameWarp L h g := sameWarp_symm hw
  cases s
  case shfl =>
    obtain ⟨pc, m, a, b, c, recv, ok, rfl⟩ := hm
    have hk : X.ShflK (h, j) (((X.tr h).take j).countP Execution.isShfl) :=
      ⟨⟨pc, m, a, b, c, recv, ok, he⟩, rfl⟩
    rcases Step.shfl_lane_of_ready hX he hk hwhg with
      ⟨j', ⟨pc', m', a', b', c', r', o', hg'⟩, -⟩ | ⟨k, pce, hex, -⟩
    · exact ht.coll_none hg hσ hs hg' ⟨pc', m', a', b', c', r', o', rfl⟩
    · exact hrun.elim fun _ hr => hr.no_exit hex
  case warpBar =>
    obtain ⟨pc, inst, rfl⟩ := hm
    obtain ⟨x, m, inst', hy, ⟨pc', hg'⟩⟩ :=
      WarpBar.partner hX hwhg ⟨pc, he⟩ (member_full (laneOf_lt L g))
    obtain ⟨pcy, hy⟩ := hy
    rw [he] at hy
    simp only [Option.some.injEq, Event.mk.injEq, Kind.warpBar.injEq] at hy
    obtain ⟨-, rfl, rfl⟩ := hy
    exact ht.coll_none hg hσ hs hg' ⟨pc', inst, rfl⟩
  all_goals
    obtain ⟨inst, leader, rfl⟩ := hm
    obtain ⟨x, pc1, pc', mask1, mask', inst1, l1, l', hy, hg'⟩ :=
      ElectOrd.partner hX hwhg he (member_full (laneOf_lt L g))
    have hy' : X.get (h, j) = some ⟨pc1, .elect mask1 inst1 l1⟩ := hy
    rw [he] at hy'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.elect.injEq] at hy'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hy'
    obtain ⟨rfl, rfl, -, -⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ he hg' hwhg
    exact ht.coll_none hg hσ hs hg' ⟨inst, l', rfl⟩

/-- A thread at a collective site other than the shuffle has made an event. -/
theorem coll_ne_nil (ht : ThreadFacts L X) (hub : ¬ HasUb X) {g : Nat} (hg : g < L.threads)
    {d : ThreadD} {s : CollSite} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hs : d.coll = some s) (hsh : s ≠ .shfl) : X.tr g ≠ [] := by
  have hb := ht.coll_before hg (noUb_of hub g) hσ hs
  cases s
  case shfl => exact absurd rfl hsh
  case elect => obtain ⟨e, he, -⟩ := hb; rw [he]; simp
  case warpBar =>
    obtain ⟨j, pc, grp, dst, act, hj, -⟩ := hb
    intro h0
    have := len_of_get hj
    simp [h0] at this
  all_goals exact List.ne_nil_of_length_pos hb.1

/-- **A lane that stopped before the site, or is at an earlier site, is pending and ranks below
`g`.** -/
theorem lane_lower (ht : ThreadFacts L X) (hX : Consistent L kernel Prod mem0 X) (hub : ¬ HasUb X)
    {g h : Nat} (hg : g < L.threads) {d : ThreadD} {s : CollSite}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hs : d.coll = some s)
    (hrel : Step.Released L X g) (hw : SameWarp L g h)
    (hlow : (Frame.stateAt (code L) X h (X.tr h).length = none ∧
      (∀ pc, (X.tr h).getLast? ≠ some ⟨pc, .exit⟩) ∧
        s ≠ .shfl) ∨
      ∃ d', Frame.stateAt (code L) X h (X.tr h).length = some (some d') ∧ d'.exitOff = none ∧
        d'.vtime L h (X.tr h) + 2 ≤ d.vtime L g (X.tr g)) :
    Descent.Obl L X (.thread h) ∧ rank L X (.thread h) < rank L X (.thread g) := by
  have hrg : rank L X (.thread g) = d.vtime L g (X.tr g) := by
    rw [rank_released hrel, threadTime_of hσ (ThreadD.coll_exitOff hs)]
  have hrh := rank_thread_le (L := L) (X := X) (g := h)
  have hsh : s ≠ .shfl := by
    rcases hlow with ⟨-, -, h⟩ | ⟨d', -, -, hv⟩
    · exact h
    · rintro rfl
      have := ThreadD.coll_vtime hs L g (X.tr g)
      cases d with
      | inl p =>
        obtain ⟨site, w⟩ := p
        cases site <;> simp [ThreadD.coll] at hs
        simp [ThreadD.vtime, Prologue.Site.vtime] at hv
      | inr r =>
        cases r with
        | mma m => obtain ⟨site, _, _, _, _, _, _, _⟩ := m; cases site <;> simp [ThreadD.coll] at hs
        | sched sd => obtain ⟨site, _, _, _, _⟩ := sd; cases site <;> simp [ThreadD.coll] at hs
        | loader l => simp [ThreadD.coll] at hs
        | cons c => simp [ThreadD.coll] at hs
  have hne := coll_ne_nil ht hub hg hσ hs hsh
  have hcl : L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block) := by rw [hw.1.2.2]
  have hv2 := ThreadD.coll_vtime hs L g (X.tr g) hsh
  rcases hlow with ⟨hn, hnx, -⟩ | ⟨d', hσh, hx, hv⟩
  · refine ⟨⟨hw.1.2.1, not_canceled_of_peer hX hg hne hcl, hnx⟩, ?_⟩
    have h0 : threadTime L X h = 0 := by simp [threadTime, hn]
    omega
  · have hnx : ∀ pc, (X.tr h).getLast? ≠ some ⟨pc, .exit⟩ := by
      intro pc hl
      rw [ht.exited_state hw.1.2.1 hl] at hσh
      cases hσh
    refine ⟨⟨hw.1.2.1, not_canceled_of_peer hX hg hne hcl, hnx⟩, ?_⟩
    rw [threadTime_of hσh hx] at hrh
    omega

/-- A thread without events is released. -/
theorem released_nil {Y : Execution} {h : Nat} (h0 : Y.tr h = []) : Step.Released L Y h :=
  Step.Released.of_get fun q hq => by simp [Execution.get, h0] at hq

/-- A thread whose last event is no cluster operation, register request, Tensor Core operation,
named barrier or group wait is released: its last event does not block. -/
theorem released_of_kind {h : Nat} {q : Event}
    (hq : X.get (h, (X.tr h).length - 1) = some q) (hcl : ∀ op, q.kind ≠ .cluster op)
    (hsr : ∀ inc n inst, q.kind ≠ .setMaxReg inc n inst) (htc : ∀ k, q.kind ≠ .tc k)
    (hb : ∀ id c m, q.kind ≠ .bar id c m) (hbw : ∀ m n, q.kind ≠ .bulkWait m n)
    (haw : ∀ n, q.kind ≠ .asyncWait n) : Step.Released L X h := by
  refine Step.Released.of_get fun q' hq' hk => ?_
  rw [hq] at hq'
  obtain rfl := Option.some.inj hq'
  obtain ⟨pc, k⟩ := q
  cases k <;> simp_all [Kind.resume]

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
