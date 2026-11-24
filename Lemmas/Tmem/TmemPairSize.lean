-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairOrder

@[expose] public section

namespace PTX.Tmem.Pair
noncomputable section

def rank (L : Launch) (X : Execution) (w : WarpRequest) : Nat :=
  ((X.tr (w.event L 0).1).take (w.indices 0)).countP Event.counts

private theorem counted_next (xs : List Event) (i pc : Nat) (group : CtaGroup) (dst : Option Loc)
    (a : Tmem.Request) (h : xs[i]? = some ⟨pc, .tc (.resource group dst a)⟩) :
    (xs.take (i + 1)).countP Event.counts = (xs.take i).countP Event.counts + 1 := by
  simp [List.take_add_one, h, Event.counts]

private theorem rank_lt {L : Launch} {X : Execution} {group : CtaGroup} {w : WarpRequest}
    (hw : w.Valid L X group) :
    rank L X w < (X.tr (w.event L 0).1).countP Event.counts := by
  have he := hw.2.2.1 0
  have hn := counted_next _ (w.indices 0) _ _ _ _ he
  have hm := (List.take_prefix (w.indices 0 + 1) (X.tr (w.event L 0).1)).countP_le
    (p := Event.counts)
  unfold rank
  omega

private theorem rank_lt_of_index {L : Launch} {X : Execution} {group : CtaGroup}
    {a b : WarpRequest} (ha : a.Valid L X group)
    (hg : (a.event L 0).1 = (b.event L 0).1) (hlt : a.indices 0 < b.indices 0) :
    rank L X a < rank L X b := by
  have hn := counted_next _ (a.indices 0) _ _ _ _ (ha.2.2.1 0)
  have hm := (List.take_prefix_take_left (l := X.tr (a.event L 0).1)
    (Nat.succ_le_of_lt hlt)).countP_le (p := Event.counts)
  calc
    rank L X a < ((X.tr (a.event L 0).1).take (a.indices 0 + 1)).countP Event.counts := by
      rw [hn]
      exact Nat.lt_succ_self _
    _ ≤ ((X.tr (a.event L 0).1).take (b.indices 0)).countP Event.counts := hm
    _ = rank L X b := by unfold rank; rw [hg]

private theorem rank_before {L : Launch} {X : Execution} {group : CtaGroup} {a b : WarpRequest}
    (ha : a.Valid L X group) (hab : a.Before b) : rank L X a < rank L X b :=
  rank_lt_of_index ha (by simp [WarpRequest.event, hab.1, hab.2.1]) (hab.2.2 0)

private theorem lane_zero_in_launch {L : Launch} {X : Execution} {group : CtaGroup}
    {w : WarpRequest} (hw : w.Valid L X group) : (w.event L 0).1 < L.threads := by
  have hc := Nat.mul_le_mul_right L.block (Nat.succ_le_of_lt hw.1)
  have hb := hw.2.1
  simp only [WarpRequest.event, Fin.val_zero, Nat.add_zero, Launch.threads]
  nlinarith

/-- Two requests whose lane-0 events are in one thread are performed by one warp. -/
private theorem same_warp_of_thread {L : Launch} {X : Execution} {g g' : CtaGroup}
    {a b : WarpRequest} (ha : a.Valid L X g) (hb : b.Valid L X g')
    (h : (a.event L 0).1 = (b.event L 0).1) : a.cta = b.cta ∧ a.warp = b.warp := by
  have h1 := ha.2.1
  have h2 := hb.2.1
  simp only [WarpRequest.event, Fin.val_zero, Nat.add_zero] at h
  have hl : a.warp * 32 < L.block := by nlinarith
  have hr : b.warp * 32 < L.block := by nlinarith
  have hc : a.cta = b.cta := by
    have e1 : (a.cta * L.block + a.warp * 32) / L.block = a.cta := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hl, Nat.zero_add]
    have e2 : (b.cta * L.block + b.warp * 32) / L.block = b.cta := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]
    rw [← e1, ← e2, h]
  rw [hc] at h
  exact ⟨hc, by omega⟩

/-- Warp requests with distinct lane-0 events, injectively keyed by their lane-0 thread and
the number of counted events before them, cannot outnumber counted instructions. -/
private theorem length_le_of_keys {L : Launch} {X : Execution} {α : Type} {rs : List α}
    (own : α → WarpRequest) (hv : ∀ r ∈ rs, ∃ group, (own r).Valid L X group)
    (hne : rs.Pairwise fun a b => (own a).event L 0 ≠ (own b).event L 0) (n : Nat)
    (hcount : ∀ g < L.threads, (X.tr g).countP Event.counts ≤ n) :
    rs.length ≤ L.threads * n := by
  let f := fun r : α => ((own r).event L 0).1 * n + rank L X (own r)
  have hrank : ∀ r ∈ rs, rank L X (own r) < n := fun r hr => by
    obtain ⟨_, hw⟩ := hv r hr
    exact (rank_lt hw).trans_le (hcount _ (lane_zero_in_launch hw))
  have hp : rs.Pairwise (fun a b => f a ≠ f b) := hne.imp_of_mem (by
    intro a b ha hb hab hf
    have hra := hrank a ha
    have hrb := hrank b hb
    have ht : ((own a).event L 0).1 = ((own b).event L 0).1 := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have : ((own a).event L 0).1 * n + n ≤ ((own b).event L 0).1 * n := by nlinarith
        simp only [f] at hf; omega
      · have : ((own b).event L 0).1 * n + n ≤ ((own a).event L 0).1 * n := by nlinarith
        simp only [f] at hf; omega
    obtain ⟨ga, hwa⟩ := hv a ha
    obtain ⟨gb, hwb⟩ := hv b hb
    have hidx : (own a).indices 0 = (own b).indices 0 := by
      rcases Nat.lt_trichotomy ((own a).indices 0) ((own b).indices 0) with hlt | heq | hlt
      · have := rank_lt_of_index hwa ht hlt
        simp only [f, ht] at hf; omega
      · exact heq
      · have := rank_lt_of_index hwb ht.symm hlt
        simp only [f, ht] at hf; omega
    exact hab (Prod.ext ht hidx))
  have hnodup : (rs.map f).Nodup := List.pairwise_map.mpr hp
  have hsub : (rs.map f).toFinset ⊆ Finset.range (L.threads * n) := by
    intro value hval
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hval)
    obtain ⟨_, hw⟩ := hv r hr
    have hl := lane_zero_in_launch hw
    have hk := hrank r hr
    refine Finset.mem_range.mpr ?_
    calc ((own r).event L 0).1 * n + rank L X (own r)
        < ((own r).event L 0).1 * n + n := by omega
      _ = (((own r).event L 0).1 + 1) * n := by ring
      _ ≤ L.threads * n := Nat.mul_le_mul_right _ hl
  have hc := Finset.card_le_card hsub
  simpa [List.toFinset_card_of_nodup hnodup] using hc

/-- Allocator records cannot outnumber counted instructions of the owner threads.
Failed polls do not affect this bound, even if arbitrarily many precede a request. -/
theorem RequestHistory.length_le {L : Launch} {X : Execution} {rs : List Requests}
    (hh : RequestHistory L X rs) (hord : rs.Pairwise fun a b => a.own.Ordered b.own) (n : Nat)
    (hcount : ∀ g < L.threads, (X.tr g).countP Event.counts ≤ n) :
    rs.length ≤ L.threads * n := by
  refine length_le_of_keys Requests.own (fun r hr => ⟨_, (hh r hr).2.2⟩) ?_ n hcount
  refine hord.imp_of_mem fun {a b} ha hb hab he => ?_
  have ht : (a.own.event L 0).1 = (b.own.event L 0).1 := congrArg Prod.fst he
  obtain ⟨hc, hw⟩ := same_warp_of_thread (hh a ha).2.2 (hh b hb).2.2 ht
  have := (hab hc hw).2.2 0
  have hi : a.own.indices 0 = b.own.indices 0 := congrArg Prod.snd he
  omega

/-- Pairings cannot outnumber counted instructions: each pairs a distinct even-CTA request. -/
theorem pairing_length_le {L : Launch} {X : Execution} (hv : HistoriesOk L X) (n : Nat)
    (hcount : ∀ g < L.threads, (X.tr g).countP Event.counts ≤ n) :
    X.tmemPairing.length ≤ L.threads * n :=
  length_le_of_keys Prod.fst (fun q hq => ⟨_, (hv.2.1 q hq).1.2.1⟩)
    (hv.2.2.imp fun h => h.1) n hcount

end
end PTX.Tmem.Pair
