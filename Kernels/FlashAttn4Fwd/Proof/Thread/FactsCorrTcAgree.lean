-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrTrip
public import Lemmas.Flow.VoteSeq

@[expose] public section

/-! # The correction parts of `Cross.TcAgree`, `Cross.TcExitAgree` and `Cross.TcExitAbove`

A correction thread makes its warp-collective `tcgen05` events in blocks: a rescale of
twenty-five events after each vote with a nonzero ballot (per chunk a load, its wait and a
store; then the wait for the stores), and thirty-two events in each item's final part (per stage
and chunk a load and its wait). With `n` the trips and `V = 2 (n - 1)` the votes of an item,
`S m` the nonzero ballots among the thread's first `m`, the rescale of vote `m` of item `i` starts
at ordinal `25 S m + 32 i` and the final part of item `i` at `25 S (V (i + 1)) + 32 i`
(`corr_tc_pos`, from `Counts.tcColl`, `Counts.voteN` and `Counts.rsNz`).

The `k`-th ballots of the lanes of a warp are equal: no lane exits before its `k`-th ballot
(a lane exits after its `V T` ballots, `T` its items, `corr_no_vote_exit`), so each bit of either
ballot is the predicate of its lane (`ballot_eq`). The lanes' counts `S` therefore agree, and the
ordinal of an event fixes its block and its offset in the block (`blk_rr`, `blk_ff`, `blk_rf`):
the site, hence the position and the static operands, which name the warp's Tensor Memory lanes.
At its exit a lane has made `25 S (V T) + 32 T` of them, more than the ordinal of any. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Correction

/-- The static operands of a site's warp-collective `tcgen05` event. -/
def tcStat (L : Launch) (g : Nat) : Site → TcKind
  | .rld s j | .fld s j => .ld (tmem L g (256 + 128 * s.val + 16 * j.val)) [] .s32x32b
  | .rst s j => .st (tmem L g (256 + 128 * s.val + 16 * j.val)) [] .s32x32b
  | .rwait _ => .waitSt
  | _ => .waitLd

/-- The offset of a rescale site's event in its rescale. -/
def rsOff : Site → Nat
  | .rld _ j => 3 * j.val
  | .rldW _ j => 3 * j.val + 1
  | .rst _ j => 3 * j.val + 2
  | _ => 24

/-- The stage of a site. -/
def stOf : Site → Nat
  | .rld s _ | .rldW s _ | .rst s _ | .rwait s | .fld s _ | .fldW s _ => s.val
  | _ => 0

/-- A site of a rescale. -/
def IsRs (s : Site) : Prop :=
  (∃ st j, s = .rld st j) ∨ (∃ st j, s = .rldW st j) ∨ (∃ st j, s = .rst st j) ∨
    ∃ st, s = .rwait st

/-- A site of a final part with a warp-collective `tcgen05` event. -/
def IsFin (s : Site) : Prop := (∃ st j, s = .fld st j) ∨ ∃ st j, s = .fldW st j

/-- **The sites of warp-collective `tcgen05` events**, with their static operands. -/
theorem tc_site {g pc : Nat} {kd : TcKind} {d : D} (hev : Ev L g d ⟨pc, .tc kd⟩) :
    (IsRs d.site ∨ IsFin d.site) ∧ tcStatic kd = tcStat L g d.site := by
  obtain ⟨-, hk⟩ := hev
  obtain ⟨site, i, t, aw, a, o⟩ := d
  cases site <;> simp only [Kind.tc.injEq, reduceCtorEq, exists_false, false_and] at hk
  all_goals try (obtain ⟨_, rfl⟩ := hk)
  all_goals first
    | exact ⟨.inl (.inl ⟨_, _, rfl⟩), rfl⟩
    | exact ⟨.inl (.inr (.inl ⟨_, _, rfl⟩)), rfl⟩
    | exact ⟨.inl (.inr (.inr (.inl ⟨_, _, rfl⟩))), rfl⟩
    | exact ⟨.inl (.inr (.inr (.inr ⟨_, rfl⟩))), rfl⟩
    | exact ⟨.inr (.inl ⟨_, _, rfl⟩), rfl⟩
    | exact ⟨.inr (.inr ⟨_, _, rfl⟩), rfl⟩

theorem vote_site {g pc m : Nat} {a : Bool} {b : BitVec 32} {d : D}
    (hev : Ev L g d ⟨pc, .vote m a b⟩) : ∃ st, d.site = .vote st := by
  obtain ⟨-, hk⟩ := hev
  obtain ⟨site, i, t, aw, a, o⟩ := d
  cases site <;> simp only [reduceCtorEq, exists_false, false_and] at hk
  all_goals exact ⟨_, rfl⟩

theorem rs_facts {d : D} (h : IsRs d.site) :
    tcLack d = 25 - rsOff d.site ∧ rsOff d.site < 25 ∧ finTc d = 0 ∧ stOf d.site < 2 ∧
      votePos L 0 d + votePos L 1 d = 2 * d.t + stOf d.site + 1 ∧ d.site.inTrip = true ∧
      d.site.inItem = true := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  simp only at h ⊢
  rcases h with ⟨st, j, rfl⟩ | ⟨st, j, rfl⟩ | ⟨st, j, rfl⟩ | ⟨st, rfl⟩ <;> fin_cases st <;>
    simp [tcLack, rsOff, finTc, stOf, votePos, Site.inTrip, Site.inItem] <;> omega

theorem fin_facts {d : D} (h : IsFin d.site) :
    tcLack d = 0 ∧ finTc d < 32 ∧ votePos L 0 d + votePos L 1 d = 2 * (trips L - 1) ∧
      d.site.inItem = true := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  simp only at h ⊢
  rcases h with ⟨st, j, rfl⟩ | ⟨st, j, rfl⟩ <;> fin_cases st <;>
    simp [tcLack, finTc, votePos, Site.inItem] <;> omega

theorem vote_facts {d : D} {st : Fin 2} (h : d.site = .vote st) :
    votePos L 0 d + votePos L 1 d = 2 * d.t + st.val ∧ d.site.inTrip = true ∧
      d.site.inItem = true := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  simp only at h ⊢
  subst h
  fin_cases st <;> simp [votePos, Site.inTrip, Site.inItem] <;> omega

theorem rs_site_eq {x y : Site} (hx : IsRs x) (hy : IsRs y) (hs : stOf x = stOf y)
    (ho : rsOff x = rsOff y) : x = y := by
  rcases hx with ⟨s, j, rfl⟩ | ⟨s, j, rfl⟩ | ⟨s, j, rfl⟩ | ⟨s, rfl⟩ <;>
    rcases hy with ⟨s', j', rfl⟩ | ⟨s', j', rfl⟩ | ⟨s', j', rfl⟩ | ⟨s', rfl⟩ <;>
    simp only [stOf, rsOff] at hs ho <;>
    simp only [Site.rld.injEq, Site.rldW.injEq, Site.rst.injEq, Site.rwait.injEq, Fin.ext_iff,
      reduceCtorEq] <;> omega

theorem fin_site_eq {d d' : D} (hx : IsFin d.site) (hy : IsFin d'.site) (ho : finTc d = finTc d') :
    d.site = d'.site := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  obtain ⟨site', i', t', aw', a', o'⟩ := d'
  simp only at hx hy ho ⊢
  rcases hx with ⟨s, j, rfl⟩ | ⟨s, j, rfl⟩ <;> rcases hy with ⟨s', j', rfl⟩ | ⟨s', j', rfl⟩ <;>
    simp only [finTc] at ho <;>
    simp only [Site.fld.injEq, Site.fldW.injEq, Fin.ext_iff, reduceCtorEq] <;> omega

/-- A correction ballot event is a ballot event (`isBallot`). -/
theorem isVote_eq_isBallot : isVote = isBallot := by
  funext e
  obtain ⟨pc, k⟩ := e
  cases k <;> rfl

end Correction

/-- The nonzero ballots among thread `g`'s first `m` ballot events. -/
def vS (X : Execution) (g m : Nat) : Nat := (List.range m).countP (voteNz X g)

theorem vS_mono (g : Nat) {a b : Nat} (h : a ≤ b) : vS X g a ≤ vS X g b :=
  (List.range_sublist.2 h).countP_le

theorem vS_succ {g m : Nat} (hz : voteNz X g m = true) : vS X g (m + 1) = vS X g m + 1 := by
  simp [vS, List.range_succ, List.countP_append, hz]

theorem vS_congr {g h M : Nat} (hz : ∀ k < M, voteNz X g k = voteNz X h k) :
    vS X g M = vS X h M :=
  List.countP_congr fun k hk => by rw [hz k (List.mem_range.1 hk)]

/-! ### The arithmetic of the blocks -/

theorem lt_of_mul {V i i' m m' : Nat} (h1 : V * i ≤ m) (h2 : m ≤ m') (h3 : m' < V * (i' + 1)) :
    i ≤ i' := by
  have := Nat.lt_of_mul_lt_mul_left (a := V) (by omega : V * i < V * (i' + 1))
  omega

/-- Two rescale events with one ordinal are of one vote, at one offset. -/
theorem blk_rr {S : Nat → Nat} (hmono : ∀ a b, a ≤ b → S a ≤ S b) {V i i' m m' o o' N : Nat}
    (h1 : V * i ≤ m) (h2 : m < V * (i + 1)) (h1' : V * i' ≤ m') (h2' : m' < V * (i' + 1))
    (hz : S (m + 1) = S m + 1) (hz' : S (m' + 1) = S m' + 1) (ho : o < 25) (ho' : o' < 25)
    (hN : N = 25 * S m + 32 * i + o) (hN' : N = 25 * S m' + 32 * i' + o') : m = m' ∧ o = o' := by
  rcases Nat.lt_trichotomy m m' with h | rfl | h
  · have := lt_of_mul h1 h.le h2'
    have := hmono (m + 1) m' h
    omega
  · have := lt_of_mul h1 le_rfl h2'
    have := lt_of_mul h1' le_rfl h2
    omega
  · have := lt_of_mul h1' h.le h2
    have := hmono (m' + 1) m h
    omega

/-- Two final-part events with one ordinal are of one item, at one offset. -/
theorem blk_ff {S : Nat → Nat} (hmono : ∀ a b, a ≤ b → S a ≤ S b) {V i i' o o' N : Nat}
    (ho : o < 32) (ho' : o' < 32) (hN : N = 25 * S (V * (i + 1)) + 32 * i + o)
    (hN' : N = 25 * S (V * (i' + 1)) + 32 * i' + o') : i = i' ∧ o = o' := by
  rcases Nat.lt_trichotomy i i' with h | rfl | h
  · have := hmono _ _ (Nat.mul_le_mul_left V (show i + 1 ≤ i' + 1 by omega))
    omega
  · omega
  · have := hmono _ _ (Nat.mul_le_mul_left V (show i' + 1 ≤ i + 1 by omega))
    omega

/-- A rescale event and a final-part event have different ordinals. -/
theorem blk_rf {S : Nat → Nat} (hmono : ∀ a b, a ≤ b → S a ≤ S b) {V i i' m o o' N : Nat}
    (h1 : V * i ≤ m) (h2 : m < V * (i + 1)) (hz : S (m + 1) = S m + 1) (ho : o < 25)
    (ho' : o' < 32) (hN : N = 25 * S m + 32 * i + o)
    (hN' : N = 25 * S (V * (i' + 1)) + 32 * i' + o') : False := by
  rcases Nat.lt_or_ge i' i with h | h
  · have := hmono _ _ (show V * (i' + 1) ≤ m from
      (Nat.mul_le_mul_left V (show i' + 1 ≤ i by omega)).trans h1)
    omega
  · have := hmono _ _ (show m + 1 ≤ V * (i' + 1) from
      h2.trans_le (Nat.mul_le_mul_left V (by omega)))
    omega

theorem corr_items_eq {g h : Nat} (hs : SameWarp L g h) :
    Correction.items L g = Correction.items L h := by
  obtain ⟨⟨-, -, hc⟩, -⟩ := hs
  simp only [Correction.items, clusterOf, ctaOf]
  rw [hc]

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **The block and the offset of a correction thread's warp-collective `tcgen05` event.** -/
theorem corr_tc_pos {g k pc : Nat} {kd : TcKind} (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    (he : X.get (g, k) = some ⟨pc, .tc kd⟩) :
    ∃ d : Correction.D, pc = d.site.pc ∧ tcStatic kd = Correction.tcStat L g d.site ∧
      d.i < Correction.items L g ∧
      ((Correction.IsRs d.site ∧ ∃ m, 2 * (Correction.trips L - 1) * d.i ≤ m ∧
          m < 2 * (Correction.trips L - 1) * (d.i + 1) ∧ m % 2 = Correction.stOf d.site ∧
          voteNz X g m = true ∧ m + 1 ≤ ((X.tr g).take k).countP Correction.isVote ∧
          ((X.tr g).take k).countP isTcColl =
            25 * vS X g m + 32 * d.i + Correction.rsOff d.site) ∨
        (Correction.IsFin d.site ∧
          2 * (Correction.trips L - 1) * (d.i + 1) ≤ ((X.tr g).take k).countP Correction.isVote ∧
          ((X.tr g).take k).countP isTcColl =
            25 * vS X g (2 * (Correction.trips L - 1) * (d.i + 1)) + 32 * d.i +
              Correction.finTc d ∧ Correction.finTc d < 32)) := by
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by cases h) with ⟨p, -, hk⟩ |
    ⟨d, t, ins, o, -, hc, hi, -, -, -, hev⟩
  · cases hk
  have hev := hev (by simp)
  obtain ⟨hcls, hst⟩ := Correction.tc_site hev
  have hpc : pc = d.site.pc := hev.1
  have hvN := hc.voteN
  have htc := hc.tcColl
  rw [countP_nz_take, ← Correction.isVote_eq_isBallot] at htc
  have hm2 : ∀ x y : Nat, 2 * (Correction.trips L - 1) * (x + y) =
      2 * (Correction.trips L - 1) * x + 2 * (Correction.trips L - 1) * y := fun x y => by ring
  rcases hcls with hr | hf
  · obtain ⟨hlack, hoff, hfin, hs2, hvp, htrip, hitem⟩ := Correction.rs_facts (L := L) hr
    have htr := hi.trip htrip
    -- the vote of the rescale has a nonzero ballot
    have hz : voteNz X g (2 * (Correction.trips L - 1) * d.i +
        (2 * d.t + Correction.stOf d.site)) = true := by
      obtain ⟨v, hv, vpc, vm, va, vb, hget, hb, hcnt⟩ := hc.rsNz (by omega)
      have hvk : v < k := by rw [List.length_take] at hv; omega
      rw [take_get hvk] at hget
      rw [take_take_le hvk.le] at hcnt
      have hn := nthEv_eq (p := Correction.isVote) hget rfl
      rw [show ((X.tr g).take v).countP Correction.isVote =
        2 * (Correction.trips L - 1) * d.i + (2 * d.t + Correction.stOf d.site) by omega] at hn
      unfold voteNz
      rw [← Correction.isVote_eq_isBallot, hn, hget]
      simpa [isNzVote] using hb
    refine ⟨d, hpc, hst, hi.item hitem, .inl ⟨hr, 2 * (Correction.trips L - 1) * d.i +
      (2 * d.t + Correction.stOf d.site), by omega, ?_, ?_, hz, by omega, ?_⟩⟩
    · rw [hm2, Nat.mul_one]; omega
    · rw [Nat.mul_assoc]; omega
    · rw [show ((X.tr g).take k).countP Correction.isVote =
        2 * (Correction.trips L - 1) * d.i + (2 * d.t + Correction.stOf d.site) + 1 by omega,
        List.range_succ, List.countP_append, List.countP_singleton, hz] at htc
      unfold vS
      simp only [ite_true] at htc
      omega
  · obtain ⟨hlack, hfin, hvp, hitem⟩ := Correction.fin_facts (L := L) hf
    refine ⟨d, hpc, hst, hi.item hitem, .inr ⟨hf, ?_, ?_, hfin⟩⟩
    · rw [hm2, Nat.mul_one]; omega
    · rw [show ((X.tr g).take k).countP Correction.isVote =
        2 * (Correction.trips L - 1) * (d.i + 1) by rw [hm2, Nat.mul_one]; omega] at htc
      unfold vS
      omega

/-- A correction thread makes no mode vote. -/
theorem corr_no_voteMode {g k pc m : Nat} {mode : VoteMode} {a r : Bool} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (he : X.get (g, k) = some ⟨pc, .voteMode mode m a r⟩) : False := by
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by cases h) with ⟨p, -, hk⟩ |
    ⟨d, t, ins, o, -, -, -, -, -, -, hev⟩
  · cases hk
  obtain ⟨-, hk⟩ := hev (by simp)
  obtain ⟨site, i, tt, aw, aa, o'⟩ := d
  cases site <;> simp at hk

/-- A correction thread's votes with the full member mask are its ballot events. -/
theorem corr_maskCount {g k : Nat} (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) :
    ((X.tr g).take k).countP (fun ev => (voteClass ev.kind).any (·.mask == 2 ^ 32 - 1)) =
      ((X.tr g).take k).countP Correction.isVote := by
  apply List.countP_congr
  intro ev hev
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hev)
  have he : X.get (g, i) = some ev := hi
  obtain ⟨pc, kd⟩ := ev
  cases kd
  case vote m a b =>
    have hm := corr_vote_mask hpre hX ht hw hw' he
    generalize (2 ^ 32 - 1 : Nat) = M at hm ⊢
    subst hm
    simp only [voteClass, Correction.isVote, Option.any_some, beq_self_eq_true]
  case voteMode mode m a r => exact (corr_no_voteMode hpre hX ht hw hw' he).elim
  all_goals rfl

/-- A correction thread's ballot event with `k` earlier ones has `k` below `V T`. -/
theorem corr_vote_bound {g j k pc m : Nat} {a : Bool} {b : BitVec 32} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (he : X.get (g, j) = some ⟨pc, .vote m a b⟩)
    (hcnt : ((X.tr g).take j).countP Correction.isVote = k) :
    k < 2 * (Correction.trips L - 1) * Correction.items L g := by
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by cases h) with ⟨p, -, hk⟩ |
    ⟨d, t, ins, o, -, hc, hi, -, -, -, hev⟩
  · cases hk
  obtain ⟨st, hs⟩ := Correction.vote_site (hev (by simp))
  obtain ⟨hvp, htrip, hitem⟩ := Correction.vote_facts (L := L) hs
  have htr := hi.trip htrip
  have hit := hi.item hitem
  have hvN := hc.voteN
  have hle := Nat.mul_le_mul_left (2 * (Correction.trips L - 1)) (show d.i + 1 ≤ _ from hit)
  rw [Nat.mul_add, Nat.mul_one] at hle
  have := st.isLt
  omega

/-- At its exit a correction thread has made `V T` ballot events and `25 S (V T) + 32 T`
warp-collective `tcgen05` events. -/
theorem corr_exit_counts {y kk pc : Nat} (hw : 8 ≤ warpOf L y) (hw' : warpOf L y < 12)
    (he : X.get (y, kk) = some ⟨pc, .exit⟩) :
    ((X.tr y).take kk).countP Correction.isVote =
        2 * (Correction.trips L - 1) * Correction.items L y ∧
      ((X.tr y).take kk).countP isTcColl =
        25 * vS X y (2 * (Correction.trips L - 1) * Correction.items L y) +
          32 * Correction.items L y := by
  obtain ⟨d, -, hc, hi, hs⟩ := corr_exit_state hpre hX ht hw hw' he
  have hti := hi.tail (by rw [hs]; rfl) (by rw [hs]; simp) (by rw [hs]; simp)
    (fun _ => by rw [hs]; simp)
  have hvN := hc.voteN
  have htc := hc.tcColl
  rw [countP_nz_take, ← Correction.isVote_eq_isBallot] at htc
  obtain ⟨site, i, t, aw, a, o⟩ := d
  simp only at hs hti hvN htc
  subst hs hti
  simp only [Correction.votePos, Correction.tcLack, Correction.finTc, Nat.add_zero] at hvN htc
  refine ⟨hvN, ?_⟩
  rw [hvN] at htc
  exact htc

/-- **No lane of a correction warp exits before the warp's `k`-th ballot.** -/
theorem corr_no_vote_exit {g y j k pc m : Nat} {a : Bool} {b : BitVec 32}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (hs : SameWarp L g y)
    (he : X.get (g, j) = some ⟨pc, .vote m a b⟩)
    (hcnt : ((X.tr g).take j).countP Correction.isVote = k) :
    ¬ MaskExited voteClass X y (2 ^ 32 - 1) k := by
  rintro ⟨kk, pc', he', hle⟩
  have hwy : warpOf L y = warpOf L g := hs.2.symm
  have hb := corr_vote_bound hpre hX ht hw hw' he hcnt
  rw [corr_maskCount hpre hX ht (by omega) (by omega),
    (corr_exit_counts hpre hX ht (by omega) (by omega) he').1, ← corr_items_eq hs] at hle
  omega

/-- **The `k`-th ballots of two lanes of a correction warp are equally nonzero.** -/
theorem corr_voteNz_eq {g h j k pc m : Nat} {a : Bool} {b : BitVec 32}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (hs : SameWarp L g h)
    (he : X.get (g, j) = some ⟨pc, .vote m a b⟩)
    (hcnt : ((X.tr g).take j).countP Correction.isVote = k) : voteNz X g k = voteNz X h k := by
  obtain rfl := corr_vote_mask hpre hX ht hw hw' he
  have hwh : warpOf L h = warpOf L g := hs.2.symm
  have hK : X.MaskK voteClass (g, j) (2 ^ 32 - 1) k :=
    ⟨⟨_, ⟨_, .ballot, a⟩, he, rfl, rfl⟩, (corr_maskCount hpre hX ht hw hw').trans hcnt⟩
  have hlh : laneOf L h < 32 := Nat.mod_lt _ (by decide)
  have hbit : (2 ^ 32 - 1 : Nat).testBit (laneOf L h) = true := by
    rw [Nat.testBit_two_pow_sub_one]; simpa using hlh
  rcases ballot_lane hX he hK hlh hbit with ⟨v', j', pc', kd, he', hc', hK'⟩ | hx
  · rw [← sameWarp_lane L hs] at he' hK'
    obtain ⟨b', rfl⟩ : ∃ b', kd = .vote (2 ^ 32 - 1) v' b' := by
      cases kd with
      | vote m a b =>
        simp only [voteClass, Option.some.injEq, WarpPart.mk.injEq] at hc'
        obtain ⟨rfl, -, rfl⟩ := hc'
        exact ⟨_, rfl⟩
      | voteMode => exact (corr_no_voteMode hpre hX ht (by omega) (by omega) he').elim
      | _ => simp [voteClass] at hc'
    have hblk : L.block % 32 = 0 := by rw [hpre.block]
    obtain ⟨part, hpart⟩ := ballot_instance hX he hK
    have hbb := ballot_eq hX.vote hblk hs he hK he' hK' hpart
      (fun y hy => corr_no_vote_exit hpre hX ht hw hw' hy he hcnt)
    subst hbb
    have hc2 : ((X.tr h).take j').countP isBallot = k := by
      rw [← Correction.isVote_eq_isBallot, ← corr_maskCount hpre hX ht (by omega) (by omega)]
      exact hK'.2
    have h1 := nthEv_eq (p := isBallot) he rfl
    have h2 := nthEv_eq (p := isBallot) he' rfl
    rw [← Correction.isVote_eq_isBallot, hcnt, Correction.isVote_eq_isBallot] at h1
    rw [hc2] at h2
    unfold voteNz
    rw [h1, h2, he, he']
    rfl
  · exact absurd hx (by
      rw [← sameWarp_lane L hs]
      exact corr_no_vote_exit hpre hX ht hw hw' hs he hcnt)

/-- The lanes of a correction warp agree on the nonzero ballots among the first `M`, when one of
them made `M` ballot events. -/
theorem corr_vS_eq {g h kk M : Nat} (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    (hs : SameWarp L g h) (hM : M ≤ ((X.tr g).take kk).countP Correction.isVote) :
    vS X g M = vS X h M := by
  refine vS_congr fun k hk => ?_
  obtain ⟨j, e, -, he, hv, hc⟩ :=
    exists_nthEv (X := X) (p := Correction.isVote) (g := g) (k := kk) (n := k) (by omega)
  obtain ⟨epc, ek⟩ := e
  cases ek with
  | vote m a b => exact corr_voteNz_eq hpre hX ht hw hw' hs he hc
  | _ => simp [Correction.isVote] at hv

/-- **The correction part of `Cross.TcAgree`.** -/
theorem Cross.TcAgree_corr {g h k k' pc pc' n : Nat} {kd kd' : TcKind} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (hs : SameWarp L g h) (he : X.get (g, k) = some ⟨pc, .tc kd⟩)
    (he' : X.get (h, k') = some ⟨pc', .tc kd'⟩) (hn : X.TcK (g, k) n) (hn' : X.TcK (h, k') n) :
    pc = pc' ∧ tcStatic kd = tcStatic kd' := by
  have hwh : warpOf L h = warpOf L g := hs.2.symm
  have hhs : SameWarp L h g := ⟨⟨hs.1.2.1, hs.1.1, hs.1.2.2.symm⟩, hs.2.symm⟩
  obtain ⟨d, hpc, hst, hit, hA⟩ := corr_tc_pos hpre hX ht hw hw' he
  obtain ⟨d', hpc', hst', hit', hB⟩ := corr_tc_pos hpre hX ht (by omega) (by omega) he'
  have hN := hn.2
  have hN' := hn'.2
  have hmono : ∀ a b, a ≤ b → vS X g a ≤ vS X g b := fun a b => vS_mono g
  have htm : ∀ c, Correction.tmem L g c = Correction.tmem L h c := fun c => by
    simp only [Correction.tmem]
    rw [corr_kOf hw hw', corr_kOf (by omega) (by omega), hwh]
  have hstat : ∀ s, Correction.tcStat L g s = Correction.tcStat L h s := fun s => by
    cases s <;> simp only [Correction.tcStat, htm]
  suffices hsite : d.site = d'.site by
    refine ⟨by rw [hpc, hpc', hsite], ?_⟩
    rw [hst, hst', hsite, hstat]
  have hE : ∀ {M}, M ≤ ((X.tr h).take k').countP Correction.isVote → vS X h M = vS X g M :=
    fun hM => corr_vS_eq hpre hX ht (by omega) (by omega) hhs hM
  simp only at hN hN'
  rcases hA with ⟨hr, m, h1, h2, hm2, hz, hcm, hcnt⟩ | ⟨hf, hcm, hcnt, hfo⟩ <;>
    rcases hB with ⟨hr', m', h1', h2', hm2', hz', hcm', hcnt'⟩ | ⟨hf', hcm', hcnt', hfo'⟩
  · have hzS := vS_succ hz
    have hzS' : vS X g (m' + 1) = vS X g m' + 1 := by
      rw [← hE hcm', ← hE (by omega)]; exact vS_succ hz'
    rw [hE (by omega)] at hcnt'
    obtain ⟨rfl, ho⟩ := blk_rr hmono h1 h2 h1' h2' hzS hzS'
      (Correction.rs_facts (L := L) hr).2.1 (Correction.rs_facts (L := L) hr').2.1
      (hN.symm.trans hcnt) (hN'.symm.trans hcnt')
    exact Correction.rs_site_eq hr hr' (hm2.symm.trans hm2') ho
  · rw [hE hcm'] at hcnt'
    exact (blk_rf hmono h1 h2 (vS_succ hz) (Correction.rs_facts (L := L) hr).2.1 hfo'
      (hN.symm.trans hcnt) (hN'.symm.trans hcnt')).elim
  · have hzS' : vS X g (m' + 1) = vS X g m' + 1 := by
      rw [← hE hcm', ← hE (by omega)]; exact vS_succ hz'
    rw [hE (by omega)] at hcnt'
    exact (blk_rf hmono h1' h2' hzS' (Correction.rs_facts (L := L) hr').2.1 hfo
      (hN'.symm.trans hcnt') (hN.symm.trans hcnt)).elim
  · rw [hE hcm'] at hcnt'
    obtain ⟨-, ho⟩ := blk_ff hmono hfo hfo' (hN.symm.trans hcnt) (hN'.symm.trans hcnt')
    exact Correction.fin_site_eq hf hf' ho

/-- **The correction part of `Cross.TcExitAgree`.** -/
theorem Cross.TcExitAgree_corr {g h k k' pc pc' : Nat} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (hs : SameWarp L g h) (he : X.get (g, k) = some ⟨pc, .exit⟩)
    (he' : X.get (h, k') = some ⟨pc', .exit⟩) :
    ((X.tr g).take k).countP isTcColl = ((X.tr h).take k').countP isTcColl := by
  have hwh : warpOf L h = warpOf L g := hs.2.symm
  obtain ⟨hv, hc⟩ := corr_exit_counts hpre hX ht hw hw' he
  obtain ⟨-, hc'⟩ := corr_exit_counts hpre hX ht (by omega) (by omega) he'
  rw [hc, hc', ← corr_items_eq hs, corr_vS_eq hpre hX ht hw hw' hs hv.ge]

/-- **The correction part of `Cross.TcExitAbove`.** -/
theorem Cross.TcExitAbove_corr {g h k k' pc n : Nat} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (hs : SameWarp L g h) (he' : X.get (h, k') = some ⟨pc, .exit⟩)
    (hn : X.TcK (g, k) n) : n < ((X.tr h).take k').countP isTcColl := by
  have hwh : warpOf L h = warpOf L g := hs.2.symm
  have hhs : SameWarp L h g := ⟨⟨hs.1.2.1, hs.1.1, hs.1.2.2.symm⟩, hs.2.symm⟩
  obtain ⟨⟨⟨epc, ek⟩, hx, hcl⟩, hN⟩ := hn
  obtain ⟨tk, rfl⟩ : ∃ tk, ek = .tc tk := by cases ek <;> simp_all [isTcColl]
  obtain ⟨hv, hc⟩ := corr_exit_counts hpre hX ht (by omega) (by omega) he'
  rw [hc, ← corr_items_eq hs, corr_vS_eq hpre hX ht (by omega) (by omega) hhs
    (by rw [hv, corr_items_eq hs])]
  simp only at hN
  subst hN
  have hmono : ∀ a b, a ≤ b → vS X g a ≤ vS X g b := fun a b => vS_mono g
  obtain ⟨d, -, -, hit, hA⟩ := corr_tc_pos hpre hX ht hw hw' hx
  have hle := Nat.mul_le_mul_left (2 * (Correction.trips L - 1))
    (show d.i + 1 ≤ Correction.items L g from hit)
  rcases hA with ⟨hr, m, -, h2, -, hz, -, hcnt⟩ | ⟨hf, -, hcnt, hfo⟩
  · have := hmono (m + 1) _ (h2.trans_le hle)
    have := vS_succ hz
    have := (Correction.rs_facts (L := L) hr).2.1
    omega
  · have := hmono _ _ hle
    omega

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
