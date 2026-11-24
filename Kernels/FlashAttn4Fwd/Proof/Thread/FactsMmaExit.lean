-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsTmemLife
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsAccess
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaCommitCount
public import Lemmas.Flow.NotRead

@[expose] public section

/-! # The MMA warp's end

A lane of warp 12 exits at the exit site, after its hand-off arrival on the peer's handshake
barrier and a successful poll of its own (`Counts.handoff`, `Counts.dealloc`; the arrival comes
before the wait site, `ExitFacts.mma_exit`). At its hand-off, a lane of the leader CTA has done
every item of its cluster (`Counts.done`), so it has polled each ring full barrier for every
use of those items (`Counts.qFull`, `Counts.kvFull`; `ExitFacts.mma_full`).

The premises of the cross-warp layer that are facts of the MMA role are proved here for warp 12
(`Cross.*_mma`): the exit after two `bar.sync 2`, the uses of the other CTA before the second
one, the base-word write and reads, and the barriers the arrivals and polls name. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The field `ExitFacts.mma_exit`.** -/
theorem ExitFacts_mma_exit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc : Nat} (_ : g < L.threads) (hw : warpOf L g = 12)
    (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    ∃ a w, a < w ∧ w < k ∧
      (∃ pca tx cnt rel sc, X.get (g, a) =
        some ⟨pca, .arrive (FBar.loc L (pairCta (ctaOf L g)) .dealloc) tx cnt rel sc⟩) ∧
      ∃ pcw acq sc, X.get (g, w) =
        some ⟨pcw, .wait (FBar.loc L (ctaOf L g) .dealloc) 0 true acq sc⟩ := by
  obtain ⟨d, t, ins, o, -, hJ, -, -, -, -, hc, hf⟩ :=
    mma_state hpre hX ht he hw (by simp [Prologue.ProKind]) (fun f h => by cases h)
  have h1 := hJ.dealloc
  rw [Mma.exit_site hc hf rfl] at h1
  obtain ⟨w, pcw, p, acq, sc, hwk, hgw⟩ := exists_okPoll (X := X) (by rw [h1]; decide)
  obtain ⟨d', hJ', hs', -, rfl, -, -⟩ := mma_hs_wait hpre hX ht hw hgw
  have h2 := hJ'.handoff
  rw [hs'] at h2
  unfold arrivals at h2
  obtain ⟨a, e, ha, hea, hp, -⟩ := exists_nthEv (X := X)
    (p := arrivesOn (FBar.loc L (Mma.peer L g) .dealloc)) (g := g) (k := w) (n := 0)
    (by rw [h2]; decide)
  unfold arrivesOn sourceArrive at hp
  split at hp
  · rename_i m tx c rel sc' hk
    simp only [decide_eq_true_eq] at hp
    subst hp
    refine ⟨a, w, ha, hwk, ⟨e.pc, tx, c, rel, sc', ?_⟩, pcw, acq, sc, hgw⟩
    rw [hea, ← peer_eq hpre, ← hk]
  · cases hp

/-- Items of the cluster below the done ones are done: work items grow with the item. -/
theorem item_lt {g i j : Nat} (h : workOf L g i < totOf L) (hd : totOf L ≤ Mma.work L g j) :
    i < j := by
  have h' : clusterOf L g + i * clusterCount L < clusterOf L g + j * clusterCount L := by
    have := h
    unfold workOf at this
    unfold Mma.work at hd
    exact Nat.lt_of_lt_of_le this hd
  exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_add_lt_add_left h')

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

/-- **The field `ExitFacts.mma_full`.** -/
theorem ExitFacts_mma_full (ht : Frame.Tracked (code L) X) {g a pc tx cnt u : Nat} {rel : Bool}
    {sc : MbarScope} {b : FBar} (_ : g < L.threads) (hw : warpOf L g = 12) (hev : ctaOf L g % 2 = 0)
    (he : X.get (g, a) =
      some ⟨pc, .arrive (FBar.loc L (pairCta (ctaOf L g)) .dealloc) tx cnt rel sc⟩) (hb : b.isFull)
    (hu : workOf L g (useItem P b u) < totOf L) :
    u < okPolls (b.loc L (ctaOf L g)) ((X.tr g).take a) := by
  obtain ⟨d, hJ, hs, -⟩ := mma_arrive hpre hX ht hw he
  have hlt := item_lt hu (hJ.done (by rw [hs]; rfl) (by simpa [Mma.rank, ctaOf] using hev))
  cases b with
  | qFull st =>
    have h := hJ.qFull st
    change u < okPolls (Mma.bar L g (.qFull st)) _
    rw [h]
    obtain ⟨site, i, tt, base, pro⟩ := d
    simp only at hs hlt
    subst hs
    simpa [Mma.cnt, Mma.qA, Mma.Site.after, Mma.Site.ord, useItem] using hlt
  | kvFull s =>
    have h := hJ.kvFull s
    change u < okPolls (Mma.bar L g (.kvFull s)) _
    rw [h]
    obtain ⟨site, i, tt, base, pro⟩ := d
    simp only at hs hlt
    subst hs
    simp only [useItem, ← trips_eq hpre] at hlt
    have hs6 := s.isLt
    have hm : 6 * u + s.val < 2 * Mma.trips L * i := by
      have := (Nat.div_lt_iff_lt_mul (by have := mma_trips_pos hpre; omega)).mp hlt
      rw [Nat.mul_comm i] at this
      exact this
    simp only [Mma.cnt, Mma.kvA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop, Mma.Site.ord,
      Mma.slots]
    simp
    omega
  | _ => simp [FBar.isFull] at hb

/-! ### The cross-warp premises of the MMA role -/

/-- **`Cross.MmaExitBar2`**: a lane of warp 12 exits after its two `bar.sync 2`. -/
theorem Cross.MmaExitBar2_mma (ht : Frame.Tracked (code L) X) :
    ∀ {g k pc : Nat}, g < L.threads → warpOf L g = 12 → X.get (g, k) = some ⟨pc, .exit⟩ →
      2 ≤ barOrd X g k 2 := by
  intro g k pc _ hw he
  obtain ⟨d, t, ins, o, -, hJ, -, -, -, -, hc, hf⟩ :=
    mma_state hpre hX ht he hw (by simp [Prologue.ProKind]) (fun f h => by cases h)
  have h := hJ.bar2
  rw [Mma.exit_site hc hf rfl] at h
  show 2 ≤ ((X.tr g).take k).countP (Execution.isBarId 2)
  rw [h]
  decide

/-- **`Cross.MmaBaseWrite`**: a write of warp 12 is lane 0's address store, the event after its
allocation, before barrier 2. -/
theorem Cross.MmaBaseWrite_mma (ht : Frame.Tracked (code L) X) :
    ∀ {g k : Nat} {a : Acc} {bs : List Byte} {l : Loc}, warpOf L g = 12 →
      X.Writes (g, k) a bs → a.Covers l → L.sharedBase + 328 ≤ l.addr →
      l.addr < L.sharedBase + 332 →
        g % L.block = 384 ∧ a.loc = baseLoc L (ctaOf L g) ∧ a.size = 4 ∧ bs.length = 4 ∧
          barOrd X g k 2 = 0 ∧
          ∃ j pc grp dst n, k = j + 1 ∧
            X.get (g, j) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ := by
  intro g k a bs l hw ⟨pc, he⟩ _ _ _
  obtain ⟨d, t, ins, u, -, hJ, -, -, hs, h, hc, hf⟩ :=
    mma_state_cont hpre hX ht he hw (by simp [Prologue.ProKind])
      (by rintro (⟨f, h⟩ | h) <;> cases h)
  have hd := Mma.write_site hpre hs h hc hf rfl
  obtain ⟨a', bs', hk, hloc, hsz, hlen⟩ :=
    Mma.allocWrite_site hpre hd (by rw [hs, hd]; rfl) h hc hf
  simp only [Kind.wr.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  obtain ⟨hl0, x, hlast, hkx⟩ := hJ.allocWrite hd
  have hb := hJ.bar2
  rw [hd] at hb
  have hlen' : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    cases k with
    | zero => simp at hlast
    | succ j => exact ⟨j, rfl⟩
  refine ⟨by simp only [warpOf, laneOf] at hw hl0; omega, hloc, hsz, hlen, hb, j, x.pc, .two,
    some (Mma.baseAt L g), 512, rfl, ?_⟩
  rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left (by omega),
    Nat.add_sub_cancel, List.getElem?_take_of_lt (by omega)] at hlast
  show (X.tr g)[j]? = _
  rw [hlast, ← hkx]

/-- **`Cross.MmaBaseRead`**: a read of warp 12 follows its first `bar.sync 2`. -/
theorem Cross.MmaBaseRead_mma (ht : Frame.Tracked (code L) X) :
    ∀ {g k : Nat} {a : Acc} {bs : List (Option Byte)} {l : Loc}, warpOf L g = 12 →
      X.Reads (g, k) a bs → a.Covers l → L.sharedBase + 328 ≤ l.addr →
      l.addr < L.sharedBase + 332 → ∃ b < k, Bar2Sync X g b 0 := by
  intro g k a bs l hw ⟨pc, he⟩ _ _ _
  obtain ⟨d, t, ins, u, -, hJ, -, -, hs, h, hc, hf⟩ :=
    mma_state_cont hpre hX ht he hw (by simp [Prologue.ProKind])
      (by rintro (⟨f, h⟩ | h) <;> cases h)
  refine bar2_nth hJ ?_
  have hb := (Mma.bar2_site hpre hc hf).1
  obtain ⟨site, i, tt, base, pro⟩ := d
  cases site
  case setMaxReg =>
    code_at hc
    subst hc
    simp only [eventTmpl, SetMaxNReg.tmpl] at hf
    split_ifs at hf <;> simp [Fires] at hf
  case alloc =>
    have := Mma.alloc_site hpre rfl hs h hc hf
    cases this
  case allocWrite =>
    obtain ⟨_, _, hk, -⟩ := Mma.allocWrite_site hpre rfl hs h hc hf
    cases hk
  case bar0 => simp [Execution.isBarId, Mma.bar2Ev] at hb
  all_goals simp [Mma.bar2A]

/-- **`Cross.PeerBar2High`, for warp 12**: its commits and its arrivals on another CTA other
than the hand-off come before its second `bar.sync 2` (an arrival of warp 12 is the
hand-off). -/
theorem Cross.PeerBar2High_mma (ht : Frame.Tracked (code L) X) :
    ∀ {g k : Nat} {ev : Event}, g < L.threads → warpOf L g = 12 → X.get (g, k) = some ev →
      PeerEvent L g ev → warpOf L g = 12 ∧ barOrd X g k 2 ≤ 1 := by
  intro g k ev _ hw he hp
  rcases hp with ⟨m, tx, cnt, rel, sc, hk, -, hne⟩ | ⟨sp, hk⟩
  · obtain ⟨d, -, -, hm, -⟩ := mma_arrive hpre hX ht hw (get_kind he hk)
    subst hm
    exact absurd rfl hne
  · obtain ⟨-, d, c, hJ, -, hs, -⟩ := commit_state hpre hX ht (get_kind he hk)
    have h := hJ.bar2
    rw [hs] at h
    refine ⟨hw, ?_⟩
    show ((X.tr g).take k).countP (Execution.isBarId 2) ≤ 1
    rw [h]
    simp [Mma.bar2A]

/-- **`Cross.SyncNamed`, for warp 12**: its arrival and polls name table barriers, not spare,
of its pair. -/
theorem Cross.SyncNamed_mma (ht : Frame.Tracked (code L) X) :
    ∀ {g k pc : Nat} {m : Loc} {kd : Kind}, g < L.threads → warpOf L g = 12 →
      X.get (g, k) = some ⟨pc, kd⟩ →
      ((∃ tx c rel sc, kd = .arrive m tx c rel sc) ∨
        (∃ p ok acq sc, kd = .wait m p ok acq sc)) →
      ∃ (b : FBar) (c : Nat), m = b.loc L c ∧ c / 2 = ctaOf L g / 2 ∧
        ∀ i st, b ≠ .spare i st := by
  intro g k pc m kd _ hw he hk
  rcases hk with ⟨tx, c, rel, sc, rfl⟩ | ⟨p, ok, acq, sc, rfl⟩
  · obtain ⟨d, -, -, hm, -⟩ := mma_arrive hpre hX ht hw he
    refine ⟨.dealloc, _, hm, ?_, fun _ _ => nofun⟩
    rw [peer_eq hpre, pairCta]
    omega
  · obtain ⟨d, B, t, ins, -, -, hB, hm, -⟩ := mma_wait hpre hX ht hw he
    refine ⟨B, _, hm, rfl, fun i st h => ?_⟩
    subst h
    obtain ⟨site, i, tt, base, pro⟩ := d
    cases site <;> simp [Mma.pollBar] at hB

omit hpre hX in
/-- Only the read-back is a load. -/
theorem Mma.read_ops : Mma.OpsOff (fun s => decide (s = .ldBase)) readOp := by
  unfold Mma.OpsOff
  decide +kernel

/-- **A memory access of warp 12** is lane 0's address store or the read-back: of the four
bytes of the base word of its CTA. -/
theorem mma_access (ht : Frame.Tracked (code L) X) {g k : Nat} {a : Acc} {w : Bool}
    (hw : warpOf L g = 12) (hA : X.Access (g, k) a w) : a.loc = Mma.baseAt L g ∧ a.size = 4 := by
  rcases Cross.access_rw hX hA with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩
  · obtain ⟨d, t, ins, u, -, -, -, -, hs, h, hc, hf⟩ :=
      mma_state_cont hpre hX ht he hw (by simp [Prologue.ProKind])
        (by rintro (⟨f, h⟩ | h) <;> cases h)
    have hop := fires_read_op hf rfl
    cases hd : decide (d.site = .ldBase)
    · rw [Mma.read_ops.op hd hc] at hop
      cases hop
    · have hd' : d.site = .ldBase := by simpa using hd
      obtain ⟨a', bs', hk, hloc, hsz⟩ := Mma.ldBase_site hpre hd' (by rw [hs, hd']; rfl) h hc hf
      simp only [Kind.rd.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact ⟨hloc, hsz⟩
  · obtain ⟨d, t, ins, u, -, -, -, -, hs, h, hc, hf⟩ :=
      mma_state_cont hpre hX ht he hw (by simp [Prologue.ProKind])
        (by rintro (⟨f, h⟩ | h) <;> cases h)
    have hd := Mma.write_site hpre hs h hc hf rfl
    obtain ⟨a', bs', hk, hloc, hsz, -⟩ := Mma.allocWrite_site hpre hd (by rw [hs, hd]; rfl) h hc hf
    simp only [Kind.wr.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    exact ⟨hloc, hsz⟩

/-- **`Cross.LowAccessLow`, for warp 12**: its accesses are of the base word. -/
theorem Cross.LowAccessLow_mma (ht : Frame.Tracked (code L) X) :
    ∀ {g k : Nat} {a : Acc} {w : Bool} {l : Loc}, warpOf L g = 12 → X.Access (g, k) a w →
      a.Covers l → l.addr < L.sharedBase + 68608 := by
  intro g k a w l hw hA hc
  obtain ⟨hloc, hsz⟩ := mma_access hpre hX ht hw hA
  obtain ⟨-, -, -, h⟩ := hc
  rw [hloc, hsz] at h
  simp only [Mma.baseAt] at h
  omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof
