-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Index
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Objs
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.RefLoop
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.LastTime

@[expose] public section

/-! # The index warp's time facts

**The role's lemma table** (channel: producer early / waiter / producer exit). Common
hypotheses: `hp : Pre P L m`, `hX : Consistent L kernel Assumptions.all m X`, `hFw : Follow P L X`;
a producer lane `g` additionally `hw : MbarRow.warp L g = 7`, `hc : g / L.block = c`, and for the
early fact `hub : ¬ HasUb X`, `hg : g < L.threads`; an exit fact `hx : X.get (g, k) = some ⟨pc,
.exit⟩`. A waiter is given by `hn : Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait
(mbarLoc L c F) p ok acq sc⟩`. `R = blocksOf P L c`; `A`, `u` the lane's arrivals on, successful
polls of, the slot's object (`arrivals`, `okPolls` over `X.tr g`); `t` is
`Sched.threadTime (timed P L) X g`; the slots are those of `Lib/Slots.lean`.

* `valid_coord_free[j]` (waits 2446, 2534): waiter `ix_cfWait` (`hpc : pc = 2446 ∨ pc = 2534`,
  no other hypothesis): `warp L g = 7 ∧ g / L.block = c ∧ u < ringUses 4 j R ∧
  cfWait (4u + j) ≤ t` (block `4u + j` waits for block `4u + j - 4`'s frees); producers wg0 and
  the TMA lane.
* `valid_coord_ready[j]` (arrivals 2476, 2565): early `ix_crEarly`
  (`A < ringUses 4 j R → t ≤ crArr (4A + j)`), exit `ix_crExit` (`ringUses 4 j R ≤ A`);
  waiters wg0 and the TMA lane (`tma_crWait`).
* named barrier 12 (pc 2585): `ix_barSlot` (`hp`, `hFw`; `hn : NextEv … g e`, `e.pc = 2585`, `e`
  not a fault):
  `warp L g = 7 ∧ t = endSlot`.

The state does not hold its block: it is the block of the counts (`Index.blockOf`, the arrivals on
`valid_coord_ready`), the reference invariant's block `i` (`Index.RingCounts`), whose loops'
counters (`Index.Ctr`) put a wait or an arrival below the CTA's block count and the barrier and the
exit at it (`Index.ctr_blk_lt`; the lane's length words are the launch's, `ix_rounds`). The
producers' facts come from one view of the lane's last state (`ix_end`): a startup, head or
set-up state (time at most `142`), a block-`b` state at `frame b + x` (`x ≤ 12`) with `b`
arrivals' worth of counts, or the barrier or exit with every block's (`ix_step`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- No undefined behaviour in the glued ledger: none in the role's. -/
private theorem ub_idx {k : Nat} (h : ((X.tr g).take k).countP (cls .ub) = 0) :
    ((X.tr g).take k).countP (Index.cls .ub) = 0 :=
  List.countP_eq_zero.mpr fun f hf hc => List.countP_eq_zero.mp h f hf (by
    obtain ⟨pc, kd⟩ := f
    cases kd with
    | wait l q ok a sc => cases ok <;> simp_all [Index.cls, Index.kindOf, cls]
    | _ => simp_all [Index.cls, Index.kindOf, cls])

/-- No undefined behaviour in any prefix. -/
private theorem ub_none (hub : ¬ HasUb X) (i : Nat) : ((X.tr g).take i).countP (cls .ub) = 0 :=
  List.countP_eq_zero.mpr fun f hf hcl => hub (by
    obtain ⟨j, -, hj⟩ := get_lt_of_mem_take hf
    obtain ⟨pc, kd⟩ := f
    cases kd <;> simp [cls] at hcl
    exact ⟨(g, j), pc, _, hj⟩)

/-- A state's counts on the role's classes at prefix `i`. -/
private def ixc (X : Execution) (g i : Nat) : Index.Cnt → Nat :=
  fun c => ((X.tr g).take i).countP (Index.cls c)

/-- The arrivals on `valid_coord_ready` after `b` blocks. -/
private abbrev Arr (L : Launch) (g : Nat) (n : Index.Cnt → Nat) (b : Nat) : Prop :=
  ∀ s : Fin 4, n (.arrive (loc L g (.coordReady s))) = ringUses 4 s.val b

/-- **The index lane at its wait on `coordFree j`** (pcs 2446, 2534): it is a lane of warp 7 of
CTA `c`, and is no earlier than `cfWait` of the block of its use. -/
theorem ix_cfWait (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {c p pc : Nat} {j : Fin 4} {ok acq : Bool} {sc : MbarScope}
    (hpc : pc = 2446 ∨ pc = 2534)
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨pc, .wait (mbarLoc L c (.coordFree j)) p ok acq sc⟩) :
    warp L g = 7 ∧ g / L.block = c ∧
    okPolls (mbarLoc L c (.coordFree j)) (X.tr g) < ringUses 4 j.val (blocksOf P L c) ∧
    cfWait (4 * okPolls (mbarLoc L c (.coordFree j)) (X.tr g) + j.val) ≤
      Sched.threadTime (timed P L) X g := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := next_state hp hFw hn (fun _ h => by cases h)
  obtain ⟨d, n, rfl, hR, hE, hw⟩ := index_state hJ hi hev hpcσ
    ⟨by simp only; omega, by simp only; omega⟩
  have hu : ((X.tr g).take (X.tr g).length).countP (cls .ub) = 0 :=
    (state_count hσ .ub).symm.trans (next_ub hn hσ)
  have hu' : n (.index .ub) = 0 := (state_count hσ (.index .ub)).trans (ub_idx hu)
  obtain ⟨i, -, hslot, -, hrc, hct, -⟩ := hR (next_ub hn hσ) hu'
  have h1 : pc = d.site.pc := hE.1
  have hs : d.site = .wA ∨ d.site = .wB := by
    cases hsd : d.site <;> rw [hsd] at h1 <;> simp only [IxSite.pc] at h1 <;>
      first | omega | simp
  have hK : Index.PollEv L g (Index.freeW L d.c) (ixParW d.c.par)
      ⟨pc, .wait (mbarLoc L c (.coordFree j)) p ok acq sc⟩ := by
    obtain ⟨-, hK⟩ := hE
    rcases hs with h | h <;> simpa only [Index.EvK, h] using hK
  rcases hK with ⟨ok', hk⟩ | ⟨f, hk⟩
  · simp only [Kind.wait.injEq] at hk
    obtain ⟨hl', -⟩ := hk
    have hloc := hl'.trans (Index.free_loc hp d.c)
    simp only [loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff, true_and] at hloc
    obtain ⟨rfl, hf⟩ := hloc
    cases MbarFam.off_inj hf
    have hw0 : Index.incW d.site = 0 := by rcases hs with h | h <;> rw [h] <;> rfl
    rw [hw0] at hrc
    have hP := ix_okPolls hp hX hFw hw (X.tr g).length (loc L g (.coordFree d.c.slot))
    have hc := state_count hσ (.index (.acq (loc L g (.coordFree d.c.slot))))
    simp only at hc
    replace hP := hP.trans hc.symm
    have hr1 := (hrc d.c.slot).1
    simp only at hr1
    rw [hr1, hslot, Nat.add_zero, Index.ring_here, List.take_length] at hP
    simp only [loc] at hP
    have hlt := Index.ctr_blk_lt hct (by rcases hs with h | h <;> rw [h] <;> simp)
    rw [ix_rounds hp hX hσ (by rcases hs with h | h <;> rw [h] <;> simp)
      (by rcases hs with h | h <;> rw [h] <;> simp)] at hlt
    refine ⟨hw, rfl, ?_, ?_⟩
    · rw [hslot, hP]
      simp only [slot4, ringUses]
      omega
    rw [hslot, hP, timed_eq, Sched.threadTime_of hσ]
    have hb := Index.blockOf_eq (L := L) (g := g) hrc
    have hpl : Index.place L g d (fun c => n (.index c)) ≥ ixBlk0 + stride * i + ixWait := by
      rcases hs with h | h <;>
        simp only [Index.place, Index.placeAt, h, Index.ord, hb, ixWait] <;> omega
    simp only [time, fragTime, wg1Time, indexTime, Index.time, slot4, cfWait, frame,
      loopBase, stride, ixOff, ixWait, ixBlk0, ixOrg, idleBase, roleBase] at hpl ⊢
    omega
  · cases hk

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hw : warp L g = 7)
include hp hX hFw hw

/-- **The time of a state of the lane**, plus `δ` when the machine moves on from it. -/
private theorem ix_step (hub : ¬ HasUb X) (hg : g < L.threads) {Q : Nat → Prop}
    (hpro : ∀ t, t ≤ 142 → Q t)
    (hloop : ∀ i b x, i ≤ (X.tr g).length → b < blocksOf P L (g / L.block) → x ≤ 12 →
      Arr L g (ixc X g i) b → Q (frame b + x))
    (hend : ∀ i, i ≤ (X.tr g).length → Arr L g (ixc X g i) (blocksOf P L (g / L.block)) → False)
    {i δ : Nat} {σ : (thread P L g).D} (hi : i ≤ (X.tr g).length) (hδ : δ ≤ 1)
    (hσ : Frame.stateAt (thread P L) X g i = some (some σ))
    (hmv : δ = 1 → ∀ d n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n) →
      d.site ≠ .arrA ∧ d.site ≠ .arrB) :
    Q (time P L g σ + δ) := by
  rcases ix_state hp hX hFw hw hg hσ with ht | ⟨d, n, rfl, hR, hel⟩
  · exact hpro _ (by omega)
  have hc : (fun c => n (.index c)) = ixc X g i := funext fun c => state_count hσ (.index c)
  rw [hc] at hR
  obtain ⟨b, hpre, -, -, hrc, hct, -⟩ :=
    hR ((state_count hσ .ub).trans (ub_none hub i)) (ub_idx (ub_none hub i))
  have harr : Arr L g (ixc X g i) b := fun s => (hrc s).2
  have hb : Index.blockOf L g (ixc X g i) = b := by
    unfold Index.blockOf
    rw [harr 0, harr 1, harr 2, harr 3]
    exact Index.ring_sum b
  have ht : time P L g (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n) =
      idleBase + Index.placeAt b d.site d.el := by
    show idleBase + Index.placeAt (Index.blockOf L g (fun c => n (.index c))) d.site d.el = _
    rw [hc, hb]
  have hmv' := fun h => hmv h d n rfl
  rw [ht]
  have hR' := ix_rounds hp hX hσ
  obtain ⟨site, el, ac, c⟩ := d
  simp only at hel hpre hct hmv' hR' ⊢
  have hbase : idleBase = 103 := rfl
  by_cases hs : site = .lenA ∨ site = .lenB ∨ site = .pre ∨ site = .bar ∨ site = .exit
  · rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact hpro _ (by simp only [Index.placeAt]; omega)
    · exact hpro _ (by simp only [Index.placeAt]; omega)
    · obtain rfl := hpre rfl
      exact hpro _ (by simp only [Index.placeAt, Index.ord, ixBlk0, loopBase, ixOff, ixOrg,
        roleBase, idleBase] at *; omega)
    · exact (hend i hi (by rw [← hR' (by simp) (by simp), ← (hct : b = _)]; exact harr)).elim
    · exact (hend i hi (by rw [← hR' (by simp) (by simp), ← (hct : b = _)]; exact harr)).elim
  have hA : site ≠ .lenA := fun h => hs (.inl h)
  have hB : site ≠ .lenB := fun h => hs (.inr (.inl h))
  have hlt : b < blocksOf P L (g / L.block) := by
    rw [← hR' hA hB]
    by_cases hx : site = .xpre
    · subst hx
      obtain ⟨h1, h2, -⟩ := hct
      omega
    · exact Index.ctr_blk_lt hct ⟨hA, hB, fun h => hs (.inr (.inr (.inl h))), hx,
        fun h => hs (.inr (.inr (.inr (.inl h)))), fun h => hs (.inr (.inr (.inr (.inr h))))⟩
  have hpl : Index.placeAt b site el = ixBlk0 + stride * b + Index.ord site + min el 1 := by
    cases site <;> first | rfl | exact absurd (by simp) hs
  have hx : Index.ord site + min el 1 + δ ≤ 12 := by
    by_cases ha : site = .arrA ∨ site = .arrB
    · have h0 : δ = 0 := by
        by_contra h1
        obtain ⟨h2, h3⟩ := hmv' (by omega)
        rcases ha with ha | ha <;> contradiction
      rcases ha with rfl | rfl <;> simp only [IxSite.elems] at hel <;>
        simp only [Index.ord] <;> omega
    · cases site <;> simp only [IxSite.elems] at hel <;> simp only [Index.ord] <;>
        first | omega | exact absurd (.inl rfl) ha | exact absurd (.inr rfl) ha
  rw [hpl]
  have := hloop i b _ hi hlt hx harr
  rw [show idleBase + (ixBlk0 + stride * b + Index.ord site + min el 1) + δ =
    frame b + (Index.ord site + min el 1 + δ) by
      simp only [ixBlk0, frame, loopBase, ixOff, ixOrg, idleBase, roleBase]; omega]
  exact this

/-- **The lane's last state**: the principle behind the producers' facts. -/
private theorem ix_end (hub : ¬ HasUb X) (hg : g < L.threads) {Q : Nat → Prop}
    (hpro : ∀ t, t ≤ 142 → Q t)
    (hloop : ∀ i b x, i ≤ (X.tr g).length → b < blocksOf P L (g / L.block) → x ≤ 12 →
      Arr L g (ixc X g i) b → Q (frame b + x))
    (hend : ∀ i, i ≤ (X.tr g).length → Arr L g (ixc X g i) (blocksOf P L (g / L.block)) → False) :
    Q (Sched.threadTime (timed P L) X g) := by
  refine time_last (hpro 0 (by omega)) (fun σ hs => ?_) (fun σ f hs hf hn => ?_)
  · simpa using ix_step hp hX hFw hw hub hg hpro hloop hend (Nat.le_refl _) (Nat.zero_le 1) hs
      (by omega)
  · refine ix_step hp hX hFw hw hub hg hpro hloop hend (by omega) (Nat.le_refl 1) hs
      fun _ d n hd => ?_
    rw [hd] at hn
    exact ⟨fun h => ix_arr_next (.inl h) hn, fun h => ix_arr_next (.inr h) hn⟩

/-- The arrivals of the lane at prefix `i`: below the trace's, and the role's count. -/
private theorem ix_arr_at (i : Nat) (f : MbarFam) :
    arrivals (loc L g f) ((X.tr g).take i) ≤ arrivals (loc L g f) (X.tr g) ∧
    arrivals (loc L g f) ((X.tr g).take i) = ixc X g i (.arrive (loc L g f)) :=
  ⟨(List.take_sublist i _).countP_le, ix_arrivals hp hX hFw hw i _⟩

/-- **An index lane short of its uses of `valid_coord_ready j` is no later than the arrival slot
of its next use.** -/
theorem ix_crEarly (hub : ¬ HasUb X) (hg : g < L.threads) {c : Nat} {s : Fin 4}
    (hc : g / L.block = c)
    (hlt : arrivals (mbarLoc L c (.coordReady s)) (X.tr g) < ringUses 4 s.val (blocksOf P L c)) :
    Sched.threadTime (timed P L) X g ≤
      crArr (4 * arrivals (mbarLoc L c (.coordReady s)) (X.tr g) + s.val) := by
  subst hc
  have hs := s.isLt
  refine ix_end hp hX hFw hw hub hg (Q := fun t => t ≤ crArr (4 * arrivals
    (mbarLoc L (g / L.block) (.coordReady s)) (X.tr g) + s.val)) (fun t ht => ?_)
    (fun i b x hi _ hx harr => ?_) (fun i hi harr => ?_)
  · simp only [crArr, frame, loopBase, stride, ixOff, ixArr]
    omega
  · obtain ⟨hle, heq⟩ := ix_arr_at hp hX hFw hw i (.coordReady s)
    rw [heq, harr s] at hle
    simp only [loc] at hle
    simp only [ringUses, crArr, frame, loopBase, stride, ixOff, ixArr] at hle ⊢
    omega
  · obtain ⟨hle, heq⟩ := ix_arr_at hp hX hFw hw i (.coordReady s)
    rw [heq, harr s] at hle
    simp only [loc] at hle
    omega

/-- **An index lane that exited has made all its uses of `valid_coord_ready j`.** -/
theorem ix_crExit {c k pc : Nat} {s : Fin 4} (hc : g / L.block = c)
    (hx : X.get (g, k) = some ⟨pc, .exit⟩) :
    ringUses 4 s.val (blocksOf P L c) ≤ arrivals (mbarLoc L c (.coordReady s)) (X.tr g) := by
  subst hc
  obtain ⟨d, hR, hs, hr⟩ := ix_exit_at hp hX hFw hw hx
  obtain ⟨i, -, -, -, hrc, hct, -⟩ := hR (ix_take_noUb hX hx)
  rw [hs] at hrc hct
  have hct' : i = roundsOf d.c.l0 d.c.l1 := hct
  obtain ⟨hle, heq⟩ := ix_arr_at hp hX hFw hw k (.coordReady s)
  have h3 : ixc X g k (.arrive (loc L g (.coordReady s))) = ringUses 4 s.val i := (hrc s).2
  rw [heq, h3, hct', hr] at hle
  simpa only [loc] using hle

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
