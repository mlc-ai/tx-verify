-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Lemmas.Kernel.Progress.NextEv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Dequant
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Wait
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.SitePc

@[expose] public section

/-! # Warpgroup 2's time facts

**The role's lemma table** (channel: producer early / waiter / producer exit). Common
hypotheses: `hp : Pre P L m`, `hX : Consistent L kernel Assumptions.all m X`, `hFw : Follow P L X`;
a producer lane `g` additionally `hub : ¬ HasUb X` (early only),
`hw : 8 ≤ MbarRow.warp L g ∧ MbarRow.warp L g < 12`, `hg : g < L.threads` (early only) and
`hc : g / L.block = c`; an exit fact `hx : X.get (g, k) = some ⟨pc, .exit⟩`. A waiter is given by
`hn : Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait (mbarLoc L c F) p ok acq sc⟩`.
`R = blocksOf P L c`; `A`, `u` the lane's arrivals on, successful polls of, the slot's object.

* `qUtccp` (wait 2644): waiter `dequant_slot_wait` (`t = qUtccpSlot`); producer MMA.
* `rawReady j` (wait 2677): waiter `deq_rrWait` (`u < ringUses 2 j R`, `rrWait (2u+j) ≤ t`);
  producer TMA (lane Eb).
* `svDone j` (wait 2684): waiter `deq_svWait` (`u < ringUses 2 j R`, `svWaitD (2u+j) ≤ t`);
  producer MMA (`mma_svEarly`, `mma_svExit`).
* `dequantReady j` (arrival 3597): early `deq_drEarly` (`A < ringUses 2 j R → t ≤ drArr (2A+j)`),
  exit `deq_drExit` (`ringUses 2 j R ≤ A`); waiter MMA (`mma_drWait`).
* `rawFree j` (arrival 3599): early `deq_rfEarly` (`A < ringUses 2 j R → t ≤ rfArr (2A+j)`),
  exit `deq_rfExit` (`ringUses 2 j R ≤ A`); waiter TMA (lane Eb).

The waiters' conclusions also give `g / L.block = c` and the lane's warp in 8–11; the waits at 2677
and 2684 are in `Dequant/Export/Wait.lean` (imported here). `t` is
`Sched.threadTime (timed P L) X g`; the slots are those of `Lib/Slots.lean`.

A dequant lane whose next event is its wait on `bar_q_utccp` (pc 2644) is at the slot of the MMA
lane's commit (`dequant_slot_wait`; the input `QueryTime.deqSlot` of `Protocol/Query/Lag.lean`):
its state is warpgroup 2's Q poll (`dequant_state`), at place 3 of the role, glued at
`idleBase + 29 + 3 = qUtccpSlot` (`Common/Time.lean`).

The producers' facts come from one view of the lane's last state (`deq_end`): a startup or set-up
state (time at most `136`), a block-`r` state at `frame r + deqOff + x` with its slot counts
(`Dequant/Ref.lean`), or the closing barrier or exit with every use made (`deq_view`,
`deq_exit_at`); per ring (`arr_early`, `arr_exit`) the arrival count of the slot counts. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem wq_of_pc {s : Dequant.Site} (h : s.pc = 2644) : s = .wq := by
  rcases Dequant.small_site (s := s) (by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Dequant.Site.pc] at h ⊢

/-- **A dequant lane at its wait on `bar_q_utccp` is at the slot.** -/
theorem dequant_slot_wait (hp : Pre P L m) (hFw : Follow P L X) {g c p : Nat} {ok acq : Bool}
    {sc : MbarScope} (_hd : MbarRow.DequantAt L g 2644)
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨2644, .wait (mbarLoc L c .qUtccp) p ok acq sc⟩) :
    Sched.threadTime (timed P L) X g = qUtccpSlot := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := next_state hp hFw hn (fun _ h => by cases h)
  obtain ⟨d, n, rfl, -, hE, -⟩ :=
    dequant_state hp hJ hi hev hpc ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hs : d.site = .wq := wq_of_pc hE.1.symm
  rw [timed_eq, Sched.threadTime_of hσ]
  simp [time, fragTime, dequantTime, Dequant.time, Dequant.place, hs, idleBase, roleBase,
    qUtccpSlot]

/-! ### The view of a lane's last state -/

section
variable {g : Nat}

/-- A state's counts on the role's classes at prefix `i`. -/
private def pc' (X : Execution) (g i : Nat) : Dequant.Cnt → Nat :=
  fun c => ((X.tr g).take i).countP (Dequant.cls c)

/-- The slot counts at every use among `R` blocks. -/
private abbrev Full (L : Launch) (g : Nat) (n : Dequant.Cnt → Nat) (R : Nat) : Prop :=
  ∀ b, Dequant.SlotCounts L g n b (Dequant.uses b R) (Dequant.uses b R) (Dequant.uses b R)
    (Dequant.uses b R)

/-- **A state with the reference invariant**: a set-up state (place at most 3), a block-`r`
state with its slot counts, or the closing barrier or exit with every use made. -/
private theorem deq_view {d : Dequant.Control.D} {n : Dequant.Cnt → Nat} (hR : Dequant.Ref L g d n)
    (h0 : n .ub = 0) :
    Dequant.place d ≤ 3 ∨
    (∃ r, d.site.inLoop = true ∧ Dequant.LoopWords d r ∧
      ∀ b, Dequant.SlotCounts L g n b (Dequant.uses b (r + Dequant.incR d.site))
        (Dequant.uses b (r + Dequant.incS d.site)) (Dequant.uses b (r + Dequant.incD d.site))
        (Dequant.uses b (r + Dequant.incF d.site))) ∨
    ((d.site = .bar ∨ d.site = .exit) ∧ Full L g n (Dequant.rounds d.l0 d.l1)) := by
  have hJ := hR h0
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases site with
  | smr | lenA | lenB | wq => left; simp [Dequant.place]
  | bar => exact .inr (.inr ⟨.inl rfl, hJ⟩)
  | exit => exact .inr (.inr ⟨.inr rfl, hJ⟩)
  | _ =>
    obtain ⟨r, hw, -, -, hc⟩ := hJ
    exact .inr (.inl ⟨r, rfl, hw, hc⟩)

/-- No undefined behaviour in any prefix. -/
private theorem noUb {c : Event → Bool} (hc : ∀ f, c f = true → ∃ fl, f.kind = .ub fl)
    (hub : ¬ HasUb X) (i : Nat) : ((X.tr g).take i).countP c = 0 :=
  List.countP_eq_zero.mpr fun f hf hcl => hub (by
    obtain ⟨j, -, hj⟩ := get_lt_of_mem_take hf
    obtain ⟨fl, hk⟩ := hc f hcl
    obtain ⟨pc, kd⟩ := f
    simp only at hk
    subst hk
    exact ⟨(g, j), pc, fl, hj⟩)

private theorem ubD (f : Event) (h : Dequant.cls .ub f = true) : ∃ fl, f.kind = .ub fl := by
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | ub fl => exact ⟨fl, rfl⟩
  | wait l q ok a sc => cases ok <;> simp [Dequant.cls, Dequant.kindOf] at h
  | _ => simp [Dequant.cls, Dequant.kindOf] at h

private theorem ubG (f : Event) (h : cls .ub f = true) : ∃ fl, f.kind = .ub fl := by
  obtain ⟨pc, kd⟩ := f
  cases kd <;> simp [cls] at h ⊢

variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hub : ¬ HasUb X) (hw : 8 ≤ MbarRow.warp L g ∧ MbarRow.warp L g < 12) (hg : g < L.threads)
include hp hX hFw hub hw hg

/-- **The time of a state of the lane**, plus `δ` when the machine moves on from it. -/
private theorem deq_step {Q : Nat → Prop} (hpro : ∀ t, t ≤ 136 → Q t)
    (hloop : ∀ i r x (s : Dequant.Site), i ≤ (X.tr g).length → r < blocksOf P L (g / L.block) →
      x ≤ 83 + Dequant.incD s → Dequant.incD s ≤ 1 → x ≤ 84 →
      (∀ b, Dequant.SlotCounts L g (pc' X g i) b (Dequant.uses b (r + Dequant.incR s))
        (Dequant.uses b (r + Dequant.incS s)) (Dequant.uses b (r + Dequant.incD s))
        (Dequant.uses b (r + Dequant.incF s))) → Q (frame r + deqOff + x))
    (hend : ∀ i, i ≤ (X.tr g).length → Full L g (pc' X g i) (blocksOf P L (g / L.block)) → False)
    {i δ : Nat} {σ : (thread P L g).D} (hi : i ≤ (X.tr g).length) (hδ : δ ≤ 1)
    (hσ : Frame.stateAt (thread P L) X g i = some (some σ))
    (hmv : δ = 1 → ∀ d n, σ = (.inr ⟨.inl .dequant, d⟩, n) → d.site ≠ .arrD ∧ d.site ≠ .arrF) :
    Q (time P L g σ + δ) := by
  rcases deq_state hFw hw hg hσ with ht | ⟨d, n, rfl, hR⟩
  · exact hpro _ (by omega)
  have hc : (fun c => n (.dequant c)) = pc' X g i := funext fun c => state_count hσ (.dequant c)
  rw [hc] at hR
  have ht : time P L g (.inr ⟨.inl .dequant, d⟩, n) = idleBase + 29 + Dequant.place d := rfl
  rw [ht]
  have h0 := noUb (g := g) ubD hub i
  have hR0 := hR ((state_count hσ .ub).trans (noUb (g := g) ubG hub i))
  rcases deq_view hR0 h0 with hpl | ⟨r, hl, hrw, hcnt⟩ | ⟨hbx, hF⟩
  · exact hpro _ (by simp only [idleBase, roleBase]; omega)
  · have hs : deqSetup d.site = false := by
      obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
      cases site <;> simp_all [Dequant.Site.inLoop, deqSetup]
    have hR' := deq_rounds hp hX hσ hs
    have hpl := Dequant.place_loop hl
    rw [Dequant.blk_eq hrw] at hpl
    have hrr := hrw.1
    rw [hR'] at hrr
    have hD : Dequant.incD d.site ≤ 1 := by unfold Dequant.incD; split <;> omega
    have hx : Dequant.place d + δ - deqBlk0 - stride * r ≤ 83 + Dequant.incD d.site ∧
        Dequant.place d + δ - deqBlk0 - stride * r ≤ 84 := by
      by_cases hA : d.site = .arrD ∨ d.site = .arrF
      · have h0 : δ = 0 := by
          by_contra h1
          obtain ⟨h2, h3⟩ := hmv (by omega) d n rfl
          rcases hA with hA | hA <;> contradiction
        rcases hA with hA | hA <;>
          simp only [hpl, hA, Dequant.elOff, Dequant.Site.idx, Dequant.incD, h0] <;> omega
      · have := Dequant.idx_el_le d (fun h => hA (.inl h)) (fun h => hA (.inr h))
        omega
    have heq : idleBase + 29 + Dequant.place d + δ =
        frame r + deqOff + (Dequant.place d + δ - deqBlk0 - stride * r) := by
      rw [hpl]
      simp only [frame, idleBase, roleBase, deqBlk0, loopBase, deqOff, deqOrg, stride]
      omega
    rw [heq]
    exact hloop i r _ d.site hi hrr hx.1 hD hx.2 hcnt
  · have hs : deqSetup d.site = false := by rcases hbx with h | h <;> rw [h] <;> rfl
    rw [deq_rounds hp hX hσ hs] at hF
    exact (hend i hi hF).elim

/-- **The lane's last state**: the principle behind the producers' facts. -/
private theorem deq_end {Q : Nat → Prop} (hpro : ∀ t, t ≤ 136 → Q t)
    (hloop : ∀ i r x (s : Dequant.Site), i ≤ (X.tr g).length → r < blocksOf P L (g / L.block) →
      x ≤ 83 + Dequant.incD s → Dequant.incD s ≤ 1 → x ≤ 84 →
      (∀ b, Dequant.SlotCounts L g (pc' X g i) b (Dequant.uses b (r + Dequant.incR s))
        (Dequant.uses b (r + Dequant.incS s)) (Dequant.uses b (r + Dequant.incD s))
        (Dequant.uses b (r + Dequant.incF s))) → Q (frame r + deqOff + x))
    (hend : ∀ i, i ≤ (X.tr g).length → Full L g (pc' X g i) (blocksOf P L (g / L.block)) → False) :
    Q (Sched.threadTime (timed P L) X g) := by
  have step := @deq_step _ _ _ _ _ hp hX hFw hub hw hg Q hpro hloop hend
  rw [timed_eq]
  unfold Sched.threadTime
  cases hs : Frame.stateAt (thread P L) X g (X.tr g).length with
  | some o =>
    cases o with
    | none => exact hpro 0 (by omega)
    | some σ => simpa using step (Nat.le_refl _) (Nat.zero_le 1) hs (by omega)
  | none =>
    simp only
    cases hs' : Frame.stateAt (thread P L) X g ((X.tr g).length - 1) with
    | none => exact hpro 0 (by omega)
    | some o =>
      cases o with
      | none => exact hpro 0 (by omega)
      | some σ =>
        refine step (by omega) (Nat.le_refl 1) hs' fun _ d n hd => ?_
        have hpos : 0 < (X.tr g).length := by
          rcases Nat.eq_zero_or_pos (X.tr g).length with h | h
          · rw [h, Frame.stateAt_zero] at hs; cases hs
          · exact h
        obtain ⟨f, hf⟩ : ∃ f, (X.tr g)[(X.tr g).length - 1]? = some f :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hn := Frame.stateAt_succ (C := thread P L) hf
        rw [Nat.sub_add_cancel hpos, hs, hs', hd] at hn
        refine ⟨fun h => deq_arr_next (.inl h) hn.symm, fun h => deq_arr_next (.inr h) hn.symm⟩

omit hub hg in
/-- The arrivals of the lane on its CTA's slot objects at prefix `i`. -/
private theorem arr_at (i : Nat) (f : MbarFam) :
    arrivals (MbarRow.loc L g f) ((X.tr g).take i) ≤ arrivals (MbarRow.loc L g f) (X.tr g) ∧
    arrivals (MbarRow.loc L g f) ((X.tr g).take i) =
      pc' X g i (.arrive (MbarRow.loc L g f)) :=
  ⟨(List.take_sublist i _).countP_le, wg2_arrivals hp hX hFw hw i _⟩

/-- **A lane short of its arrivals on slot `j` of a ring** (family `fam`, the arrival count
`sel` of the slot counts, the arrival at offset `o + inc s` of a block's site `s`) is no later than
the slot of its next arrival. -/
private theorem arr_early {c : Nat} {j : Fin 2} {fam : Fin 2 → MbarFam}
    {sel : Nat → Nat → Nat → Nat → Nat} {inc : Dequant.Site → Nat} {o : Nat}
    (hsel : ∀ n b a s r f, Dequant.SlotCounts L g n b a s r f →
      n (.arrive (MbarRow.loc L g (fam b))) = sel a s r f)
    (hinc : ∀ i s, sel (Dequant.uses j (i + Dequant.incR s)) (Dequant.uses j (i + Dequant.incS s))
      (Dequant.uses j (i + Dequant.incD s)) (Dequant.uses j (i + Dequant.incF s)) =
        Dequant.uses j (i + inc s))
    (hfull : ∀ R, sel (Dequant.uses j R) (Dequant.uses j R) (Dequant.uses j R)
      (Dequant.uses j R) = Dequant.uses j R)
    (hx : ∀ s x, x ≤ 83 + Dequant.incD s → Dequant.incD s ≤ 1 → x ≤ 84 →
      x ≤ o + inc s ∧ inc s ≤ 1) (ho : o ≤ 84) (hc : g / L.block = c)
    (hlt : arrivals (mbarLoc L c (fam j)) (X.tr g) < ringUses 2 j.val (blocksOf P L c)) :
    Sched.threadTime (timed P L) X g ≤
      frame (2 * arrivals (mbarLoc L c (fam j)) (X.tr g) + j.val) + deqOff + o := by
  subst hc
  have hj := j.isLt
  refine deq_end (Q := fun t => t ≤ frame (2 * arrivals (mbarLoc L (g / L.block)
    (fam j)) (X.tr g) + j.val) + deqOff + o) hp hX hFw hub hw hg (fun t ht => ?_)
    (fun i r x s hi _ hx1 hD hx2 hcnt => ?_)
    (fun i hi hF => ?_)
  · simp only [frame, loopBase, stride, deqOff]; omega
  · have h3 := (hsel _ _ _ _ _ _ (hcnt j)).trans (hinc r s)
    obtain ⟨hle, heq⟩ := arr_at hp hX hFw hw i (fam j)
    obtain ⟨hxo, hi1⟩ := hx s x hx1 hD hx2
    simp only [MbarRow.loc] at hle heq
    simp only [frame, loopBase, stride, Dequant.uses, MbarRow.loc] at h3 ⊢
    omega
  · have h3 := (hsel _ _ _ _ _ _ (hF j)).trans (hfull _)
    obtain ⟨hle, heq⟩ := arr_at hp hX hFw hw i (fam j)
    simp only [MbarRow.loc] at hle heq
    simp only [ringUses, Dequant.uses, MbarRow.loc] at h3 hlt
    omega

/-- **A dequant lane short of its uses of `dequantReady j` is no later than the arrival slot of
its next use.** -/
theorem deq_drEarly {c : Nat} {j : Fin 2} (hc : g / L.block = c)
    (hlt : arrivals (mbarLoc L c (.dequantReady j)) (X.tr g) < ringUses 2 j.val (blocksOf P L c)) :
    Sched.threadTime (timed P L) X g ≤
      drArr (2 * arrivals (mbarLoc L c (.dequantReady j)) (X.tr g) + j.val) :=
  arr_early hp hX hFw hub hw hg (fam := MbarFam.dequantReady) (sel := fun _ _ r _ => r)
    (inc := Dequant.incD) (fun _ _ _ _ _ _ ⟨_, _, h, _⟩ => h) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ h1 h2 _ => ⟨h1, h2⟩) (by decide) hc hlt

/-- **A dequant lane short of its uses of `rawFree j` is no later than the arrival slot of its
next use.** -/
theorem deq_rfEarly {c : Nat} {j : Fin 2} (hc : g / L.block = c)
    (hlt : arrivals (mbarLoc L c (.rawFree j)) (X.tr g) < ringUses 2 j.val (blocksOf P L c)) :
    Sched.threadTime (timed P L) X g ≤
      rfArr (2 * arrivals (mbarLoc L c (.rawFree j)) (X.tr g) + j.val) :=
  arr_early hp hX hFw hub hw hg (fam := MbarFam.rawFree) (sel := fun _ _ _ f => f)
    (inc := Dequant.incF) (fun _ _ _ _ _ _ ⟨_, _, _, h⟩ => h) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ _ _ h3 => ⟨h3, Nat.zero_le 1⟩) (by decide) hc hlt

omit hub hg in
/-- The slot counts behind an `exit`: every use made. -/
private theorem exit_full {k pc : Nat} (hx : X.get (g, k) = some ⟨pc, .exit⟩) :
    Full L g (pc' X g k) (blocksOf P L (g / L.block)) := by
  obtain ⟨d, hR, hs, hr⟩ := deq_exit_at hp hX hFw hw hx
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  simp only at hs hr
  subst hs
  rw [← hr]
  exact hR (wg2_take_noUb hX hx)

omit hub hg in
/-- **A lane that exited has made all its arrivals on slot `j` of a ring** (family `fam`, the
arrival count `sel` of the slot counts). -/
private theorem arr_exit {c k pc : Nat} {j : Fin 2} {fam : Fin 2 → MbarFam}
    {sel : Nat → Nat → Nat → Nat → Nat}
    (hsel : ∀ n b a s r f, Dequant.SlotCounts L g n b a s r f →
      n (.arrive (MbarRow.loc L g (fam b))) = sel a s r f)
    (hfull : ∀ R, sel (Dequant.uses j R) (Dequant.uses j R) (Dequant.uses j R)
      (Dequant.uses j R) = Dequant.uses j R)
    (hc : g / L.block = c) (hx : X.get (g, k) = some ⟨pc, .exit⟩) :
    ringUses 2 j.val (blocksOf P L c) ≤ arrivals (mbarLoc L c (fam j)) (X.tr g) := by
  subst hc
  have h3 := (hsel _ _ _ _ _ _ (exit_full hp hX hFw hw hx j)).trans (hfull _)
  have hle : arrivals (MbarRow.loc L g (fam j)) ((X.tr g).take k) ≤
      arrivals (MbarRow.loc L g (fam j)) (X.tr g) := (List.take_sublist k _).countP_le
  rw [wg2_arrivals hp hX hFw hw k] at hle
  simp only [MbarRow.loc, ringUses, Dequant.uses, pc'] at h3 hle ⊢
  have := j.isLt
  omega

omit hub hg in
/-- **A dequant lane that exited has made all its uses of `dequantReady j`.** -/
theorem deq_drExit {c k pc : Nat} {j : Fin 2} (hc : g / L.block = c)
    (hx : X.get (g, k) = some ⟨pc, .exit⟩) :
    ringUses 2 j.val (blocksOf P L c) ≤ arrivals (mbarLoc L c (.dequantReady j)) (X.tr g) :=
  arr_exit hp hX hFw hw (sel := fun _ _ r _ => r) (fun _ _ _ _ _ _ ⟨_, _, h, _⟩ => h)
    (fun _ => rfl) hc hx

omit hub hg in
/-- **A dequant lane that exited has made all its uses of `rawFree j`.** -/
theorem deq_rfExit {c k pc : Nat} {j : Fin 2} (hc : g / L.block = c)
    (hx : X.get (g, k) = some ⟨pc, .exit⟩) :
    ringUses 2 j.val (blocksOf P L c) ≤ arrivals (mbarLoc L c (.rawFree j)) (X.tr g) :=
  arr_exit hp hX hFw hw (sel := fun _ _ _ f => f) (fun _ _ _ _ _ _ ⟨_, _, _, h⟩ => h)
    (fun _ => rfl) hc hx

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
