-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerCount

@[expose] public section

/-! # A reader that read a non-claiming response never polls the response barrier again

The scheduler's exclusion (`Scheduler.sched_fail_wait`) is stated, in `ReaderExitCons`, for the
consumer: at its response wait, every read of the response buffer right after a successful response
poll names a response that claims a CTA.

Over a site-dependent proposition `nc`: a read of a non-claiming response is right after the *last*
successful response poll, and the thread is then at a site where `nc` holds (`FailRel`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

namespace Scheduler

theorem okPolls_take_mono {L : Launch} {g : Nat} (es : List Event) {j k : Nat} (h : j ≤ k) :
    okPolls (clcResp L g) (es.take j) ≤ okPolls (clcResp L g) (es.take k) := by
  induction k, h using Nat.le_induction with
  | base => exact le_refl _
  | succ k hk ih =>
    refine le_trans ih ?_
    unfold okPolls
    rw [List.take_add_one, List.countP_append]
    exact Nat.le_add_right _ _

theorem okPolls_take_succ_of {L : Launch} {g : Nat} {es : List Event} {j pc p : Nat} {acq : Bool}
    {sc : MbarScope} (hj : es[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩) :
    okPolls (clcResp L g) (es.take (j + 1)) = okPolls (clcResp L g) (es.take j) + 1 := by
  unfold okPolls
  rw [List.take_add_one, List.countP_append, hj]
  simp [okPoll, sourceWaitSuccess]

/-- Two successful polls both followed by the count of all the successful polls are one poll. -/
theorem okPolls_last_eq {L : Launch} {g : Nat} {es : List Event} {j k pc p pc' p' : Nat}
    {acq acq' : Bool} {sc sc' : MbarScope}
    (hj : es[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩)
    (hk : es[k]? = some ⟨pc', .wait (clcResp L g) p' true acq' sc'⟩)
    (hjT : okPolls (clcResp L g) (es.take j) + 1 = okPolls (clcResp L g) es)
    (hkT : okPolls (clcResp L g) (es.take k) + 1 = okPolls (clcResp L g) es) : j = k := by
  rcases Nat.lt_trichotomy j k with h | h | h
  · exfalso
    have h1 := okPolls_take_succ_of (L := L) (g := g) hj
    have h2 := okPolls_take_mono (L := L) (g := g) es (show j + 1 ≤ k from h)
    omega
  · exact h
  · exfalso
    have h1 := okPolls_take_succ_of (L := L) (g := g) hk
    have h2 := okPolls_take_mono (L := L) (g := g) es (show k + 1 ≤ j from h)
    omega

/-- The read of a non-claiming response after the last successful poll is the response the held
read gives: the two reads are the same event, so their responses agree. -/
theorem heldRead_eq_of_fail {L : Launch} {g : Nat} {es : List Event} {rr rr' : ClcResponse}
    (hH : HeldRead L g es rr') {j pc p acq sc pcr src bs} (hj : es[j]? =
      some ⟨pc, .wait (clcResp L g) p true acq sc⟩)
    (hr : es[j + 1]? = some ⟨pcr, .rd src bs⟩)
    (hT : okPolls (clcResp L g) (es.take j) + 1 = okPolls (clcResp L g) es)
    (hbs : Flow.responseOf bs = some rr) : rr' = rr := by
  unfold HeldRead at hH
  obtain ⟨j', pc', p', acq', sc', pcr', src', bs', hT', hj', hr', -, -, hrr'⟩ := hH
  have hjj := okPolls_last_eq (L := L) (g := g) hj hj' hT hT'
  subst hjj
  rw [hr] at hr'
  have h2 := Option.some.inj hr'
  simp only [Event.mk.injEq, Kind.rd.injEq] at h2
  obtain ⟨-, rfl, rfl⟩ := h2
  exact Option.some.inj (hrr'.symm.trans hbs)

theorem getElem?_snoc_split {es : List Event} {e : Event} {j : Nat} {a b : Event}
    (ha : (es ++ [e])[j]? = some a) (hb : (es ++ [e])[j + 1]? = some b) :
    (j + 1 < es.length ∧ es[j]? = some a ∧ es[j + 1]? = some b) ∨
      (j + 1 = es.length ∧ es[j]? = some a ∧ e = b) := by
  rcases Nat.lt_or_ge (j + 1) es.length with h | h
  · left
    refine ⟨h, ?_, ?_⟩
    · rw [List.getElem?_append_left (by omega)] at ha
      exact ha
    · rw [List.getElem?_append_left h] at hb
      exact hb
  · right
    have hlt := (List.getElem?_eq_some_iff.mp hb).1
    simp only [List.length_append, List.length_singleton] at hlt
    have hj : j + 1 = es.length := by omega
    refine ⟨hj, ?_, ?_⟩
    · rw [List.getElem?_append_left (by omega)] at ha
      exact ha
    · rw [hj] at hb
      simpa using hb

theorem getLast?_of_getElem?_last {es : List Event} {j : Nat} {a : Event}
    (hlen : j + 1 = es.length) (h : es[j]? = some a) : es.getLast? = some a := by
  rw [List.getLast?_eq_getElem?, show es.length - 1 = j by omega]
  exact h

/-- The last event of `pre ++ [e]` is not a successful poll when `e` is not one. -/
theorem last_not_success {L : Launch} {g : Nat} {e : Event} {pre : List Event}
    (hw : okPoll (clcResp L g) e = false) :
    ∀ pc p acq sc, (pre ++ [e]).getLast? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ → False :=
      by
  intro pc p acq sc hl
  have he : (pre ++ [e]).getLast? = some e := by simp
  rw [he] at hl
  have hpe := Option.some.inj hl
  subst hpe
  simp [okPoll, sourceWaitSuccess] at hw

end Scheduler

/-- A read of a non-claiming response right after a successful response poll is after the last
such poll, and at a state where `nc` holds; the last event is a successful response poll only where
`ld` holds. -/
def FailRel (L : Launch) (g : Nat) (nc ld : Prop) (es : List Event) : Prop :=
  (∀ j pc p acq sc pcr src bs rr, es[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ →
    es[j + 1]? = some ⟨pcr, .rd src bs⟩ → src.loc = respLoc L g → src.size = 16 →
    Flow.responseOf bs = some rr → ¬ Loader.claims rr →
    okPolls (clcResp L g) (es.take j) + 1 = okPolls (clcResp L g) es ∧ nc) ∧
  (∀ pc p acq sc, es.getLast? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ → ld)

/-- The last event is a successful response poll. -/
def LastPoll (L : Launch) (g : Nat) (es : List Event) : Prop :=
  ∃ pc p acq sc, es.getLast? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩

variable {L : Launch} {g : Nat}

/-- A step off the poll and the read: the old non-claiming reads carry `nc` to `nc'` (given their
data), and the last event is no poll. -/
theorem FailRel.step_dep {nc ld nc' : Prop} (ld' : Prop) {pre : List Event} {e : Event}
    (h : FailRel L g nc ld pre) (hld : ¬ ld) (hw : okPoll (clcResp L g) e = false)
    (hnc : ∀ j pc p acq sc pcr src bs rr, pre[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ →
      pre[j + 1]? = some ⟨pcr, .rd src bs⟩ → src.loc = respLoc L g → src.size = 16 →
      Flow.responseOf bs = some rr → ¬ Loader.claims rr → nc → nc') :
    FailRel L g nc' ld' (pre ++ [e]) := by
  have hcnt := (Scheduler.counts_snoc (L := L) (g := g) pre e).2
  rw [hw] at hcnt
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hcnt
  refine ⟨fun j pc p acq sc pcr src bs rr ha hb hl hs hr hc => ?_,
    fun pc p acq sc hl => (Scheduler.last_not_success hw pc p acq sc hl).elim⟩
  rcases Scheduler.getElem?_snoc_split ha hb with ⟨hlt, ha', hb'⟩ | ⟨hlen, ha', -⟩
  · obtain ⟨hT, hn⟩ := h.1 j pc p acq sc pcr src bs rr ha' hb' hl hs hr hc
    refine ⟨?_, hnc j pc p acq sc pcr src bs rr ha' hb' hl hs hr hc hn⟩
    rw [hcnt, List.take_append_of_le_length (by omega)]
    exact hT
  · exact absurd (h.2 _ _ _ _ (Scheduler.getLast?_of_getElem?_last hlen ha')) hld

theorem FailRel.step {nc ld nc' : Prop} (ld' : Prop) {pre : List Event} {e : Event}
    (h : FailRel L g nc ld pre) (hld : ¬ ld) (hw : okPoll (clcResp L g) e = false)
    (hnc : nc → nc') : FailRel L g nc' ld' (pre ++ [e]) :=
  h.step_dep ld' hld hw fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn => hnc hn

/-- A successful response poll when no read of a non-claiming response has happened. -/
theorem FailRel.poll {nc ld nc' ld' : Prop} {pre : List Event} {pc p : Nat} {acq : Bool}
    {sc : MbarScope} (h : FailRel L g nc ld pre) (hn : ¬ nc) (hld' : ld') :
    FailRel L g nc' ld' (pre ++ [⟨pc, .wait (clcResp L g) p true acq sc⟩]) := by
  refine ⟨fun j pc' p' acq' sc' pcr src bs rr ha hb hl hs hr hc => ?_,
    fun _ _ _ _ _ => hld'⟩
  rcases Scheduler.getElem?_snoc_split ha hb with ⟨hlt, ha', hb'⟩ | ⟨hlen, ha', hb'⟩
  · exact (hn (h.1 j pc' p' acq' sc' pcr src bs rr ha' hb' hl hs hr hc).2).elim
  · simp at hb'

/-- A read of the response buffer, right after the last successful response poll. -/
theorem FailRel.read {nc ld nc' ld' : Prop} {pre : List Event} {epc : Nat} {a : Acc}
    {bs : List (Option Byte)} (h : FailRel L g nc ld pre) (hnc : nc → nc') (hn' : nc') :
    FailRel L g nc' ld' (pre ++ [⟨epc, .rd a bs⟩]) := by
  have hread : okPoll (clcResp L g) (⟨epc, .rd a bs⟩ : Event) = false := by
    simp [okPoll, sourceWaitSuccess]
  have hcnt := (Scheduler.counts_snoc (L := L) (g := g) pre ⟨epc, .rd a bs⟩).2
  rw [hread] at hcnt
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hcnt
  refine ⟨fun j pc p acq sc pcr src bs' rr ha hb hl' hs hr hc => ?_,
    fun pc p acq sc hl' => (Scheduler.last_not_success hread pc p acq sc hl').elim⟩
  rcases Scheduler.getElem?_snoc_split ha hb with ⟨hlt, ha', hb'⟩ | ⟨hlen, ha', -⟩
  · obtain ⟨hT, hn⟩ := h.1 j pc p acq sc pcr src bs' rr ha' hb' hl' hs hr hc
    refine ⟨?_, hnc hn⟩
    rw [hcnt, List.take_append_of_le_length (by omega)]
    exact hT
  · refine ⟨?_, hn'⟩
    rw [hcnt, List.take_append_of_le_length (by omega)]
    have h1 := Scheduler.okPolls_take_succ_of (L := L) (g := g) ha'
    rw [List.take_of_length_le (by omega)] at h1
    omega

/-- Before any successful response poll no read follows one. -/
theorem FailRel.of_quiet {nc ld : Prop} {es : List Event} (h : okPolls (clcResp L g) es = 0) :
    FailRel L g nc ld es := by
  have hnone : ∀ (j pc p : Nat) (acq : Bool) (sc : MbarScope),
      es[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ → False := by
    intro j pc p acq sc hj
    have hmem := List.mem_of_getElem? hj
    have : 0 < okPolls (clcResp L g) es :=
      List.countP_pos_iff.mpr ⟨_, hmem, by simp [okPoll, sourceWaitSuccess]⟩
    omega
  refine ⟨fun j pc p acq sc pcr src bs rr ha _ _ _ _ _ => (hnone j pc p acq sc ha).elim, ?_⟩
  intro pc p acq sc hl
  rw [List.getLast?_eq_getElem?] at hl
  exact (hnone _ pc p acq sc hl).elim

/-- The read after the last successful response poll holds the response it names. -/
theorem heldRead_of_read {pre : List Event} {pc p : Nat} {acq : Bool} {sc : MbarScope} {epc : Nat}
    {a : Acc} {bs : List (Option Byte)} {rr : ClcResponse}
    (hl : pre.getLast? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩) (ha : a.loc = respLoc L g)
    (hs : a.size = 16) (hrr : Flow.responseOf bs = some rr) :
    Scheduler.HeldRead L g (pre ++ [⟨epc, .rd a bs⟩]) rr := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  have hwok : okPoll (clcResp L g) ⟨pc, .wait (clcResp L g) p true acq sc⟩ = true := by
    simp [okPoll, sourceWaitSuccess]
  have hread : okPoll (clcResp L g) (⟨epc, .rd a bs⟩ : Event) = false := by
    simp [okPoll, sourceWaitSuccess]
  refine ⟨ys.length, pc, p, acq, sc, epc, a, bs, ?_, ?_, ?_, ha, hs, hrr⟩
  · have htake : (ys ++ [(⟨pc, .wait (clcResp L g) p true acq sc⟩ : Event)] ++
        [(⟨epc, .rd a bs⟩ : Event)]).take ys.length = ys := by simp
    have hcnt2 := (Scheduler.counts_snoc (L := L) (g := g)
      (ys ++ [(⟨pc, .wait (clcResp L g) p true acq sc⟩ : Event)]) ⟨epc, .rd a bs⟩).2
    rw [hread] at hcnt2
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hcnt2
    rw [htake, hcnt2]
    have hcnt3 := (Scheduler.counts_snoc (L := L) (g := g) ys
      (⟨pc, .wait (clcResp L g) p true acq sc⟩ : Event)).2
    rw [hwok] at hcnt3
    simp only [↓reduceIte] at hcnt3
    rw [hcnt3]
  · simp
  · simp

/-- A non-claiming read that is after the last poll names the held response, when a held read
exists. -/
theorem heldRead_nc {es : List Event} {rr0 rr : ClcResponse} (hH : Scheduler.HeldRead L g es rr0)
    {j pc p acq sc pcr src bs}
    (hj : es[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩)
    (hr : es[j + 1]? = some ⟨pcr, .rd src bs⟩)
    (hT : okPolls (clcResp L g) (es.take j) + 1 = okPolls (clcResp L g) es)
    (hbs : Flow.responseOf bs = some rr) (hc : ¬ Loader.claims rr) :
    (rr0.firstCta.map fun c => c.1.toNat).getD Loader.none32 = Loader.none32 := by
  have := Scheduler.heldRead_eq_of_fail hH hj hr hT hbs
  subst this
  unfold Loader.claims at hc
  exact not_not.mp hc


end
end PTX.Kernels.Fp16Gemm8192.Proof
