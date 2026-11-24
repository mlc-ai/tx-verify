-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Readers
public import Kernels.Fp16Gemm8192.Proof.Protocol.RingRecords

@[expose] public section

/-! # The response phase of a blocked reader

A reader `g` of cluster `c`'s response barrier, whose last event is a failed poll, sits in the
barrier's final phase: the phase is its successful polls `N` (`reader_phase`). The final phase is
at least `N`, since the reader's last successful poll found phase `N` (`sel_poll_phase`,
`cons_poll_phase`), and at most the barrier's completions (`UnitTx.phase_le_completed`), which
are at most `N + 1`:

* for a ring selector reader (the loader, the MMA warps, the scheduler), a completion of a request
  numbered above `N` needs the selector's poll numbered `N` (`reach_op`), which the reader would
  have made (`sel_only`; `sel_completions_le`);
* for any other consumer reader, its group's barrier events are at most its polls
  (`cons_bar_le`), so a request with ordinal `N + 1` is impossible (`cons_completions_le`).

The failed poll's parity then fixes the final phase to `N` (`reader_phase`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.ClcRing

open PTX PTX.Proof PTX.Flow MBarrier AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A selector's successful polls of its own full object are the selector thread's, when the reader
`g` has a role event on the object (`sel_eq`). -/
theorem sel_only (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10} {g j pc p : Nat} {acq : Bool} {sc : MbarScope}
    {m : Loc} (hg : g < L.threads) (hsel : consumerSel L c b g = true)
    (he : X.get (g, j) = some ⟨pc, .wait m p false acq sc⟩) :
    ∀ h j' pc' p' acq' sc', consumerSel L c b h = true →
      X.get (h, j') = some ⟨pc', .wait ((slot L c).full ((slot L c).owner b)) p' true acq' sc'⟩ →
      h = g := by
  intro h j' pc' p' acq' sc' hh hf
  obtain ⟨r1, hσ1, hw1⟩ := wait_role hX ht hg he rfl
  obtain ⟨r2, hσ2, hw2⟩ := poll_state ht hX (cta := 2 * c + ctaOf b) hf
  exact sel_eq hpre hX ht hsel hh he hf ⟨r1, hσ1, hw1⟩ (by simp [ObjectKind])
    (by simp [ObjectKind]) ⟨r2, hσ2, hw2⟩

/-- **A selector's response barrier has at most one more completion than the reader's successful
polls.** A completion of a request numbered above `N` needs the selector's poll numbered `N`
(`reach_op`), which is the reader's (`sel_only`). -/
theorem sel_completions_le (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10} {g j pc p : Nat} {acq : Bool} {sc : MbarScope}
    {m : Loc} (hg : g < L.threads) (hsel : consumerSel L c b g = true)
    (he : X.get (g, j) = some ⟨pc, .wait m p false acq sc⟩) :
    completedTxCount (X.objects ((slot L c).full ((slot L c).owner b))) ≤
      okPolls ((slot L c).full ((slot L c).owner b)) (X.tr g) + 1 := by
  classical
  have hacyc := hX.depAcyclic
  set R := ring hpre hX ht c with hR
  set N := okPolls ((slot L c).full ((slot L c).owner b)) (X.tr g) with hN
  have hch := (hX.tma.2.2.1 ((slot L c).full ((slot L c).owner b))).1
  have h := countP_take_le_card hch.1 isDone
    (i := (X.objects ((slot L c).full ((slot L c).owner b))).length)
    ((Finset.range (N + 1)).image (item L X c ((slot L c).owner b))) (fun k _ r hr hd => by
      obtain ⟨hf, n, ha⟩ := isDone_iff.mp hd
      obtain ⟨s, hid⟩ := item_of_completion hpre hX ht (List.mem_of_getElem? hr) ha
      have hx : ((0 : Fin 1), s) ∈ SF L X c ((slot L c).owner b) :=
        (mem_SF hX).mpr ⟨r, List.mem_of_getElem? hr, hid, hf⟩
      refine Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr ?_, hid.symm⟩
      by_contra hgt
      obtain ⟨hpres, -⟩ := R.reach_op hacyc (fun n h1 hn => R.guardP _ _ hx n h1 hn) b
        (j := N) (by simp; omega)
      have hlt := MbarRing.Poll.nth_present.mp hpres
      obtain ⟨pcw, pw, acqw, scw, hew, -⟩ := MbarRing.Poll.nth_spec hlt
      have hgg := sel_only hpre hX ht hg hsel he _ _ _ _ _ _ (thr_sel hpre c b) hew
      rw [hgg] at hlt
      omega)
  rw [List.take_length] at h
  exact h.trans (Finset.card_image_le.trans (by simp))

/-- A failed response poll has the parity of its reader's successful polls. -/
theorem fail_parity (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g pc p : Nat}
    {acq : Bool} {sc : MbarScope}
    (hg : g < L.threads)
    (hlast : (X.tr g).getLast? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p false
      acq sc⟩) :
    p % 2 = okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) % 2 := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
  have hlen : (X.tr g).length - 1 = ys.length := by
    rw [hys]
    simp
  have htake : (X.tr g).take ((X.tr g).length - 1) = ys := by
    rw [hlen, hys, List.take_left' rfl]
  have hok : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ys := by
    rw [hys, okPolls_snoc]
    simp [okPoll, sourceWaitSuccess]
  have hget : X.get (g, (X.tr g).length - 1) = some
      ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p false acq sc⟩ := by
    change (X.tr g)[(X.tr g).length - 1]? = _
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  obtain ⟨r, hσ, -⟩ := wait_role hX ht hg hget rfl
  have hvalid : (⟨.clc, 0, true⟩ : Bar).Valid := by
    simp only [Bar.Valid, Ring.slots]
    decide
  have hpoll := ht.poll_parity (b := ⟨.clc, 0, true⟩) (cta := g / L.block) hg hget hσ rfl hvalid
  have hpo : (⟨.clc, 0, true⟩ : Bar).pollOffset = 0 := rfl
  rw [hpo, htake, ← hok] at hpoll
  omega

/-- **A consumer's group barrier events are at most its successful response polls** (its clcHold is
the one response it holds, `cons_clc`). -/
theorem cons_bar_le (ht : ThreadFacts L X) {g k : Nat} {e : Event} {c : Consumer.D}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.cons c)))) :
    ((X.tr g).take k).countP (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) ≤
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) := by
  have h := ht.cons_clc hg he hσ
  omega


/-- **The response phase of a selector reader is its successful polls.** The final phase is at
least the reader's polls, by its last successful poll, at most its completions, which are at most
its polls plus one (`sel_completions_le`), and the failed poll's parity picks the lower one. -/
theorem sel_phase (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10} {g pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hg : g < L.threads) (hsel : consumerSel L c b g = true)
    (hlast : (X.tr g).getLast? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p false
      acq sc⟩)
    {before : MBarrier.State}
    (hstate : stateBefore (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩))
      (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)).length = some before)
    (hpar : before.phase % 2 = p % 2) :
    before.phase = okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
  have hloc : (slot L c).full ((slot L c).owner b) = Bar.loc L (g / L.block) ⟨.clc, 0, true⟩ := by
    rw [sel_cta hsel]
    rfl
  have hget : X.get (g, (X.tr g).length - 1) = some
      ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p false acq sc⟩ := by
    change (X.tr g)[(X.tr g).length - 1]? = _
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  have hpar' := fail_parity hX ht hg hlast
  have hcomp := sel_completions_le hpre hX ht hg hsel hget
  rw [hloc] at hcomp
  set N := okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) with hN
  have hch := (hX.tma.2.2.1 (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)).1
  have hni := objects_noInval hX ht (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)
  have hup := (resp_unitTx hpre hX ht (g / L.block)).phase_le_completed (by norm_num) hch hni le_rfl
    hstate
  rw [List.take_length] at hup
  have hlow : N ≤ before.phase := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · omega
    obtain ⟨w, pcw, pw, acqw, scw, -, hwev, hwo⟩ := nth_poll (g := g) (j := (X.tr g).length)
      (o := N - 1) (m := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (by rw [List.take_length]; omega)
    obtain ⟨i, w', st, hi, -, -, hst, hph, -⟩ := sel_poll_phase hpre hX ht hsel
      (by rw [hloc]; exact hwev)
    rw [hloc, hwo] at hph
    rw [hloc] at hi hst
    obtain ⟨t, ht', hle⟩ := hch.phase_mono hni (List.getElem?_eq_some_iff.mp hi).1.le le_rfl hst
    rw [hstate] at ht'
    cases ht'
    omega
  omega

/-- **A consumer's barrier has at most one more completion than its polls.** A completion with
ordinal `N + 1` is the completion of the request with `N + 1` earlier ones (`ordinal_eq`); that
request targets the reader's CTA, and its group's barrier event with `N` earlier ones precedes the
reader's failed poll (`grp_request`), which the reader's barrier events may not exceed
(`cons_bar_le`). -/
theorem cons_completions_le (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hag : AllResponsesAgree L X) {g : Nat} (hg : g < L.threads)
    (hw : g % L.block / 32 < 8)
    {pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hlast : (X.tr g).getLast? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p false
      acq sc⟩) :
    (X.objects ((slot L (g / L.block / 2)).full
        (⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2))).countP isCompletion ≤
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) + 1 := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
  have hlen : (X.tr g).length - 1 = ys.length := by
    rw [hys]
    simp
  have htake : (X.tr g).take ys.length = ys := by
    rw [hys, List.take_left' rfl]
  have hok : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ys := by
    rw [hys, okPolls_snoc]
    simp [okPoll, sourceWaitSuccess]
  have hget : X.get (g, ys.length) = some
      ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p false acq sc⟩ := by
    have h1 : (X.tr g).length - 1 = ys.length := hlen
    change (X.tr g)[ys.length]? = _
    rw [← h1, ← List.getLast?_eq_getElem?]
    exact hlast
  obtain ⟨r, hσ, hwr⟩ := wait_role hX ht hg hget rfl
  have hcons : ∃ cs, r = .cons cs := by
    rcases r with l | mm | sd | cs
    · exfalso
      simp only [roleWarp] at hwr
      omega
    · exfalso
      simp only [roleWarp] at hwr
      omega
    · exfalso
      simp only [roleWarp] at hwr
      omega
    · exact ⟨cs, rfl⟩
  obtain ⟨cs, rfl⟩ := hcons
  have hq : Consumer.tidOf L g / 32 / 4 < 2 := by
    simp only [Consumer.tidOf]
    omega
  by_contra hlt
  have hcnt : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) + 1 + 1 ≤
      (X.objects ((slot L (g / L.block / 2)).full
        (⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2))).countP isCompletion := by
    omega
  obtain ⟨jd, d, hjd, hdc, hord⟩ := nth_completion hX ht hcnt
  obtain ⟨h, ki, hid⟩ := completion_request hX ht (List.mem_of_getElem? hjd) hdc
  have hiss := ordinal_eq hpre hX ht _ hjd hid hord
  obtain ⟨sI, tg, hClc, hct, -, -⟩ := Consistent.clc_notified hX (List.mem_of_getElem? hjd) hid
  obtain ⟨pcI, hgetI⟩ := hClc
  let k0 : Fin 2 := ⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩
  let q0 : Fin 2 := ⟨Consumer.tidOf L g / 32 / 4, hq⟩
  have hfirst := firstB_facts k0 q0
  have hgc : g / L.block = 2 * (g / L.block / 2) + ctaOf (firstB k0 q0) := by
    rw [hfirst.1]
    show g / L.block = 2 * (g / L.block / 2) + g / L.block % 2
    omega
  have hgw : (g % L.block) / 32 ∈ OutputRing.group (Consumer.tidOf L g / 32 / 4) := by
    simp only [OutputRing.group, Finset.mem_insert, Finset.mem_singleton, Consumer.tidOf]
    omega
  obtain ⟨ibar, pcb, hbar, hcntb, -⟩ := grp_request hpre hX ht (b := firstB k0 q0)
    (q := Consumer.tidOf L g / 32 / 4) hq hfirst.2.1 hg hgc hgw hgetI hct
    (by omega) (m := okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g))
    (by rw [hiss]; omega) (OutputRing.ResponsesAgreeBelow.of_all hag _)
  have hevt : (X.tr g)[ibar]? = some ⟨pcb, .bar (Consumer.tidOf L g / 32 / 4 + 1) (some 128)⟩ := by
    change X.get (g, ibar) = _
    exact hbar
  have hibar_lt : ibar < (X.tr g).length := (List.getElem?_eq_some_iff.mp hevt).1
  have hne : ibar ≠ ys.length := by
    intro hEq
    have hg' : X.get (g, ys.length) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p
        false acq sc⟩ := hget
    rw [hEq] at hevt
    change (X.tr g)[ys.length]? = _ at hevt
    have hget' : (X.tr g)[ys.length]? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p
        false acq sc⟩ := hget
    rw [hevt] at hget'
    cases hget'
  have hlt : ibar < ys.length := by omega
  have hcount_bar : ((X.tr g).take (ibar + 1)).countP
      (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) + 1 := by
    rw [List.take_add_one, List.countP_append, hevt]
    simp [Execution.isBarId, hcntb]
  have hle : ((X.tr g).take (ibar + 1)).countP
      (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) ≤
      ((X.tr g).take ys.length).countP (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) := by
    exact (List.take_sublist_take_left (by omega)).countP_le
  have hbar' := cons_bar_le ht hg hget hσ
  rw [htake, ← hok] at hbar'
  rw [htake] at hle
  omega


/-- **A consumer's final phase is at least its successful polls.** Its last successful response poll
found the phase `N` (`cons_poll_phase`), and the barrier's phase only grows along its log
(`CheckedLog.phase_mono`). -/
theorem cons_phase_lower (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hag : AllResponsesAgree L X) {g : Nat} (hg : g < L.threads)
    (hw : g % L.block / 32 < 8)
    {before : MBarrier.State}
    (hstate : stateBefore (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩))
      (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)).length = some before) :
    okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) ≤ before.phase := by
  rcases Nat.eq_zero_or_pos (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) with
    h0 | hpos
  · omega
  obtain ⟨w, pc, p, acq, sc, -, hwev, hwo⟩ := nth_poll (g := g) (j := (X.tr g).length)
    (o := okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) - 1)
    (m := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (by rw [List.take_length]; omega)
  obtain ⟨i, w', s, hi, -, -, hs, hsph, -⟩ :=
    cons_poll_phase hpre hX ht hg hw hwev (OutputRing.ResponsesAgreeBelow.of_all hag _)
  rw [← respFull_eq] at hi hs
  obtain ⟨t, ht1, ht2⟩ := CheckedLog.phase_mono
    (hX.tma.2.2.1 (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)).1 (objects_noInval hX ht _)
    (List.getElem?_eq_some_iff.mp hi).1.le le_rfl hs
  rw [hstate] at ht1
  cases ht1
  omega

/-- **A consumer's response phase is its successful polls.** Its phase is at least its polls
(`cons_phase_lower`), and at most its completions (`UnitTx.phase_le_completed`), which are at
most its polls plus one (`cons_completions_le`); the failed poll's parity picks the lower one. -/
theorem cons_phase_eq (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hag : AllResponsesAgree L X) {g pc p : Nat} {acq : Bool}
    {sc : MbarScope} (hg : g < L.threads)
    (hw : g % L.block / 32 < 8)
    (hlast : (X.tr g).getLast? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p false
      acq sc⟩)
    {before : MBarrier.State}
    (hstate : stateBefore (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩))
      (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)).length = some before)
    (hpar : before.phase % 2 = p % 2) :
    before.phase = okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
  have hlow := cons_phase_lower hpre hX ht hag hg hw hstate
  have hup := cons_completions_le hpre hX ht hag hg hw hlast
  have hpar' := fail_parity hX ht hg hlast
  have hloc : (slot L (g / L.block / 2)).full (⟨g / L.block % 2,
    Nat.mod_lt _ (by norm_num)⟩ : Fin 2)
      = Bar.loc L (g / L.block) ⟨.clc, 0, true⟩ := by
    show Bar.loc L (2 * (g / L.block / 2) + g / L.block % 2) _ = _
    congr 1
    omega
  rw [hloc, countP_completion_eq (L := L) (c := g / L.block / 2)
    (k := ⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩) hX ht (fun q hq => by rw [hloc]; exact hq)]
    at hup
  have hch := (hX.tma.2.2.1 (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)).1
  have hni := objects_noInval hX ht (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)
  have hfl := (resp_unitTx hpre hX ht (g / L.block)).phase_le_completed (by norm_num) hch hni le_rfl
    hstate
  rw [List.take_length] at hfl
  omega

/-- **The response phase of a reader is its successful polls.** The reader is a loader, an MMA warp,
a scheduler or a consumer by its warp (`wait_role`); the first three are ring selectors
(`consumerSel_of`), and a consumer is handled by its group barrier. The MMA warps of an odd CTA
poll no response (`mma_odd_quiet`). -/
theorem reader_phase (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hag : AllResponsesAgree L X) {g : Nat} {pc p : Nat} {acq : Bool}
    {sc : MbarScope} (hg : g < L.threads)
    (hlast : (X.tr g).getLast? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p false
      acq sc⟩)
    {before : MBarrier.State}
    (hstate : stateBefore (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩))
      (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)).length = some before)
    (hpar : before.phase % 2 = p % 2) :
    before.phase = okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
  have hlen : (X.tr g).length - 1 = ys.length := by
    rw [hys]
    simp
  have hget : X.get (g, ys.length) = some
      ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p false acq sc⟩ := by
    change (X.tr g)[ys.length]? = _
    rw [← hlen, ← List.getLast?_eq_getElem?]
    exact hlast
  obtain ⟨r, hσ, hwr⟩ := wait_role hX ht hg hget rfl
  rcases r with l | mm | sd | cs
  · have hw11 : g % L.block / 32 = 11 := hwr
    have hsel : consumerSel L (g / L.block / 2)
        (loadB ⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩) g = true :=
      consumerSel_of L _ (by
          rw [(loadB_facts _).1]
          show g / L.block = 2 * (g / L.block / 2) + g / L.block % 2
          omega)
        (by rw [(loadB_facts _).2.1]; exact hw11)
        (by rw [(loadB_facts _).2.2]; simp)
    exact sel_phase hpre hX ht hg hsel hlast hstate hpar
  · have hwm : mm.w = g % L.block / 32 ∧ (g % L.block / 32 = 8 ∨ g % L.block / 32 = 9) := hwr
    rcases Nat.mod_two_eq_zero_or_one (g / L.block) with h0 | h1
    · have hsel : consumerSel L (g / L.block / 2)
          (mmaB ⟨g % L.block / 32 - 8, by have := hwm.2; omega⟩) g = true :=
        consumerSel_of L _ (by
            rw [(mmaB_facts _).1]
            omega)
          (by
            rw [(mmaB_facts _).2.1]
            show g % L.block / 32 = 8 + (g % L.block / 32 - 8)
            have := hwm.2
            omega)
          (by rw [(mmaB_facts _).2.2]; simp)
      exact sel_phase hpre hX ht hg hsel hlast hstate hpar
    · exact absurd rfl (ht.mma_odd_quiet hg hget hσ ⟨mm, rfl⟩ h1 p false acq sc)
  · have hws : g % L.block / 32 = 10 := hwr
    have hsel : consumerSel L (g / L.block / 2)
        (schedB ⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩) g = true :=
      consumerSel_of L _ (by
          rw [(schedB_facts _).1]
          show g / L.block = 2 * (g / L.block / 2) + g / L.block % 2
          omega)
        (by rw [(schedB_facts _).2.1]; exact hws)
        (by rw [(schedB_facts _).2.2]; simp)
    exact sel_phase hpre hX ht hg hsel hlast hstate hpar
  · have hw8 : g % L.block / 32 < 8 := hwr
    exact cons_phase_eq hpre hX ht hag hg hw8 hlast hstate hpar

end

end PTX.Kernels.Fp16Gemm8192.Proof.ClcRing
