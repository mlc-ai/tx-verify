-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Values
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.AckCount
public import Lemmas.Protocol.MbarRingBlocker

@[expose] public section

/-! # Who blocks the leader scheduler at its acknowledgement wait

The leader scheduler of a cluster (its producer on the acknowledgement barrier) stopped at a
failed poll of that barrier, whose phase is not ready for its parity, has polled successfully
once more than the barrier's phase: the phase is at most its polls, since every acknowledgement is
of a use below them, and at least its polls less one, by its last successful poll. Then the
barrier's arrivals are not all in, every selector has acknowledged the uses below the phase
(`content_empty`), and by pigeonhole over the ten selectors of the ring one selector has delivered
exactly the barrier's phase many arrivals (`ack_pigeonhole`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow MBarrier AsyncCopy

noncomputable section

namespace ClcRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Whether a record is an arrival. -/
def arrRec (r : Record Ref) : Bool := match r.action with | .arrive _ _ => true | _ => false

/-- The acknowledgements of the ten selectors partition the arrivals on the acknowledgement
barrier. -/
theorem ack_partition (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (c : Nat) :
    ∀ xs : List (Record Ref), (∀ r ∈ xs, r ∈ X.objects ((slot L c).empty 0)) →
      ∑ f : Fin 10, xs.countP (selectedArrival (consumerSel L c f)) =
        xs.countP arrRec := by
  intro xs hxs
  induction xs with
  | nil => simp
  | cons r xs ih =>
    have ih := ih (fun q hq => hxs q (List.mem_cons_of_mem _ hq))
    simp only [List.countP_cons, Finset.sum_add_distrib, ih]
    congr 1
    have hr := hxs r List.mem_cons_self
    cases ha : r.action with
    | arrive n tx =>
      cases bar_source (b := ⟨.clc, 0, false⟩) hX ht Nat.one_pos hr with
      | @arrive g jj pc rel sc d hid he ha' hσ hby hcta =>
        have hg := Frame.lt_of_get hX he
        obtain ⟨rr, rfl⟩ := Bar.role_of (.inr (.inl hby))
        have hrw := ht.role_warp hg (idx_le he) hσ
        simp only [Bar.arriveCta, Bar.arriveLeader, ↓reduceIte] at hcta
        obtain ⟨b, hsel⟩ := sel_of_ack (c := c) hpre hby hrw (by omega)
        have hone : ∀ f : Fin 10, selectedArrival (consumerSel L c f) r = if f = b then true else
          false := by
          intro f
          simp only [selectedArrival, hid, ha]
          by_cases hfb : f = b
          · subst hfb; simp [hsel]
          · simp only [hfb, ↓reduceIte]
            cases hq : consumerSel L c f g
            · rfl
            · exact absurd (consumerSel_disjoint hq hsel) hfb
        simp only [hone, arrRec, ha]
        simp
      | init ha' => rw [ha] at ha'; cases ha'
      | poll _ _ ha' => rw [ha] at ha'; cases ha'
      | copy _ _ _ _ _ hby => simp [Bar.copyBy] at hby
      | notify _ _ _ _ _ hby => simp [Bar.commitBy] at hby
      | clc _ _ _ _ _ hby => simp [Bar.clcBy] at hby
    | init n => simp [selectedArrival, arrRec, ha]
    | completeTx n => simp [selectedArrival, arrRec, ha]
    | pollParity p ok => simp [selectedArrival, arrRec, ha]
    | inval => simp [selectedArrival, arrRec, ha]
    | increment => exact (no_increment hX ht hr ha).elim

/-- **The acknowledgement pigeonhole.** The leader scheduler `g` of cluster `c` (the producer of
the cluster's acknowledgement ring, warp 10 of the leader CTA), stopped at a failed poll of
the acknowledgement barrier in a phase not ready for its parity, has polled that barrier
successfully `before.phase + 1` times; and one of the ten selectors has delivered exactly
`before.phase` arrivals to the barrier. -/
theorem ack_pigeonhole (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g : Nat} (hg : g < L.threads) {c : Nat}
    (hc : g / L.block = 2 * c) (hwarp : g % L.block / 32 = 10)
    {pc p : Nat} {acq : Bool} {sc : MbarScope} {s : Scheduler.D}
    (hσp : Frame.stateAt (code L) X g ((X.tr g).length - 1) = some (some (.inr (.sched s))))
    (hlast : (X.tr g).getLast? = some
      ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) p false acq sc⟩)
    {before : State}
    (hstate : stateBefore (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩))
      (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩)).length = some before)
    (hpar : before.phase % 2 = p % 2) :
    before.phase + 1 = okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) (X.tr g) ∧
    ∃ f : Fin 10, (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩)).countP
      (selectedArrival (consumerSel L c f)) = before.phase := by
  classical
  have hacyc := hX.depAcyclic
  set R := ring hpre hX ht c with hR
  have hE : (slot L c).empty 0 = Bar.loc L (g / L.block) ⟨.clc, 0, false⟩ := by
    rw [hc]
    rfl
  have h0 : ctaOf 2 = 0 := by decide
  have h1 : warpOf 2 = 10 := by decide
  have h2 : laneZero 2 = false := by decide
  have hgsel : consumerSel L c 2 g = true := by
    simp [consumerSel, h0, h1, h2, hc, hwarp]
  -- the failed poll is the last event, after the successful polls `ys`
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
  have hlen : (X.tr g).length - 1 = ys.length := by
    rw [hys]
    simp
  have htake : (X.tr g).take ((X.tr g).length - 1) = ys := by
    rw [hlen, hys, List.take_left' rfl]
  have hok : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) (X.tr g) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) ys := by
    rw [hys, okPolls_snoc]
    simp [okPoll, sourceWaitSuccess]
  have hget : X.get (g, (X.tr g).length - 1) = some
      ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) p false acq sc⟩ := by
    change (X.tr g)[(X.tr g).length - 1]? = _
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  have hvalid : (⟨.clc, 0, false⟩ : Bar).Valid := by
    simp only [Bar.Valid, Ring.slots]
    decide
  have hpoll := ht.poll_parity (b := ⟨.clc, 0, false⟩) (cta := g / L.block) hg hget hσp rfl hvalid
  have hpo : (⟨.clc, 0, false⟩ : Bar).pollOffset = 1 := rfl
  rw [hpo, htake, ← hok, ← hE] at hpoll
  rw [← hE] at hstate ⊢
  set T := okPolls ((slot L c).empty 0) (X.tr g) with hT
  have hch := (hX.tma.2.2.1 ((slot L c).empty 0)).1
  have hni := objects_noInval hX ht ((slot L c).empty 0)
  -- a successful poller of the acknowledgement barrier in the leader's selector is `g`
  have hprod : ∀ h j pc' p' acq' sc', consumerSel L c 2 h = true →
      X.get (h, j) = some ⟨pc', .wait ((slot L c).empty 0) p' true acq' sc'⟩ → h = g :=
    fun h j pc' p' acq' sc' hh he =>
      sel_eq hpre hX ht hgsel hh hget he ⟨.sched s, hσp, hwarp⟩ trivial trivial
        (wait_role hX ht (Frame.lt_of_get hX he) he rfl)
  -- a counted completion's request follows more of `g`'s successful polls than its number
  have hreq : ∀ (f : Fin 2) s', ((0 : Fin 1), s') ∈ SF L X c f → s' + 1 ≤ T := by
    intro f s' hx
    obtain ⟨r, hr, hid, -⟩ := (mem_SF hX).mp hx
    have hid : r.id = item L X c f s' := hid
    obtain ⟨sp, tg, hci, hct, -, -⟩ := hX.clc_notified hr hid
    obtain ⟨pci, hei⟩ := hci
    obtain ⟨-, -, -, hcb⟩ := issue_facts (c := c) hpre hX ht hei hct (by have := f.isLt; omega)
    rw [issuesBefore_reqIdx hei] at hcb
    obtain ⟨j, pc', p', acq', sc', -, he'⟩ := exists_okPoll (X := X)
      (g := producer L X c) (k := reqIdx L X c s') (m := (slot L c).empty 0) (by omega)
    have hpg := hprod _ _ _ _ _ _ (producer_sel hpre c) he'
    rw [hpg] at hcb
    have := MbarRing.Poll.okPolls_mono ((slot L c).empty 0) (X.tr g)
      (show reqIdx L X c s' ≤ (X.tr g).length by
        have : reqIdx L X c s' < (X.tr (producer L X c)).length := len_of_get hei
        rw [hpg] at this
        omega)
    rw [List.take_length] at this
    omega
  -- every counted acknowledgement is of a use below `T`
  have hack : ∀ y ∈ SE L X c, y.2 + 1 ≤ T := by
    intro y hy
    have hgM := R.guardM 0 y hy y.2 le_rfl
    obtain ⟨hx, -⟩ := R.observes_full hacyc (MbarRing.Round.Slot.present_of_guard hgM) 0
    exact hreq _ _ hx
  have hexp := ring_expected (b := ⟨.clc, 0, false⟩) hpre hX ht Nat.one_pos hstate
  simp only [Bar.count] at hexp
  obtain ⟨hpend, hacc⟩ := (hch.accounted hni le_rfl).2 before hstate
  rw [hexp] at hpend hacc
  have hpos := stateBefore_pending_pos hch hstate (ack_tx hX ht hstate)
  have hU := MbarRing.Round.units_le_of_uses hch
    (fun y : Fin 10 × Nat => Ref.thread (ackEv L X c y.1 y.2)) (SE L X c)
    (i := (X.objects ((slot L c).empty 0)).length)
    (fun k q c' tx' hk hqf hqa => (ack_count hpre hX ht k q c' tx' hk hqf hqa).1)
    (fun k _ q c' tx' hk hqf hqa => (ack_count hpre hX ht k q c' tx' hk hqf hqa).2)
  have hC := MbarRing.Round.card_le_of_uses (SE L X c) (Q := T)
    (fun y hy => by have := hack y hy; omega)
  simp only [Fintype.card_fin] at hC
  have hup : before.phase ≤ T := by omega
  -- the last successful poll found the phase `T - 1`
  have hlow : T - 1 ≤ before.phase := by
    rcases Nat.lt_or_ge T 2 with hT2 | hT2
    · omega
    obtain ⟨w, pcw, pw, acqw, scw, -, hew, hcw⟩ := nth_poll (g := g) (j := (X.tr g).length)
      (o := T - 1) (m := (slot L c).empty 0) (by rw [List.take_length]; omega)
    have hpg : g = producer L X c := producer_eq hpre hX ht hgsel hew
    have hnth : MbarRing.Poll.nth X ((slot L c).empty 0) (producer L X c) (T - 1) = w := by
      rw [← hpg, ← hcw]
      exact MbarRing.Poll.nth_eq hew
    have hpres : X.RefPresent (.thread (epoll L X c (T - 1))) := by
      show X.RefPresent (.thread (producer L X c,
        MbarRing.Poll.nth X ((slot L c).empty 0) (producer L X c) (T - 1)))
      rw [hnth, ← hpg]
      exact ⟨_, hew⟩
    obtain ⟨i, w', st, hi, -, -, hst, hph, -⟩ := epoll_phase hpre hX ht (n := T - 1) (by omega)
      hpres
    obtain ⟨t, ht', hle⟩ := hch.phase_mono hni (List.getElem?_eq_some_iff.mp hi).1.le le_rfl hst
    rw [hstate] at ht'
    cases ht'
    omega
  have hT1 : before.phase + 1 = T := by omega
  refine ⟨hT1, ?_⟩
  -- every selector acknowledged the uses below the phase
  have hge : ∀ f : Fin 10, before.phase ≤
      (X.objects ((slot L c).empty 0)).countP (selectedArrival (consumerSel L c f)) := by
    intro f
    obtain ⟨P', hP'⟩ | h0 : (∃ P', before.phase = P' + 1) ∨ before.phase = 0 := by
      rcases Nat.eq_zero_or_pos before.phase with h | h
      · exact .inr h
      · exact .inl ⟨before.phase - 1, by omega⟩
    · obtain ⟨w, pcw, pw, acqw, scw, -, hew, hcw⟩ := nth_poll (g := g) (j := (X.tr g).length)
        (o := P' + 1) (m := (slot L c).empty 0) (by rw [List.take_length]; omega)
      have hpg : g = producer L X c := producer_eq hpre hX ht hgsel hew
      have hnth : MbarRing.Poll.nth X ((slot L c).empty 0) (producer L X c) (P' + 1) = w := by
        rw [← hpg, ← hcw]
        exact MbarRing.Poll.nth_eq hew
      have hpres : X.RefPresent (.thread (epoll L X c (P' + 1))) := by
        show X.RefPresent (.thread (producer L X c,
          MbarRing.Poll.nth X ((slot L c).empty 0) (producer L X c) (P' + 1)))
        rw [hnth, ← hpg]
        exact ⟨_, hew⟩
      obtain ⟨hy, -⟩ := (R.content_empty hacyc (a := 0) (n := P') hpres).2 f
      obtain ⟨r, hr, hid, -⟩ := (mem_SE hX).mp hy
      obtain ⟨ev, he⟩ : X.RefPresent (.thread (ackEv L X c f P')) :=
        hid ▸ object_record_present hX.tma hr
      have hlt := nthEv_lt_iff.mp (List.getElem?_eq_some_iff.mp he).1
      have hle := ack_arrivals_le hX (thr_sel (X := X) hpre c f)
      have : arrivals ((slot L c).empty 0) (X.tr (thr L X c f)) =
          (X.tr (thr L X c f)).countP (ackP L c) := rfl
      omega
    · omega
  -- the acknowledgements are the arrival units, fewer than the phase's ten
  have hsum := ack_partition hpre hX ht c (X.objects ((slot L c).empty 0)) (fun _ h => h)
  have hclean := fault_free hpre hX ht ((slot L c).empty_mem 0)
  have harr : (X.objects ((slot L c).empty 0)).countP arrRec =
      unitsBefore (X.objects ((slot L c).empty 0)) (X.objects ((slot L c).empty 0)).length := by
    unfold unitsBefore
    rw [List.take_length, arrivalUnits_eq_length (fun r hr c' tx hf ha => by
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
        exact (ack_count hpre hX ht k r c' tx hk hf ha).1),
      ← List.countP_eq_length_filter]
    refine List.countP_congr fun q hq => ?_
    rw [countedArrive_iff]
    have hf := hclean q hq
    unfold arrRec
    cases q.action <;> simp [hf]
  obtain ⟨f, -, hf⟩ := MbarRing.Blocker.exists_eq hch hni hstate (ack_tx hX ht hstate)
    (fun _ : Fin 10 => 1)
    (fun f => (X.objects ((slot L c).empty 0)).countP (selectedArrival (consumerSel L c f)))
    (by rw [hexp]; rfl)
    (by simp only [Nat.one_mul]; rw [hsum, harr, unitsBefore, List.take_length]) hge
    (incrementsBefore_zero hX ht _)
  exact ⟨f, hf⟩

end ClcRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
