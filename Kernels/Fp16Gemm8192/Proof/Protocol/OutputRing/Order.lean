-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.OutputRing.Sync
public import Lemmas.CtaBarrier.CtaBarrierIdentity
public import Lemmas.Protocol.ClusterPhase
public import Lemmas.Flow.BulkCount
public import Kernels.Fp16Gemm8192.Proof.NoBarArrive
public import Lemmas.Step.BulkWaitReady

@[expose] public section

/-! # The order of the output ring

A consumer's staging store of slice `n` (its output barrier arrivals so far `2n + 1`) happens
before the proxy fence of its group's TMA store of any slice `n' ≥ n` (arrivals `2n' + 2`): the
leader passed the generation `2n + 1` of the output barrier, which the writer's next arrival is
in (`store_before_fence`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow CtaBarrier

noncomputable section

namespace OutputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A passed generation of a group's output barrier has the arrival of that ordinal of every
thread of the group in the CTA: from the released generation for a thread that never exits, and
for an exited thread from its arrivals (`exited_member_arrival`). -/
theorem member_arrival (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {q : Nat} (hq : q < 2) {f : EvId} {pc : Nat}
    (hf : X.IsBarrier f (q + 10) (some 128) pc)
    (hpassed : f.2 + 1 < (X.tr f.1).length)
    (hagree : OutputRing.ResponsesAgreeBelow L X
      (((X.tr f.1).take f.2).countP (Execution.isBarId (q + 10))))
    {g : Nat} (hcta : g / L.block = f.1 / L.block) (hgt : g < L.threads)
    (hw : (g % L.block) / 32 ∈ group q) :
    ∃ i pc', X.IsBarrier (g, i) (q + 10) (some 128) pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId (q + 10)) =
        ((X.tr f.1).take f.2).countP (Execution.isBarId (q + 10)) := by
  refine (out_sources hX ht q).member_arrival hX (group_shape hpre hq (by omega)) hf hpassed hcta
    hw fun ⟨j, pcx, hj⟩ => ?_
  have hfg : f.1 < L.threads := Frame.lt_of_get hX hf
  have hl := Execution.exit_last hX hgt hj
  have hlast : (X.tr g).getLast? = some ⟨pcx, .exit⟩ := by
    rw [List.getLast?_eq_getElem?, show (X.tr g).length - 1 = j by omega]
    exact hj
  have hfw := (out_warp hX ht hf hfg).1
  simp only [group, Finset.mem_insert, Finset.mem_singleton] at hw hfw
  exact exited_member_arrival hX ht hgt (by omega) hlast hf hfg hcta.symm (by omega) hagree

/-- An event that is not counted precedes the counted event of the same ordinal. -/
theorem lt_of_count {p : Event → Bool} {es : List Event} {s i : Nat} {ev ei : Event}
    (hs : es[s]? = some ev) (hnp : p ev = false) (hi : es[i]? = some ei) (hp : p ei = true)
    (hc : (es.take s).countP p = (es.take i).countP p) : s < i := by
  by_contra hn
  have hle : i + 1 ≤ s := by
    rcases Nat.lt_or_ge i s with h | h
    · omega
    · have : i = s := by omega
      subst this
      rw [hs] at hi
      cases hi
      rw [hnp] at hp
      cases hp
  have hmono := (List.take_sublist_take_left (l := es) hle).countP_le (p := p)
  have hil : i < es.length := (List.getElem?_eq_some_iff.mp hi).1
  rw [List.take_add_one, List.countP_append] at hmono
  simp only [List.getElem?_eq_getElem hil] at hi
  rw [List.getElem?_eq_getElem hil] at hmono
  simp only [Option.toList_some, List.countP_singleton, Option.some.injEq] at hmono hi
  rw [hi, hp] at hmono
  simp only [↓reduceIte] at hmono
  omega

/-- An event of a thread of the group, not on the output barrier, made when its output barrier
arrivals equal a passed arrival's ordinal, happens before what follows that passed arrival. -/
theorem before_passed (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hagree : AllResponsesAgree L X)
    {q : Nat} (hq : q < 2) {h j after pc : Nat}
    (hj : X.IsBarrier (h, j) (q + 10) (some 128) pc) (hpassed : j + 1 < (X.tr h).length)
    (hafter : j < after) (hlen : after < (X.tr h).length) {g s : Nat} {ev : Event}
    (hcta : g / L.block = h / L.block) (hgt : g < L.threads)
    (hw : (g % L.block) / 32 ∈ group q) (hs : X.get (g, s) = some ev)
    (hnb : Execution.isBarId (q + 10) ev = false)
    (hcnt : ((X.tr g).take s).countP (Execution.isBarId (q + 10)) =
      ((X.tr h).take j).countP (Execution.isBarId (q + 10))) :
    baseCausality L X (g, s) (h, after) := by
  obtain ⟨i, pc', hi, hci⟩ := member_arrival hpre hX ht hq hj hpassed (.of_all hagree _) hcta hgt hw
  have hsi : s < i := lt_of_count (es := X.tr g) hs hnb hi (by simp [Execution.isBarId])
    (hcnt.trans hci.symm)
  have hht : h < L.threads := Frame.lt_of_get hX hj
  exact out_baseCausality hpre hX ht hq ⟨hgt, hht, hcta⟩ hi hj hpassed (hci) hsi hafter hlen

/-- A consumer's group, from its output barrier. -/
theorem cons_group (ht : ThreadFacts L X) {g k : Nat} {c : Consumer.D} (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.cons c)))) :
    Consumer.outId L g - 10 < 2 ∧ Consumer.outId L g = Consumer.outId L g - 10 + 10 ∧
      (g % L.block) / 32 ∈ group (Consumer.outId L g - 10) := by
  have hrw := ht.role_warp hg hk hσ
  simp only [roleWarp] at hrw
  simp only [Consumer.outId, Consumer.tidOf] at hrw ⊢
  refine ⟨by omega, by omega, ?_⟩
  simp only [group, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- A staging store of slice `n` happens before the proxy fence preceding its group's TMA store
of any later slice or the same slice. -/
theorem store_before_fence (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hagree : AllResponsesAgree L X)
    {g s h i : Nat} {ew eh : Event}
    {c c' : Consumer.D} (hw : X.get (g, s) = some ew)
    (hσw : Frame.stateAt (code L) X g s = some (some (.inr (.cons c))))
    {a : Acc} {bs : List Byte} (hws : ew.kind = .wr a bs)
    (hti : X.get (h, i) = some eh)
    (hσh : Frame.stateAt (code L) X h i = some (some (.inr (.cons c'))))
    {ma : Nat} {sp : TensorStore.Spec} (hts : eh.kind = .tensorStore ma sp)
    (hcta : g / L.block = h / L.block) (hgrp : Consumer.outId L g = Consumer.outId L h)
    (hlt : Consumer.outBars L g ((X.tr g).take s) < Consumer.outBars L h ((X.tr h).take i)) :
    baseCausality L X (g, s) (h, i - 1) := by
  have hgt : g < L.threads := Frame.lt_of_get hX hw
  have hht : h < L.threads := Frame.lt_of_get hX hti
  obtain ⟨hq, hqid, hwg⟩ := cons_group ht hgt (idx_le hw) hσw
  set q := Consumer.outId L g - 10
  obtain ⟨-, -, htma, -⟩ := ht.cons_out hht hti hσh
  obtain ⟨-, -, -, pcf, hpos, hfence⟩ := htma ma sp hts
  rw [Consumer.outBars_eq, Consumer.outBars_eq, ← hgrp, hqid] at hlt
  have hil : i < (X.tr h).length := (List.getElem?_eq_some_iff.mp hti).1
  obtain ⟨j, r, hjr, hpr, hcj⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId (q + 10))
    (xs := (X.tr h).take i) hlt
  have hji : j < i := by
    have := (List.getElem?_eq_some_iff.mp hjr).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hji] at hjr
  rw [List.take_take, Nat.min_eq_left hji.le] at hcj
  obtain ⟨rpc, rk⟩ := r
  have hbar : ∃ cnt, rk = .bar (q + 10) cnt := by
    cases rk <;> simp only [Execution.isBarId, Bool.false_eq_true, beq_iff_eq] at hpr
    case bar id' cnt m =>
      cases m
      · exact ⟨cnt, by rw [hpr]⟩
      · subst hpr
        exact (hX.noBarArrive Fact.out (h, j) _ _ _ hjr).elim
  obtain ⟨cnt, rfl⟩ := hbar
  have hjb : X.IsBarrier (h, j) (q + 10) cnt rpc := hjr
  obtain ⟨-, hcnt, -⟩ := out_warp hX ht hjb hht
  subst hcnt
  have hj1 : j ≠ i - 1 := by
    intro heq
    subst heq
    have : (X.tr h)[i - 1]? = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ := hfence
    rw [this] at hjr
    cases hjr
  refine before_passed hpre hX ht hagree hq hjb (by omega) (by omega) (by omega) hcta hgt hwg hw
    ?_ ?_
  · simp [Execution.isBarId, hws]
  · exact hcj.symm ▸ rfl

theorem countP_take_mono (p : Event → Bool) (es : List Event) {a b : Nat} (h : a ≤ b) :
    (es.take a).countP p ≤ (es.take b).countP p :=
  (List.take_sublist_take_left h).countP_le

/-- A trace prefix of the kernel has no `bar.arrive` event. -/
theorem no_arrive_take (hX : Consistent L kernel Prod mem0 X) (g s q : Nat) :
    ∀ ev ∈ (X.tr g).take s, ∀ c, ev.kind ≠ .bar q c .arrive := by
  intro ev hev c hk
  obtain ⟨k, hk'⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hev)
  obtain ⟨pc, kd⟩ := ev
  simp only at hk
  subst hk
  exact hX.noBarArrive Fact.out (g, k) _ _ _ hk'

/-- A thread's event at `j` with the given count, by the `n`-th occurrence. -/
theorem nth_bar {es : List Event} {q n : Nat} (h : n < es.countP (Execution.isBarId (q + 10)))
    (hna : ∀ ev ∈ es, ∀ c, ev.kind ≠ .bar (q + 10) c .arrive) :
    ∃ j pc cnt, j < es.length ∧ es[j]? = some ⟨pc, .bar (q + 10) cnt⟩ ∧
      (es.take j).countP (Execution.isBarId (q + 10)) = n := by
  obtain ⟨j, r, hjr, hpr, hcj⟩ := MbarRing.Slot.exists_nth_countP _ (xs := es) (c := n) h
  obtain ⟨rpc, rk⟩ := r
  cases rk <;> simp only [Execution.isBarId, Bool.false_eq_true, beq_iff_eq] at hpr
  case bar id' cnt m =>
    subst hpr
    cases m
    · exact ⟨j, rpc, cnt, (List.getElem?_eq_some_iff.mp hjr).1, hjr, hcj⟩
    · exact (hna _ (List.mem_of_getElem? hjr) cnt rfl).elim

/-- The TMA store of slice `n'` has finished reading, observed by its leader's drain wait of any
slice `n ≥ n' + 2`, which happens before every staging store of slice `n`. -/
theorem tma_before_store (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hagree : AllResponsesAgree L X)
    {g s h i : Nat} {ew eh : Event}
    {c c' : Consumer.D} (hw : X.get (g, s) = some ew)
    (hσw : Frame.stateAt (code L) X g s = some (some (.inr (.cons c))))
    {a : Acc} {bs : List Byte} (hws : ew.kind = .wr a bs)
    (hti : X.get (h, i) = some eh)
    (hσh : Frame.stateAt (code L) X h i = some (some (.inr (.cons c'))))
    {ma : Nat} {sp : TensorStore.Spec} (hts : eh.kind = .tensorStore ma sp)
    (hcta : g / L.block = h / L.block) (hgrp : Consumer.outId L g = Consumer.outId L h)
    (hlt : Consumer.outBars L h ((X.tr h).take i) + 3 ≤ Consumer.outBars L g ((X.tr g).take s)) :
    ∃ w, X.AsyncPresent (h, i) .readsDone ∧ BulkWaitsFor X .read (h, i) w ∧
      baseCausality L X w (g, s) := by
  have hgt : g < L.threads := Frame.lt_of_get hX hw
  have hht : h < L.threads := Frame.lt_of_get hX hti
  obtain ⟨hq, hqid, hwg⟩ := cons_group ht hgt (idx_le hw) hσw
  obtain ⟨hqh, hqid', hwh⟩ := cons_group ht hht (idx_le hti) hσh
  rw [← hgrp] at hqid' hwh hqh
  obtain ⟨hrelw, hstw, -, -, -, -⟩ := ht.cons_out hgt hw hσw
  obtain ⟨hrelh, -, htma, -, -, -⟩ := ht.cons_out hht hti hσh
  obtain ⟨si, i0, el, hsw, -⟩ := hstw a bs hws
  obtain ⟨st, hst, -⟩ := htma ma sp hts
  obtain ⟨hw1, -⟩ := hrelw
  obtain ⟨-, hh2⟩ := hrelh
  simp only [Consumer.D.outPhase, hsw] at hw1
  simp only [Consumer.D.outLag, hst] at hh2
  have hsi := si.isLt
  have hobg := Consumer.outBars_eq L g ((X.tr g).take s)
  have hobh := Consumer.outBars_eq L h ((X.tr h).take i)
  rw [hqid] at hobg
  rw [← hgrp, hqid] at hobh
  have hob1 : 1 ≤ Consumer.outBars L g ((X.tr g).take s) := by omega
  -- the writer's arrival of ordinal `ob - 1`, the slice's first barrier, which it passed
  have hsl : s < (X.tr g).length := (List.getElem?_eq_some_iff.mp hw).1
  obtain ⟨jg, pcg, cntg, hjgl, hjg, hcjg⟩ := nth_bar (q := Consumer.outId L g - 10)
    (es := (X.tr g).take s) (n := Consumer.outBars L g ((X.tr g).take s) - 1)
    (by rw [← hobg]; omega)
    (no_arrive_take hX _ _ _)
  have hjgs : jg < s := by simp only [List.length_take] at hjgl; omega
  rw [List.getElem?_take_of_lt hjgs] at hjg
  rw [List.take_take, Nat.min_eq_left hjgs.le] at hcjg
  have hjgb : X.IsBarrier (g, jg) (Consumer.outId L g - 10 + 10) cntg pcg := hjg
  obtain ⟨-, hcg, -⟩ := out_warp hX ht hjgb hgt
  subst hcg
  -- the leader's arrival of the same ordinal, preceded by its drain wait
  obtain ⟨ih, pch, hih, hcih⟩ := member_arrival hpre hX ht hq hjgb
    (show jg + 1 < (X.tr g).length by omega) (.of_all hagree _) hcta.symm hht hwh
  simp only at hcih
  have hihl : ih < (X.tr h).length := (List.getElem?_eq_some_iff.mp hih).1
  have hih' : X.get (h, ih) = some ⟨pch, .bar (Consumer.outId L g - 10 + 10) (some 128)⟩ := hih
  obtain ⟨dh, hσih⟩ := Frame.event_state ht.sound hX ht.tracked hih' (by simp)
  obtain ⟨ch, rfl⟩ := ht.bar_role hht hih' hσih rfl
  obtain ⟨hrelih, -, -, -, hbarih, hdrain⟩ := ht.cons_out hht hih' hσih
  have hobih := Consumer.outBars_eq L h ((X.tr h).take ih)
  rw [← hgrp, hqid] at hobih
  obtain ⟨hr1, hr2⟩ := hrelih
  have hA : ∃ k, ch.site = .barA k := by
    rcases hbarih _ (some 128) rfl with ⟨-, hid, -⟩ | ⟨⟨k, hk | hk⟩, -⟩
    · have h2 := hgrp
      have h3 := hqh
      simp only [Consumer.outId] at h2 h3 hid
      omega
    · exact ⟨k, hk⟩
    · exfalso
      simp only [Consumer.D.outPhase, hk] at hr1
      have := k.isLt
      omega
  obtain ⟨k, hk⟩ := hA
  simp only [Consumer.D.outLag, hk] at hr2
  obtain ⟨pcw, hpos, hwait⟩ := hdrain k hk
  -- the drain wait's commits equal the barrier's
  have hwl : ih - 1 < (X.tr h).length := by omega
  have hsplit : (X.tr h).take ih = (X.tr h).take (ih - 1) ++ [⟨pcw, .bulkWait .read 1⟩] := by
    have : ih = ih - 1 + 1 := by omega
    conv_lhs => rw [this]
    rw [List.take_add_one]
    have hw' : (X.tr h)[ih - 1]? = some ⟨pcw, .bulkWait .read 1⟩ := hwait
    rw [hw']
    rfl
  have hcw : commits ((X.tr h).take ih) = commits ((X.tr h).take (ih - 1)) := by
    rw [hsplit]
    simp [commits, List.countP_append, isCommit]
  have hbw : ((X.tr h).take ih).countP (Execution.isBarId (Consumer.outId L g - 10 + 10)) =
      ((X.tr h).take (ih - 1)).countP (Execution.isBarId (Consumer.outId L g - 10 + 10)) := by
    rw [hsplit]
    simp [List.countP_append, Execution.isBarId]
  -- the TMA store precedes the drain wait
  have hiw : i < ih - 1 := by
    by_contra hn
    have := countP_take_mono (Execution.isBarId (Consumer.outId L g - 10 + 10)) (X.tr h)
      (show ih - 1 ≤ i by omega)
    omega
  have hti' : X.get (h, i) = some ⟨eh.pc, .tensorStore ma sp⟩ := by
    rw [hti, ← hts]
  have hobs := observes_of_commits (X := X) (g := h) (w := ih - 1) hti' (r := 1) hiw (by omega)
  have hdone : X.AsyncPresent (h, i) .readsDone :=
    Step.BulkWait.stages_of_returned hX ⟨pcw, 1, hwait, hobs⟩
      (by show ih - 1 + 1 < (X.tr h).length; omega) .readsDone (by simp [GroupWaitStages, hti'])
  refine ⟨(h, ih - 1), hdone, ⟨pcw, 1, hwait, hobs⟩, ?_⟩
  have hsame : SameCta L h g := ⟨hht, hgt, hcta.symm⟩
  exact out_baseCausality hpre hX ht hq hsame hih' hjgb (by omega) (by rw [hcih]) (by omega)
    hjgs hsl

/-- A staging store happens before every staging store of its group in a later slice. -/
theorem store_before_store (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hagree : AllResponsesAgree L X)
    {g s g' s' : Nat} {ew ew' : Event}
    {c : Consumer.D} (hw : X.get (g, s) = some ew)
    (hσw : Frame.stateAt (code L) X g s = some (some (.inr (.cons c))))
    {a : Acc} {bs : List Byte} (hws : ew.kind = .wr a bs)
    (hw' : X.get (g', s') = some ew')
    (hcta : g / L.block = g' / L.block) (hgrp : Consumer.outId L g = Consumer.outId L g')
    (hlt : Consumer.outBars L g ((X.tr g).take s) < Consumer.outBars L g' ((X.tr g').take s')) :
    baseCausality L X (g, s) (g', s') := by
  have hgt : g < L.threads := Frame.lt_of_get hX hw
  have hgt' : g' < L.threads := Frame.lt_of_get hX hw'
  obtain ⟨hq, hqid, hwg⟩ := cons_group ht hgt (idx_le hw) hσw
  have hobg := Consumer.outBars_eq L g ((X.tr g).take s)
  have hobg' := Consumer.outBars_eq L g' ((X.tr g').take s')
  rw [hqid] at hobg
  rw [← hgrp, hqid] at hobg'
  have hsl : s' < (X.tr g').length := (List.getElem?_eq_some_iff.mp hw').1
  obtain ⟨j, pcj, cntj, hjl, hj, hcj⟩ := nth_bar (q := Consumer.outId L g - 10)
    (es := (X.tr g').take s') (n := Consumer.outBars L g ((X.tr g).take s)) (by omega)
    (no_arrive_take hX _ _ _)
  have hjs : j < s' := by simp only [List.length_take] at hjl; omega
  rw [List.getElem?_take_of_lt hjs] at hj
  rw [List.take_take, Nat.min_eq_left hjs.le] at hcj
  have hjb : X.IsBarrier (g', j) (Consumer.outId L g - 10 + 10) cntj pcj := hj
  obtain ⟨-, hcnt, -⟩ := out_warp hX ht hjb hgt'
  subst hcnt
  exact before_passed hpre hX ht hagree hq hjb (by omega) hjs hsl hcta hgt hwg hw
    (by simp [Execution.isBarId, hws]) (by rw [hcj, ← hobg])

end OutputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
