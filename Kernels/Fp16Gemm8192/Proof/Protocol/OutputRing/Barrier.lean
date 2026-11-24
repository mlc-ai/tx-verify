-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.RingRecords
public import Kernels.Fp16Gemm8192.Proof.NoBarArrive
public import Lemmas.Protocol.NamedBarSources
public import Lemmas.CtaBarrier.CtaBarrierTraceHistory

@[expose] public section

/-! # The output barriers

Each warp group of consumers (warps `4q` to `4q+3`) has an output barrier, `q + 10`: only its
128 threads arrive there, each counting 128 (`out_sources`, of the group's shape `group_shape`), so
the library's named barrier lemmas (`NamedBar.Sources`) apply: the CTA's barrier history follows
the group's protocol and the named barrier generations are the participants' arrival ordinals.

The protocol allows exit records anywhere. A consumer whose trace ends at its exit read, as its
last response, one claiming no CTA, which every consumer of its cluster reads at the same
response poll; so no consumer polls further (`polls_le_exited`), and an exited consumer of a
group has made every arrival on the group's barriers that another member makes
(`bars_lt_exited`, `exited_member_arrival`). Only the agreement of the responses read at polls
below the other member's arrival ordinal is used (`ResponsesAgreeBelow`), so a proof of the
agreement by induction on the ordinal can use these lemmas. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow CtaBarrier

noncomputable section

namespace OutputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The responses read after successful response polls of two threads of a cluster agree at
each poll count below `n` (`AllResponsesAgree` restricted to those counts). -/
def ResponsesAgreeBelow (L : Launch) (X : Execution) (n : Nat) : Prop :=
  ∀ (c g1 g2 j1 j2 pc1 pc2 p1 p2 pcr1 pcr2 : Nat) (acq1 acq2 : Bool) (sc1 sc2 : MbarScope)
    (src1 src2 : Acc) (bs1 bs2 : List (Option Byte)),
    g1 / L.block / 2 = c → g2 / L.block / 2 = c →
    X.get (g1, j1) = some ⟨pc1, .wait (Bar.loc L (g1 / L.block) ⟨.clc, 0, true⟩) p1 true acq1 sc1⟩ →
    X.get (g2, j2) = some ⟨pc2, .wait (Bar.loc L (g2 / L.block) ⟨.clc, 0, true⟩) p2 true acq2 sc2⟩ →
    okPolls (Bar.loc L (g1 / L.block) ⟨.clc, 0, true⟩) ((X.tr g1).take j1) =
      okPolls (Bar.loc L (g2 / L.block) ⟨.clc, 0, true⟩) ((X.tr g2).take j2) →
    okPolls (Bar.loc L (g1 / L.block) ⟨.clc, 0, true⟩) ((X.tr g1).take j1) < n →
    X.get (g1, j1 + 1) = some ⟨pcr1, .rd src1 bs1⟩ →
    src1.SameFootprint ⟨⟨.shared, g1 / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
        false⟩ →
    X.get (g2, j2 + 1) = some ⟨pcr2, .rd src2 bs2⟩ →
    src2.SameFootprint ⟨⟨.shared, g2 / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
        false⟩ →
    bs1 = bs2

theorem ResponsesAgreeBelow.of_all (h : AllResponsesAgree L X) (n : Nat) :
    ResponsesAgreeBelow L X n :=
  fun c g1 g2 j1 j2 pc1 pc2 p1 p2 pcr1 pcr2 acq1 acq2 sc1 sc2 src1 src2 bs1 bs2 hc1 hc2 hw1 hw2
    hn _ hr1 hf1 hr2 hf2 =>
  h c g1 g2 j1 j2 pc1 pc2 p1 p2 pcr1 pcr2 acq1 acq2 sc1 sc2 src1 src2 bs1 bs2 hc1 hc2 hw1 hw2 hn
    hr1 hf1 hr2 hf2

/-- The warps of consumer warp group `q`. -/
def group (q : Nat) : Finset Nat := {4 * q, 4 * q + 1, 4 * q + 2, 4 * q + 3}

theorem group_card (q : Nat) : (group q).card = 4 := by
  simp only [group]
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_pair (by omega)]

theorem group_bound (hpre : Pre P L mem0) {q : Nat} (hq : q < 2) :
    ∀ w ∈ group q, w < L.block / 32 := by
  intro w hw
  rw [hpre.block]
  simp only [group, Finset.mem_insert, Finset.mem_singleton] at hw
  omega

/-- A named barrier arrival is a consumer's: its group's CLC barrier or output barrier, counting
128. -/
theorem bar_facts (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {e : EvId}
    {id pc : Nat} {cnt : Option Nat}
    (he : X.IsBarrier e id cnt pc) (hg : e.1 < L.threads) :
    cnt = some 128 ∧ (id = Consumer.tidOf L e.1 / 32 / 4 + 1 ∨ id = Consumer.outId L e.1) ∧
      Consumer.tidOf L e.1 / 32 < 8 ∧ ∃ c, Frame.stateAt (code L) X e.1 e.2 =
        some (some (.inr (.cons c))) := by
  obtain ⟨g, k⟩ := e
  have he' : X.get (g, k) = some ⟨pc, .bar id cnt⟩ := he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he' (by simp)
  obtain ⟨c, rfl⟩ := ht.bar_role hg he' hσ rfl
  have hrw := ht.role_warp hg (idx_le he') hσ
  simp only [roleWarp] at hrw
  rcases (ht.cons_out hg he' hσ).2.2.2.2.1 id cnt rfl with ⟨-, hid, hc⟩ | ⟨-, hid, hc⟩
  · exact ⟨hc, .inl hid, hrw, c, hσ⟩
  · exact ⟨hc, .inr hid, hrw, c, hσ⟩

/-- The shape of a group's named barriers: the four warps of group `q`, each counting 128. -/
theorem group_shape (hpre : Pre P L mem0) {q id : Nat} (hq : q < 2) (hid : id < 16) :
    NamedBar.Shape L (some 128) (group q) id := by
  refine ⟨by rw [group_card]; decide, ?_, group_bound hpre hq, hid⟩
  rw [group_card]
  exact NamedBar.target_some_mul (n := 4) (by decide) (by decide)

/-- **The sources of output barrier `q + 10`**: only the warps of group `q` arrive there, each
counting 128. -/
theorem out_sources (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) (q : Nat) :
    NamedBar.Sources L X (some 128) (group q) (q + 10) := by
  intro e pc cnt he hg
  obtain ⟨hc, hid, hw8, -⟩ := bar_facts hX ht (hX.isBarrier_of_arrival Fact.out he) hg
  simp only [Consumer.tidOf, Consumer.outId] at hid hw8
  refine ⟨?_, hc⟩
  simp only [group, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- A consumer whose trace ends at its exit is in an exit stage at its exit, with its counts. -/
theorem exited_state (ht : ThreadFacts L X) {g pc : Nat} (hg : g < L.threads)
    (hw : g % L.block / 32 < 8) (hlast : (X.tr g).getLast? = some ⟨pc, .exit⟩) :
    ∃ c, Frame.stateAt (code L) X g ((X.tr g).length - 1) = some (some (.inr (.cons c))) ∧
      Consumer.exitOff c ≠ none ∧ c.clcHold = 0 ∧ Consumer.tileOpen c = 0 ∧ c.inEpi = 0 ∧
      c.outPhase = 0 ∧ X.get (g, (X.tr g).length - 1) = some ⟨pc, .exit⟩ := by
  have hne : X.tr g ≠ [] := fun h => by simp [h] at hlast
  have hget : X.get (g, (X.tr g).length - 1) = some ⟨pc, .exit⟩ := by
    change (X.tr g)[(X.tr g).length - 1]? = _
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  obtain ⟨d, hσ, hoff⟩ := ht.exit_event_state hg hget
  rcases d with p | (l | m | sd | c)
  · simp [ThreadD.exitOff] at hoff
  all_goals have hrw := ht.role_warp hg (Nat.sub_le _ 1) hσ
  all_goals simp only [roleWarp] at hrw
  · omega
  · omega
  · omega
  · refine ⟨c, hσ, hoff, ?_⟩
    have hx : Consumer.exitOff c ≠ none := hoff
    unfold Consumer.exitOff at hx
    unfold Consumer.tileOpen Consumer.D.clcHold Consumer.D.inEpi Consumer.D.outPhase
    cases hs : c.site <;> simp_all

/-- **No consumer polls past an exited consumer of its cluster.** The exited consumer's last
successful response poll read a response claiming no CTA; a consumer with more successful polls
read the same response at that poll and then polled again, so it read it as claiming. The
agreement is used at the exited consumer's last poll, below `n` when `n + 1` bounds the other
consumer's polls. -/
theorem polls_le_exited (ht : ThreadFacts L X) {n : Nat} (hagree : ResponsesAgreeBelow L X n)
    {g f j pc : Nat} {c : Consumer.D} (hg : g < L.threads) (hgw : g % L.block / 32 < 8)
    (hf : f < L.threads) (hcta : f / L.block = g / L.block)
    (hlast : (X.tr g).getLast? = some ⟨pc, .exit⟩)
    (hσ : Frame.stateAt (code L) X f j = some (some (.inr (.cons c))))
    (hn : okPolls (Bar.loc L (f / L.block) ⟨.clc, 0, true⟩) ((X.tr f).take j) ≤ n + 1) :
    okPolls (Bar.loc L (f / L.block) ⟨.clc, 0, true⟩) ((X.tr f).take j) ≤
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
  by_contra hlt
  push Not at hlt
  rw [hcta] at hlt hn
  obtain ⟨-, jg, pcw, p, acq, sc, pcr, a, bs, rr, hwg, hrg, hsf, hresp, hnc, hcnt⟩ :=
    ht.cons_exit_tiles hg hgw hlast
  set m := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩ with hmdef
  set E := (X.tr f).take j with hE
  unfold okPolls at hlt hcnt
  obtain ⟨jm, e, hjm, hok, hprior⟩ := countP_index (xs := E) (p := okPoll m)
    (n := ((X.tr g).take jg).countP (okPoll m)) (by omega)
  -- a later poll follows within `E`, so the read after this poll is in `E`
  have hEl : jm + 1 < E.length := by
    by_contra hn
    push Not at hn
    have h2 : (E.take (jm + 1)).countP (okPoll m) = (E.take jm).countP (okPoll m) + 1 := by
      rw [List.take_add_one, hjm]
      simp [hok]
    rw [List.take_of_length_le hn] at h2
    omega
  have hlenE : E.length = min j (X.tr f).length := List.length_take
  obtain ⟨pm, acqm, scm, hkm⟩ := okPoll_wait_form hok
  obtain ⟨pcm, km⟩ := e
  simp only at hkm
  subst hkm
  have hjm' : X.get (f, jm) = some ⟨pcm, .wait m pm true acqm scm⟩ := by
    change (X.tr f)[jm]? = _
    rw [← hjm, hE, List.getElem?_take_of_lt (by omega)]
  have hjmf : X.get (f, jm) =
      some ⟨pcm, .wait (Bar.loc L (f / L.block) ⟨.clc, 0, true⟩) pm true acqm scm⟩ := by
    rw [hcta]
    exact hjm'
  obtain ⟨pcr2, src2, bs2, hrd2, hsf2⟩ := ht.poll_read hf hjmf (by omega)
  have htk : E.take jm = (X.tr f).take jm := by
    rw [hE, List.take_take, Nat.min_eq_left (by omega)]
  have hord : okPolls (Bar.loc L (f / L.block) ⟨.clc, 0, true⟩) ((X.tr f).take jm) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take jg) := by
    rw [hcta, ← htk]
    exact hprior
  have hbs := hagree (g / L.block / 2) f g jm jg pcm pcw pm p pcr2 pcr acqm acq scm sc src2 a
    bs2 bs (by rw [hcta]) rfl hjmf hwg hord
    (by rw [hord, ← hmdef]; unfold okPolls at hn ⊢; omega) hrd2 hsf2 hrg hsf
  subst hbs
  apply hnc
  refine ht.cons_claims hf hσ jm pcm pm acqm scm pcr2 src2 bs2 rr ?_ ?_ hsf2 hresp ?_
  · rw [List.getElem?_take_of_lt (by omega)]
    exact hjmf
  · rw [List.getElem?_take_of_lt (by omega)]
    exact hrd2
  · rw [hcta, ← hmdef]
    unfold okPolls
    rw [← hE, hprior]
    omega

/-- **An exited consumer has made more arrivals on each of its group's barriers than another member
before any of its arrivals.** -/
theorem bars_lt_exited (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g pcx : Nat}
    {f : EvId} {id pc : Nat} {cnt : Option Nat} (hg : g < L.threads) (hgw : g % L.block / 32 < 8)
    (hlast : (X.tr g).getLast? = some ⟨pcx, .exit⟩) (he : X.IsBarrier f id cnt pc)
    (hf : f.1 < L.threads) (hcta : f.1 / L.block = g / L.block)
    (hgrp : f.1 % L.block / 32 / 4 = g % L.block / 32 / 4)
    (hagree : ResponsesAgreeBelow L X (((X.tr f.1).take f.2).countP (Execution.isBarId id))) :
    ((X.tr f.1).take f.2).countP (Execution.isBarId id) <
      (X.tr g).countP (Execution.isBarId id) := by
  obtain ⟨cg, hσg, -, hh0, ht0, hi0, ho0, hgx⟩ := exited_state ht hg hgw hlast
  have hlen : 0 < (X.tr g).length := by
    have := len_of_get hgx
    simp only at this
    omega
  -- the exited consumer's totals: its counts before its exit
  have htr : X.tr g = (X.tr g).take ((X.tr g).length - 1) ++ [⟨pcx, .exit⟩] := by
    conv_lhs => rw [← List.take_append_drop ((X.tr g).length - 1) (X.tr g)]
    congr 1
    rw [List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega)]
    congr 1
    have := hgx
    change (X.tr g)[(X.tr g).length - 1]? = _ at this
    rw [List.getElem?_eq_getElem (by omega)] at this
    exact Option.some.inj this
  have hc1 := ht.cons_clc hg hgx hσg
  obtain ⟨qg, hq1, hq2⟩ := ht.cons_bar_phase hg hσg
  rw [hh0] at hc1 hq1
  rw [ht0] at hq1
  rw [hi0, ho0] at hq2
  have hT : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take ((X.tr g).length - 1)) := by
    conv_lhs => rw [htr]
    rw [okPolls_snoc]
    simp [okPoll, sourceWaitSuccess]
  have hbtot : ∀ i, (X.tr g).countP (Execution.isBarId i) =
      ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId i) := by
    intro i
    conv_lhs => rw [htr]
    simp [Execution.isBarId]
  -- the other member's arrival
  obtain ⟨-, -, -, cf, hσf⟩ := bar_facts hX ht he hf
  obtain ⟨g1, k1⟩ := f
  simp only at hf hcta hgrp hσf hagree ⊢
  have he' : X.get (g1, k1) = some ⟨pc, .bar id cnt⟩ := he
  have hc2 := ht.cons_clc hf he' hσf
  obtain ⟨qf, hr1, hr2⟩ := ht.cons_bar_phase hf hσf
  rw [hbtot]
  rcases (ht.cons_out hf he' hσf).2.2.2.2.1 id cnt rfl with ⟨hs, hid', -⟩ | ⟨⟨s, hs | hs⟩, hid', -⟩
  · -- the group's CLC barrier: the arrival consumes a held response
    have hh : cf.clcHold = 1 := by simp [Consumer.D.clcHold, hs]
    have hidg : id = Consumer.tidOf L g / 32 / 4 + 1 := by
      rw [hid']
      simp only [Consumer.tidOf]
      omega
    rw [← hid'] at hc2
    have hle := polls_le_exited ht hagree hg hgw hf hcta hlast hσf (by omega)
    rw [hcta] at hle hc2
    rw [← hidg] at hc1
    omega
  all_goals
    have hh : cf.clcHold = 0 := by simp [Consumer.D.clcHold, hs]
    have hto : Consumer.tileOpen cf = 0 := by simp [Consumer.tileOpen, hs]
    have hie : cf.inEpi = 1 := by simp [Consumer.D.inEpi, hs]
    have hop : cf.outPhase ≤ 15 := by simp [Consumer.D.outPhase, hs]; omega
    have hout : Consumer.outId L g1 = Consumer.outId L g := by
      simp only [Consumer.outId, Consumer.tidOf]
      omega
    rw [Consumer.outBars_eq, ← hout, ← hid'] at hq2
    rw [Consumer.outBars_eq, ← hid'] at hr2
    have hle := polls_le_exited ht hagree hg hgw hf hcta hlast hσf (by omega)
    rw [hcta] at hle hc2
    omega

/-- **An exited member makes every arrival of another member.** A consumer of a group whose trace
ends at its exit has an arrival on each of the group's barriers of every ordinal another member of
the group arrives at. -/
theorem exited_member_arrival (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {g pcx : Nat} {f : EvId} {id pc : Nat} {cnt : Option Nat} (hg : g < L.threads)
    (hgw : g % L.block / 32 < 8) (hlast : (X.tr g).getLast? = some ⟨pcx, .exit⟩)
    (he : X.IsBarrier f id cnt pc) (hf : f.1 < L.threads) (hcta : f.1 / L.block = g / L.block)
    (hgrp : f.1 % L.block / 32 / 4 = g % L.block / 32 / 4)
    (hagree : ResponsesAgreeBelow L X (((X.tr f.1).take f.2).countP (Execution.isBarId id))) :
    ∃ i pc', X.IsBarrier (g, i) id (some 128) pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId id) =
        ((X.tr f.1).take f.2).countP (Execution.isBarId id) := by
  obtain ⟨i, ev, hi, hb, hprior⟩ :=
    countP_index (bars_lt_exited hX ht hg hgw hlast he hf hcta hgrp hagree)
  obtain ⟨pc', kd⟩ := ev
  cases kd <;> simp only [Execution.isBarId, beq_iff_eq, Bool.false_eq_true] at hb
  rename_i id' cnt' mode'
  subst hb
  have hbar : X.IsBarrier (g, i) id' cnt' pc' :=
    hX.isBarrier_of_arrival Fact.out ⟨mode', hi⟩
  obtain ⟨hc128, -⟩ := bar_facts hX ht hbar hg
  subst hc128
  exact ⟨i, pc', hbar, hprior⟩

end OutputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
