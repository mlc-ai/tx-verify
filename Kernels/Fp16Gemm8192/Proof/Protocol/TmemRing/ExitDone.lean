-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Order
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.ExitCover

@[expose] public section

/-! # The accumulator ring's completion before the release

An event that a thread makes past its exit wait follows the exit wait's phase, which every thread
of the cluster completes with its second cluster arrival (`two_arrivals_of_wait`); an event of a
thread before that arrival happens before it (`exitWaited_order`).

A Tensor Memory load is a consumer's in its task loop, before its second arrival
(`ThreadFacts.data_loop`), and its wait follows it (`ThreadFacts.cons_load`): the load is finished
before the event (`load_done`).

An MMA of buffer `j` has fewer accumulator commits before it than its thread's successful response
polls, the reads after the earlier ones claiming a CTA (`ThreadFacts.mma_tile`). The buffer's
consumer at the first thread of warp `4 j` of the leader CTA makes its second arrival in its exit
stage (`cons_exit_arrival`), where it has polled the full barrier once per successful response poll,
its latest response read claiming no CTA (`ThreadFacts.cons_exit_stage`). The responses agree, so
the consumer polled the response at least as often, and one of its full polls before its arrival
observes the MMA (`mma_observed`): the MMA is observed complete before the event (`mma_done`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace TmemRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An event past its thread's exit wait: every thread of its cluster has made both its cluster
arrivals. -/
theorem waited_arrivals (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {f : EvId} {ev : Event} (hf : X.get f = some ev)
    (hEW : ExitWaited ((X.tr f.1).take f.2)) {g : Nat} (hg : g < L.threads)
    (hsame : L.clusterOfCta (g / L.block) = L.clusterOfCta (f.1 / L.block)) :
    clArrives (X.tr g) = 2 := by
  have hfx : f.2 < (X.tr f.1).length := len_of_get hf
  obtain ⟨j, pcj, alj, hjf, hwj, hcountj⟩ := exit_wait_of hEW
  have h2 := two_arrivals_of_wait hpre hX ht (h := f.1) (j := j) hwj (by omega) hcountj hsame
  have h3 := clArrives_take_le hX ht hg (X.tr g).length
  rw [List.take_length] at h3
  omega

/-- **The exit arrival of a consumer.** A consumer thread with both its cluster arrivals makes the
second in its exit stage, with one arrival before it. -/
theorem cons_exit_arrival (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {h : Nat}
    (hh : h < L.threads)
    (hw : h % L.block / 32 < 8) (h2 : clArrives (X.tr h) = 2) :
    ∃ ka c, ka < (X.tr h).length ∧ Frame.stateAt (code L) X h ka = some (some (.inr (.cons c))) ∧
      Consumer.exitOff c ≠ none ∧ clArrives ((X.tr h).take ka) = 1 := by
  obtain ⟨ka, ea, hea, harr, hcnt⟩ := MbarRing.Slot.exists_nth_countP isClArrive
    (xs := X.tr h) (c := 1) (by unfold clArrives at h2; omega)
  have hlt := (List.getElem?_eq_some_iff.mp hea).1
  obtain ⟨rel, al, hk⟩ := ClusterTrace.isArr_kind harr
  have he : X.get (h, ka) = some ea := hea
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by rintro pc f rfl; cases hk)
  have hph := (ht.cluster hh he hσ).1
  have hc1 : clArrives ((X.tr h).take ka) = 1 := hcnt
  rw [hc1] at hph
  obtain ⟨hev, hat⟩ := ((ht.cl_ops hh hσ).2 ea he).1 (by simp [isCluster, hk])
  rcases d with p | (l | m | sd | cs)
  · exfalso
    simp only [ThreadD.AtCluster] at hat
    rcases hat with h | h
    · simp [ThreadD.clPhase, h] at hph
    · simp only [ThreadD.clOps, h, clEvent] at hev
      rw [hev] at hk
      cases hk
  all_goals have hr := ht.role_warp hh hlt.le hσ
  all_goals simp only [roleWarp] at hr
  · omega
  · omega
  · omega
  · simp only [ThreadD.AtCluster] at hat
    rcases hat with hs | hs
    · exact ⟨ka, cs, hlt, hσ, by simp [Consumer.exitOff, hs], hc1⟩
    · simp [ThreadD.clPhase, hs] at hph

/-- **A Tensor Memory load is finished before an event of its cluster past an exit wait.** -/
theorem load_done (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {i f : EvId} {a : Nat} {vals : List Value} {sh : TcShape}
    {ev : Event} (hld : X.TLd i a vals sh) (hf : X.get f = some ev)
    (hEW : ExitWaited ((X.tr f.1).take f.2))
    (hc : f.1 / L.block / 2 = i.1 / L.block / 2) : TcMma.WaitBefore L X .waitLd i f := by
  obtain ⟨h, k⟩ := i
  obtain ⟨pc, hget⟩ := hld
  have hh := Frame.lt_of_get hX hget
  obtain rfl := ht.ld_shape hh hget
  have hfh := Frame.lt_of_get hX hf
  have hsame : L.clusterOfCta (h / L.block) = L.clusterOfCta (f.1 / L.block) := by
    simp only [clusterOfCta_eq hpre]
    simp only at hc
    omega
  obtain ⟨c, hσ, hoff, -⟩ := ht.data_loop hh hget rfl
  have hph : clArrives ((X.tr h).take k) ≤ 1 := by
    rw [(ht.cluster hh hget hσ).1]
    exact InputRing.clPhase_le_of_exitOff hoff
  have h2 := waited_arrivals hpre hX ht hf hEW hh hsame
  have hnot : ∀ {j : Nat} {e : Event}, (X.tr h)[j]? = some e → isClArrive e = false →
      clArrives ((X.tr h).take (j + 1)) = clArrives ((X.tr h).take j) := fun hj hn =>
    ClusterTrace.countP_take_succ_not hj hn
  have hk1 : clArrives ((X.tr h).take (k + 1)) ≤ 1 := by
    rw [hnot (show (X.tr h)[k]? = _ from hget) rfl]
    exact hph
  have hklen : k + 1 < (X.tr h).length := by
    by_contra hn
    rw [List.take_of_length_le (by omega)] at hk1
    omega
  have hw := (ht.cons_load hh hget hσ).2.2 hklen
  obtain ⟨pcw, hwget⟩ := hw
  have hk2 : ((X.tr h).take ((k + 1) + 1)).countP ClusterTrace.isArr ≤ 1 := by
    have := hnot (show (X.tr h)[k + 1]? = _ from hwget) rfl
    change clArrives _ ≤ 1
    omega
  exact ⟨(h, k + 1), ⟨pcw, hwget⟩, rfl, by simp,
    .inl (exitWaited_order hpre hX ht (e := (h, k + 1)) hk2 hf hEW ⟨hh, hfh, hsame⟩)⟩

/-- **An MMA is observed complete before an event of its cluster past an exit wait.** -/
theorem mma_done (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hag : AllResponsesAgree L X) {i f : EvId} {d : Nat}
    {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat} {ev : Event}
    (hmma : X.MmaIssue i d s acc mask) (hf : X.get f = some ev)
    (hEW : ExitWaited ((X.tr f.1).take f.2)) (hcf : f.1 / L.block / 2 = i.1 / L.block / 2) :
    TcMma.DoneBefore L X i f := by
  have hblock := hpre.block
  obtain ⟨M, k⟩ := i
  obtain ⟨pcm, hem⟩ := hmma
  have hM := Frame.lt_of_get hX hem
  have hfh := Frame.lt_of_get hX hf
  obtain ⟨dm, hσm⟩ := Frame.event_state ht.sound hX ht.tracked hem (by simp)
  obtain ⟨hw89, hlead, hbatch⟩ := ht.mma_acc_batch hM hem hσm rfl
  obtain ⟨hlt, hclaims⟩ := ht.mma_tile hM hem hσm rfl
  set c := M / L.block / 2 with hc
  set j : Fin 2 := ⟨M % L.block / 32 % 2, Nat.mod_lt _ (by decide)⟩ with hj
  have hMc : M / L.block = 2 * c := by omega
  -- the MMA thread is the buffer's producer
  have hempty : Bar.loc L (M / L.block) ⟨.acc, M % L.block / 32 % 2, false⟩ =
    (slot L c j).empty 0 := by
    simp only [slot, hMc, hj]
  have hfull0 : Bar.loc L (M / L.block) ⟨.acc, M % L.block / 32 % 2, true⟩ = (slot L c j).full 0 :=
    by
    simp only [slot, hMc, hj, Fin.val_zero, Nat.add_zero]
  rw [hempty, hfull0] at hbatch
  rw [hfull0] at hlt
  have hprod : producerThread L c j M = true := by
    simp only [producerThread, decide_eq_true_eq, hj]
    omega
  obtain ⟨jp, pcp, pp, acqp, scp, -, hep⟩ := exists_okPoll (X := X) (g := M) (k := k)
    (m := (slot L c j).empty 0) (by omega)
  have hMp : M = producer L X c j := producer_eq hX ht hprod hep
  -- the buffer's consumer at the first thread of warp `4 j` of the leader CTA
  set h := consumerOf L c j 0 with hhdef
  have hhv : h = 2 * c * L.block + 128 * j.val := by
    simp only [hhdef, consumerOf, Fin.val_zero, Nat.zero_div, Nat.add_zero, Nat.zero_mod]
  have hgr : M / L.block < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).mpr hM
  have hh : h < L.threads := by
    change _ < L.grid * L.block
    have := j.isLt
    rw [hhv, hblock]
    rw [hblock] at hgr hMc
    omega
  have hhc : h / L.block = 2 * c := by
    have := j.isLt
    rw [hhv, hblock]
    omega
  have hhw : h % L.block / 32 / 4 = j.val := by
    have := j.isLt
    rw [hhv, hblock]
    omega
  have hsame : L.clusterOfCta (h / L.block) = L.clusterOfCta (f.1 / L.block) := by
    simp only [clusterOfCta_eq hpre]
    omega
  have h2 := waited_arrivals hpre hX ht hf hEW hh hsame
  obtain ⟨ka, cs, hka, hσa, hoff, hka1⟩ := cons_exit_arrival hX ht hh (by omega) h2
  obtain ⟨hpollh, jhr, pchr, phr, acqhr, schr, pcrh, srch, bsh, rrh, hwhr, hrhr, hsfh, hresph,
    hnch, hcnth⟩ := ht.cons_exit_stage hh hka.le hσa hoff
  set Rh := okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) ((X.tr h).take ka) with hRh
  set RM := okPolls (Bar.loc L (M / L.block) ⟨.clc, 0, true⟩) ((X.tr M).take k) with hRM
  -- the consumer polled the response at least as often
  have hle : RM ≤ Rh := by
    by_contra hgt
    push Not at hgt
    obtain ⟨jm, pcm', pm, acqm, scm, hjm, hwm, hcm'⟩ := MbarRing.Poll.exists_nth (X := X) (g := M)
      (k := k) (m := Bar.loc L (M / L.block) ⟨.clc, 0, true⟩) (n := Rh - 1) (by omega)
    obtain ⟨pcr, a', bs', rr', hrd, hsf, hresp, hcl⟩ := hclaims jm pcm' pm acqm scm hwm (by omega)
    have hbs := hag c h M jhr jm pchr pcm' phr pm pcrh pcr acqhr acqm schr scm srch a' bsh bs'
      (by omega) rfl hwhr hwm (by omega) hrhr hsfh hrd hsf
    rw [hbs, hresp] at hresph
    obtain rfl := Option.some.inj hresph
    exact hnch hcl
  -- a full poll of the consumer before its arrival observes the MMA
  have hF : Bar.loc L (h / L.block) ⟨.acc, h % L.block / 32 / 4, true⟩ =
      (slot L c j).full ((slot L c j).owner 0) := by
    rw [hhc, hhw]
    rfl
  rw [hF] at hpollh
  obtain ⟨jw, pcw, pw, acqw, scw, hjw, hww, hcw⟩ := MbarRing.Poll.exists_nth (X := X) (g := h)
    (k := ka) (m := (slot L c j).full ((slot L c j).owner 0))
    (n := ((X.tr M).take k).countP (commitsTo ((slot L c j).full 0))) (by omega)
  have hsucc : ((X.tr M).take (k + 1)).countP (commitsTo ((slot L c j).full 0)) =
      ((X.tr M).take k).countP (commitsTo ((slot L c j).full 0)) := by
    rw [List.take_add_one, show (X.tr M)[k]? = _ from hem]
    simp [commitsTo]
  have hR : X.TcAsync (producer L X c j, k) := by
    rw [← hMp]
    exact .inl ⟨d, s, acc, mask, pcm, hem⟩
  rw [hMp] at hsucc
  obtain ⟨jw', hjw', ws, hobs, hsc⟩ := mma_observed hpre hX ht hR hww hcw (by rw [hsucc, ← hMp])
  have hcnt : ((X.tr h).take (jw' + 1)).countP ClusterTrace.isArr ≤ 1 := by
    have := ClusterTrace.countP_take_mono (xs := X.tr h) (p := ClusterTrace.isArr)
      (show jw' + 1 ≤ ka by omega)
    change _ ≤ clArrives _ at this
    omega
  rw [hMp]
  exact .inl ⟨_, ws, hobs, hsc,
    exitWaited_order hpre hX ht (e := (h, jw')) hcnt hf hEW ⟨hh, hfh, hsame⟩⟩

/-- **The accumulator ring's completion before the release** (`TmemExitDone`). -/
theorem tmemExitDone (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hag : AllResponsesAgree L X) : TmemExitDone L X :=
  ⟨fun _ _ _ _ _ _ _ hm hf hEW hc => mma_done hpre hX ht hag hm hf hEW hc,
    fun _ _ _ _ _ _ hl hf hEW hc => load_done hpre hX ht hl hf hEW hc⟩

end TmemRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
