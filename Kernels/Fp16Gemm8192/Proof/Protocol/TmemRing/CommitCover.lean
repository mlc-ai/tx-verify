-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Order
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.CommitCover

@[expose] public section

/-! # The commits notified an exited CTA

An accumulator commit of MMA warp `8 + j` notifies buffer `j`'s full barrier in both CTAs of the
pair. Once a CTA of the pair has exited, so has the consumer of buffer `j` at the first thread of
warp `4 j`: its successful polls of the full barrier are its successful response polls, its latest
response read claiming no CTA (`ThreadFacts.cons_exit_tiles`). The MMA thread has made its exit
arrival (`ClusterExitAll`), before which lie all its commits (`commit_before_arrival`), its
accumulator commits as many as its successful response polls, its earlier response reads claiming
(`ThreadFacts.mma_exit_reads`). The responses agree, so the consumer polled the response at least
as often; its last full poll finds at least as many notifications (`cons_poll`), each of a distinct
commit of the producer (`notify_commit`), one of them the commit's (`acc_commit_notified`).

With the slots' commits (`InputRing.slot_commit_notified`), every commit notified an exited CTA it
targets, before an exit of that CTA (`commitNotified`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace TmemRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **An accumulator commit notified an exited CTA of the pair.** -/
theorem acc_commit_notified (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hag : AllResponsesAgree L X) {M kc pcc : Nat}
    {csp : TcCommit.Spec} {k : Fin 2}
    (hec : X.get (M, kc) = some ⟨pcc, .tc (.commit csp)⟩)
    (hmb : csp.mbar = Bar.loc L (M / L.block) ⟨.acc, M % L.block / 32 % 2, true⟩)
    (hex : CtaExited L X (M / L.block + k.val)) :
    SharedFinished L kernel Prod X (.async (M, kc) (.tcNotify ⟨k.val, by omega⟩))
      (M / L.block + k.val) := by
  classical
  have hb := hpre.block
  have hgr := hpre.grid
  have hM := Frame.lt_of_get hX hec
  obtain ⟨dc, hσc⟩ := Frame.event_state ht.sound hX ht.tracked hec (by simp)
  obtain ⟨mc, rfl, heven, -⟩ := ht.commit_spec hM hec hσc rfl
  have hwM := ht.role_warp hM (len_of_get hec).le hσc
  simp only [roleWarp] at hwM
  set c := M / L.block / 2 with hc
  have hMc : M / L.block = 2 * c := by omega
  set j : Fin 2 := ⟨M % L.block / 32 % 2, by omega⟩ with hj
  have hMg : M / L.block < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).mpr hM
  have hTg : M / L.block + k.val < L.grid := by
    have := k.isLt
    rw [hgr] at hMg ⊢
    omega
  -- the consumer of buffer `j` at the first thread of warp `4 j` of the exited CTA
  set h := (M / L.block + k.val) * L.block + 128 * j.val with hh
  have hht : h < L.threads := by
    change _ < L.grid * L.block
    have := j.isLt
    rw [hh, hb]
    rw [hb] at hTg
    omega
  have hhc : h / L.block = M / L.block + k.val := by
    have := j.isLt
    rw [hh, hb]
    omega
  have hhm : h % L.block = 128 * j.val := by
    have := j.isLt
    rw [hh, hb]
    omega
  have hhw : h % L.block / 32 < 8 := by have := j.isLt; omega
  obtain ⟨px, hlasth⟩ := hex h hht hhc
  obtain ⟨hpollh, jhr, pchr, phr, acqhr, schr, pcrh, srch, bsh, rrh, hwhr, hrhr, hsfh, hresph,
    hnch, hcnth⟩ := ht.cons_exit_tiles hht hhw hlasth
  set b : Fin 256 := ⟨k.val * 128, by have := k.isLt; omega⟩ with hbdef
  have hcb : consumerOf L c j b = h := by
    have := k.isLt
    have := j.isLt
    rw [hh, hMc]
    simp only [consumerOf, hbdef]
    rw [hb]
    omega
  have hown : (slot L c j).owner b = k := by
    apply Fin.ext
    simp only [slot, hbdef]
    omega
  set F := (slot L c j).full k with hF
  have hgrp : h % L.block / 32 / 4 = j.val := by
    have := j.isLt
    rw [hhm]
    omega
  have hFh : (Bar.loc L (h / L.block) ⟨.acc, h % L.block / 32 / 4, true⟩ : Loc) = F := by
    rw [hhc, hMc, hgrp]
    rfl
  rw [hFh] at hpollh
  -- the MMA thread's exit arrival
  have h2 := clusterExitAll hpre hX ht h px hht hlasth M hM
    (by simp only [clusterOfCta_eq hpre]; omega)
  obtain ⟨ka, m', hkal, hσa, hsa, hka1, ea, hea, harr⟩ := InputRing.exit_arrival hX ht hM hwM.2 h2
  obtain ⟨hacc, hcbm⟩ := ht.mma_exit_reads hM hkal.le hσa hsa
  set Rh := okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h) with hRh
  set RM := okPolls (Bar.loc L (M / L.block) ⟨.clc, 0, true⟩) ((X.tr M).take ka) with hRM
  -- the consumer polled the response at least as often
  have hle : RM ≤ Rh := by
    by_contra hlt
    push Not at hlt
    obtain ⟨jm, pcm, pm, acqm, scm, hjm, hwm, hcm'⟩ := MbarRing.Poll.exists_nth (X := X) (g := M)
      (k := ka) (m := Bar.loc L (M / L.block) ⟨.clc, 0, true⟩) (n := Rh - 1) (by omega)
    obtain ⟨pcr, a', bs', rr', hrd, hsf, hresp, hcl⟩ := hcbm jm pcm pm acqm scm hwm (by omega)
    have hbs := hag c h M jhr jm pchr pcm phr pm pcrh pcr acqhr acqm schr scm srch a' bsh bs'
      (by omega) rfl hwhr hwm (by omega) hrhr hsfh hrd hsf
    rw [hbs, hresp] at hresph
    obtain rfl := Option.some.inj hresph
    exact hnch hcl
  -- the consumer's last full poll
  have hRh1 : 1 ≤ Rh := by omega
  obtain ⟨jw, pcw, pw, acqw, scw, hjw, hww, hcw⟩ := MbarRing.Poll.exists_nth (X := X) (g := h)
    (k := (X.tr h).length) (m := F) (n := Rh - 1) (by rw [List.take_length, hpollh]; omega)
  have hww' : X.get (consumerOf L c j b, jw) =
      some ⟨pcw, .wait ((slot L c j).full ((slot L c j).owner b)) pw true acqw scw⟩ := by
    rw [hcb, hown]
    exact hww
  obtain ⟨jr, w, hjr, hwid, -, -, -, hfl⟩ := cons_poll hpre hX ht hww'
  rw [hcb, hown, ← hF] at hfl
  rw [hown, ← hF] at hjr
  rw [hcb] at hwid
  rw [hcw] at hfl
  -- the MMA thread is the buffer's producer
  have hF0 : Bar.loc L (M / L.block) ⟨.acc, M % L.block / 32 % 2, true⟩ = (slot L c j).full 0 := by
    rw [hMc]
    rfl
  rw [hF0] at hacc hmb
  have hprod : producerThread L c j M = true := by
    simp only [producerThread, decide_eq_true_eq, hj]
    omega
  have hkc : kc < ka := InputRing.commit_before_arrival hX ht hM hea harr hka1 hec
  have hcmb : commitsTo ((slot L c j).full 0) ⟨pcc, .tc (.commit csp)⟩ = true := by
    simp [commitsTo, hmb]
  have hpoll : ∃ jf pcf pf acqf scf, X.get (M, jf) =
      some ⟨pcf, .wait ((slot L c j).empty 0) pf true acqf scf⟩ := by
    have htg := ht.acc_commit_ranks (j := j) (⟨0, by decide⟩ : Fin 16) hM hec hσc rfl
      (by rw [hmb, ← hF0]) (by decide)
    have hcbud := ht.commit_budget (b := ⟨.acc, j.val, true⟩) hM hec hσc rfl htg j.isLt
    have hpe : (Bar.partner ⟨.acc, j.val, true⟩).loc L (M / L.block) = (slot L c j).empty 0 := by
      simp only [slot, Bar.partner, Bool.not_true, hMc]
    rw [hpe] at hcbud
    obtain ⟨jf, pcf, pf, acqf, scf, -, hf⟩ := exists_okPoll (X := X) (g := M) (k := kc)
      (m := (slot L c j).empty 0) (by omega)
    exact ⟨jf, pcf, pf, acqf, scf, hf⟩
  obtain ⟨jf, pcf, pf, acqf, scf, hf⟩ := hpoll
  have hMeq := producer_eq hX ht hprod hf
  -- the notifications before the consumer's poll name every commit; one names this commit
  let f : Record Ref → Nat := fun x => match x.id with
    | .async i _ => i.2
    | _ => 0
  set xs := ((X.objects F).take jr).filter isArrival with hxs
  have hnd : (X.objects F).Nodup := List.Nodup.of_map _ (hX.tma.2.2.1 F).1.1
  have hxsnd : xs.Nodup := (hnd.sublist (List.take_sublist _ _)).filter _
  have hcommit_of : ∀ x ∈ xs, ∃ jc pcx sp, x.id = .async (M, jc) (.tcNotify ⟨k.val, by omega⟩) ∧
      X.get (M, jc) = some ⟨pcx, .tc (.commit sp)⟩ ∧ sp.mbar = (slot L c j).full 0 ∧
      x ∈ X.objects F := by
    intro x hx
    obtain ⟨hxt, hxn⟩ := List.mem_filter.mp hx
    obtain ⟨jc, pcx, sp, hid, hcx, hmbx, -⟩ :=
      notify_commit hpre hX ht (List.mem_of_mem_take hxt) hxn
    rw [← hMeq] at hid hcx
    exact ⟨jc, pcx, sp, hid, hcx, hmbx, List.mem_of_mem_take hxt⟩
  obtain ⟨x, hx, hfx⟩ := InputRing.exists_hit xs hxsnd (X.tr M) (commitsTo ((slot L c j).full 0))
    ka f
    (fun x hx => by
      obtain ⟨jc, pcx, sp, hid, hcx, hmbx, -⟩ := hcommit_of x hx
      have hfx : f x = jc := by simp only [f, hid]
      rw [hfx]
      refine ⟨InputRing.commit_before_arrival hX ht hM hea harr hka1 hcx, ?_⟩
      change (X.get (M, jc)).any _ = true
      rw [hcx]
      simp [commitsTo, hmbx])
    (fun x hx y hy hxy => by
      obtain ⟨jc, -, -, hid, -, -, hxm⟩ := hcommit_of x hx
      obtain ⟨jc', -, -, hid', -, -, hym⟩ := hcommit_of y hy
      have h1 : f x = jc := by simp only [f, hid]
      have h2 : f y = jc' := by simp only [f, hid']
      rw [h1, h2] at hxy
      subst hxy
      exact hX.record_eq hxm hym (hid.trans hid'.symm))
    (by
      rw [hacc, hxs, ← List.countP_eq_length_filter]
      omega)
    hkc (by change (X.get (M, kc)).any _ = true; rw [hec]; exact hcmb)
  obtain ⟨jc, pcx, sp, hid, -, -, hxm⟩ := hcommit_of x hx
  have hfx' : f x = jc := by simp only [f, hid]
  rw [hfx'] at hfx
  subst hfx
  -- the notification is present, and before the poll in the barrier's history
  have hobj : objectAction X X.async F (.async (M, jc) (.tcNotify ⟨k.val, by omega⟩)) =
      some x.action := by
    have h := ((hX.tma.2.2.1 _).2.1 x hxm).1
    rw [hid] at h
    exact h
  obtain ⟨-, -, -, -, hnotif⟩ := notify_facts hobj
  obtain ⟨hxt, -⟩ := List.mem_filter.mp hx
  obtain ⟨ix, hix⟩ := List.getElem?_of_mem hxt
  have hixl : ix < jr := by
    have := (List.getElem?_eq_some_iff.mp hix).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hixl] at hix
  have hbefore : MBarrier.Before (X.objects F) (.async (M, jc) (.tcNotify ⟨k.val, by omega⟩))
      (.thread (h, jw)) := ⟨ix, jr, x, w, hix, hid, hjr, hwid, hixl⟩
  refine ⟨hnotif, (h, (X.tr h).length - 1), px, hht, hhc, InputRing.exit_get hlasth, ?_⟩
  exact CompletedBefore.of_before hbefore (InputRing.before_exit hX ht hlasth hww)

end TmemRing

/-- **Every commit notified an exited CTA it targets.** -/
theorem commitNotified (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hag : AllResponsesAgree L X) : CommitNotified L X := by
  intro i s rank m hc htg hexit
  obtain ⟨M, kc⟩ := i
  obtain ⟨pcc, hec⟩ := hc
  have hM := Frame.lt_of_get hX hec
  obtain ⟨dc, hσc⟩ := Frame.event_state ht.sound hX ht.tracked hec (by simp)
  obtain ⟨mc, -, heven, hsite⟩ := ht.commit_spec hM hec hσc rfl
  have hr : rank.val < s.clusterSize ∧ s.mask.toNat / 2 ^ rank.val % 2 = 1 := by
    by_contra hn
    simp [TcCommit.target, hn] at htg
  simp only [TcCommit.target, hr, and_self, ↓reduceIte] at htg
  obtain rfl := Option.some.inj htg
  have hr2 : rank.val < 2 := by rcases hsite with ⟨_, -, rfl⟩ | ⟨-, rfl⟩ <;> exact hr.1
  set a : Fin 2 := ⟨rank.val, hr2⟩ with ha
  have hrank : rank = ⟨a.val, by omega⟩ := Fin.ext rfl
  have hcta : s.clusterBase + rank.val = M / L.block + a.val := by
    rcases hsite with ⟨_, -, rfl⟩ | ⟨-, rfl⟩ <;> simp only [ha] <;> omega
  simp only [hcta] at hexit ⊢
  rw [hrank]
  rcases hsite with ⟨s', -, rfl⟩ | ⟨-, rfl⟩
  · exact InputRing.slot_commit_notified hpre hX ht hag hec
      (InputRing.emptyLoc_bar L _ s') hexit
  · exact TmemRing.acc_commit_notified hpre hX ht hag (k := a) hec
      (by simp only [Bar.loc, Bar.off]; congr 1; omega) hexit

end
end PTX.Kernels.Fp16Gemm8192.Proof
