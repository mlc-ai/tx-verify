-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Reuse
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.ExitCover

@[expose] public section

/-! # A slot's commits notified an exited CTA

A commit of an MMA thread to slot `s`'s empty barrier notifies the barrier in both CTAs of the
pair. Once a CTA of the pair has exited, so has its elected loader, which drained: its successful
polls of the slot's empty barrier are 32 per successful response poll plus one, its latest response
read claiming no CTA (`ThreadFacts.loader_exit_drain`). The MMA thread has made its exit arrival
(`ClusterExitAll`), before which lie all its commits, as many to the slot as 32 per successful
response poll (`ThreadFacts.mma_exit_tasks`); its earlier response reads claim
(`ThreadFacts.mma_exit_reads`). The responses agree (`AllResponsesAgree`), so the loader polled the
response at least as often. Its last poll of the slot then finds at least as many notifications of
the MMA thread as the thread's commits (`producer_poll`), each of a distinct commit
(`notification_commit`): one of them is the commit's (`exists_hit`). That notification is before
the poll in the barrier's history, and the poll before the loader's exit
(`slot_commit_notified`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace InputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Distinct entries that are as many as the positions hit every position.** A list without
repetitions whose entries name distinct positions below `K` of entries of `es` satisfying `p`, at
least as long as the count of such entries, names each of them. -/
theorem exists_hit {α β : Type} [DecidableEq α] (xs : List α) (hxs : xs.Nodup)
    (es : List β) (p : β → Bool) (K : Nat) (f : α → Nat)
    (hf : ∀ x ∈ xs, f x < K ∧ (es[f x]?).any p = true)
    (hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y)
    (hlen : (es.take K).countP p ≤ xs.length) {k : Nat} (hk : k < K)
    (hp : (es[k]?).any p = true) : ∃ x ∈ xs, f x = k := by
  classical
  by_contra hno
  push Not at hno
  rw [MbarRing.Slot.countP_take_card] at hlen
  set S := (Finset.range K).filter (fun j => (es[j]?).any p = true) with hS
  have hsub : xs.toFinset.image f ⊆ S.erase k := by
    intro j hj
    simp only [Finset.mem_image, List.mem_toFinset] at hj
    obtain ⟨x, hx, rfl⟩ := hj
    simp only [Finset.mem_erase, hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨hno x hx, (hf x hx).1, (hf x hx).2⟩
  have hcard : (xs.toFinset.image f).card = xs.length := by
    rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hxs]
    intro x hx y hy h
    exact hinj x (List.mem_toFinset.mp (Finset.mem_coe.mp hx)) y
      (List.mem_toFinset.mp (Finset.mem_coe.mp hy)) h
  have hkS : k ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨hk, hp⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hkS, hcard] at hle
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨k, hkS⟩
  omega

/-- **The elected loader of an exited CTA.** A CTA that has exited has a warp-11 lane elected by
its warp. -/
theorem elected_loader (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {T : Nat} (hT : T < L.grid) (hex : CtaExited L X T) :
    ∃ gl jl pcl maskl instl, gl < L.threads ∧ gl / L.block = T ∧ gl % L.block / 32 = 11 ∧
      X.Elect (gl, jl) pcl maskl instl (laneOf L gl) := by
  have hb := hpre.block
  set h0 := T * L.block + 352 with hh0
  have hh0t : h0 < L.threads := by
    change _ < L.grid * L.block
    rw [hh0, hb]
    omega
  have hh0c : h0 / L.block = T := by rw [hh0, hb]; omega
  have hh0w : h0 % L.block / 32 = 11 := by rw [hh0, hb]; omega
  by_cases hel : ∃ j pc mask inst leader, X.Elect (h0, j) pc mask inst leader
  · obtain ⟨j, pc, mask, inst, leader, hE⟩ := hel
    obtain ⟨M, jM, hM, ⟨⟨-, -, hcta⟩, hwarp⟩, hE'⟩ := elected_of_elect hpre hX hE
    exact ⟨M, jM, pc, mask, inst, hM, by omega, by omega, hE'⟩
  · exfalso
    obtain ⟨d, hσ, -⟩ := ht.loader_unelected hh0t hh0w
      (fun j pc mask inst leader h => hel ⟨j, pc, mask, inst, leader, h⟩)
    obtain ⟨px, hlast⟩ := hex h0 hh0t hh0c
    rw [ht.exited_state hh0t hlast] at hσ
    cases hσ

/-- **Every commit of an MMA thread precedes its exit arrival.** A commit fires at a commit site,
before both cluster arrivals; the exit arrival is the second. -/
theorem commit_before_arrival (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {M ka : Nat} (hM : M < L.threads)
    {ea : Event} (hea : X.get (M, ka) = some ea) (harr : isClArrive ea = true)
    (hka1 : clArrives ((X.tr M).take ka) = 1) {jc pcj : Nat} {spj : TcCommit.Spec}
    (hj : X.get (M, jc) = some ⟨pcj, .tc (.commit spj)⟩) : jc < ka := by
  obtain ⟨dj, hσj⟩ := Frame.event_state ht.sound hX ht.tracked hj (by simp)
  obtain ⟨mj, rfl, -, hsite⟩ := ht.commit_spec hM hj hσj rfl
  have hph := (ht.cluster hM hj hσj).1
  have h1 : clArrives ((X.tr M).take jc) = 1 := by
    rw [hph]
    rcases hsite with ⟨s', hs', -⟩ | ⟨hs', -⟩ <;> simp [ThreadD.clPhase, hs']
  by_contra hge
  have hne : ka ≠ jc := by
    rintro rfl
    rw [hj] at hea
    obtain rfl := Option.some.inj hea
    simp [isClArrive] at harr
  have := ClusterTrace.countP_take_lt (xs := X.tr M) (p := isClArrive) (by omega : ka < jc)
    hea harr
  change clArrives _ + 1 ≤ clArrives _ at this
  omega

/-- **A successful poll of an exited thread precedes its exit in the dependency order.** The
poll is a canonical spin, so its return resumes every later event of its thread, the exit
included. -/
theorem before_exit (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {g j pc pcw q : Nat} {m : Loc} {acq : Bool}
    {sc : MbarScope} (hlast : (X.tr g).getLast? = some ⟨pc, .exit⟩)
    (hj : X.get (g, j) = some ⟨pcw, .wait m q true acq sc⟩) :
    Relation.TransGen (DepStep L kernel X) (.thread (g, j), true)
      (.thread (g, (X.tr g).length - 1), false) := by
  have hjl : j < (X.tr g).length := len_of_get hj
  have hx := exit_get hlast
  have hne' : j ≠ (X.tr g).length - 1 := by
    rintro rfl
    rw [hx] at hj
    cases hj
  obtain ⟨ex, hspin⟩ := ht.wait_spins (Frame.lt_of_get hX hj) hj
  exact .single (DepStep.of_resumes L
    (Resumes.of_spin hj hspin rfl (by simp only; omega) (by simp only; omega)))

/-- **A slot's commit notified an exited CTA of the pair.** -/
theorem slot_commit_notified (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hag : AllResponsesAgree L X) {M kc pcc : Nat}
    {csp : TcCommit.Spec} {s : Fin 4} {a : Fin 2}
    (hec : X.get (M, kc) = some ⟨pcc, .tc (.commit csp)⟩)
    (hmb : csp.mbar = inputEmpty L (M / L.block) s)
    (hex : CtaExited L X (M / L.block + a.val)) :
    SharedFinished L kernel Prod X (.async (M, kc) (.tcNotify ⟨a.val, by omega⟩))
      (M / L.block + a.val) := by
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
  have hMg : M / L.block < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).mpr hM
  have hTg : M / L.block + a.val < L.grid := by
    have := a.isLt
    rw [hgr] at hMg ⊢
    omega
  -- the drained loader of the exited CTA
  obtain ⟨gl, jl, pcl, maskl, instl, hgl, hglc, hglw, hglE⟩ := elected_loader hpre hX ht hTg hex
  obtain ⟨pxl, hlastl⟩ := hex gl hgl hglc
  obtain ⟨hRpos, hpolls, jlr, pclr, plr, acqlr, sclr, pcrl, srcl, bsl, rrl, hwlr, hrlr, hsfl,
    hrespl, hncl, hcntl⟩ := ht.loader_exit_drain hgl hglw ⟨jl, pcl, maskl, instl, hglE⟩ hlastl
  -- the MMA thread's exit arrival
  have h2 := clusterExitAll hpre hX ht gl pxl hgl hlastl M hM
    (by simp only [clusterOfCta_eq hpre]; omega)
  obtain ⟨ka, m', hkal, hσa, hsa, hka1, ea, hea, harr⟩ := exit_arrival hX ht hM hwM.2 h2
  obtain ⟨hfullM, hclaimless, -, hcm⟩ := ht.mma_exit_tasks hM hσa hsa
  obtain ⟨-, hcb⟩ := ht.mma_exit_reads hM hkal.le hσa hsa
  set Rl := okPolls (Bar.loc L (gl / L.block) ⟨.clc, 0, true⟩) (X.tr gl) with hRl
  set RM := okPolls (Bar.loc L (M / L.block) ⟨.clc, 0, true⟩) ((X.tr M).take ka) with hRM
  -- the loader polled the response at least as often
  have hle : RM ≤ Rl := by
    by_contra hlt
    push Not at hlt
    obtain ⟨jm, pcm, pm, acqm, scm, hjm, hwm, hcm'⟩ := MbarRing.Poll.exists_nth (X := X) (g := M)
      (k := ka) (m := Bar.loc L (M / L.block) ⟨.clc, 0, true⟩) (n := Rl - 1) (by omega)
    obtain ⟨pcr, a', bs', rr', hrd, hsf, hresp, hcl⟩ := hcb jm pcm pm acqm scm hwm (by omega)
    have hbs := hag c gl M jlr jm pclr pcm plr pm pcrl pcr acqlr acqm sclr scm srcl a' bsl bs'
      (by omega) rfl hwlr hwm (by omega) hrlr hsfl hrd hsf
    rw [hbs, hresp] at hrespl
    obtain rfl := Option.some.inj hrespl
    exact hncl hcl
  -- the loader's last poll of the slot's empty barrier
  set E := (slot L c s).empty a with hE
  have hEl : emptyLoc L (gl / L.block) s = E := by
    rw [hE, emptyLoc_bar, hglc, hMc]
    rfl
  have hlast := hpolls s
  rw [hEl] at hlast
  obtain ⟨jw, pcw, pw, acqw, scw, hjw, hww, hcw⟩ := MbarRing.Poll.exists_nth (X := X)
    (g := gl) (k := (X.tr gl).length) (m := E) (n := 32 * Rl) (by rw [List.take_length]; omega)
  have hprod : producerThread L c a gl = true := by
    simp only [producerThread, decide_eq_true_eq]
    exact ⟨by omega, hglw⟩
  have hpos : 0 < 32 * Rl := by omega
  obtain ⟨jr, w, hjr, hwid, -, -, -, hnot⟩ := producer_poll hpre hX ht hprod hww
    (q := 32 * Rl - 1) (by rw [hcw]; omega)
  -- the MMA thread is the slot's MMA thread of its warp
  set b : Fin 2 := ⟨M % L.block / 32 - 8, by omega⟩ with hbdef
  have hcons : consumerThread L c b M = true := by
    simp only [consumerThread, decide_eq_true_eq, hbdef]
    omega
  have hE0 : (⟨.shared, M / L.block, L.sharedBase + 40 + 8 * s.val⟩ : Loc) =
      (slot L c s).empty 0 := by
    rw [hMc]
    exact emptyLoc_bar L (2 * c) s
  have hF0 : (⟨.shared, M / L.block, L.sharedBase + 8 + 8 * s.val⟩ : Loc) =
      (slot L c s).full 0 := by
    rw [hMc]
    exact fullLoc_bar L c s
  have hcommits := hcm s
  rw [hfullM s, hE0] at hcommits
  have hkc : kc < ka := commit_before_arrival hX ht hM hea harr hka1 hec
  have hIE : inputEmpty L (M / L.block) s = (slot L c s).empty 0 := by
    rw [← hE0]
    exact (emptyLoc_bar L (M / L.block) s).symm
  have hcmb : commitsTo ((slot L c s).empty 0) ⟨pcc, .tc (.commit csp)⟩ = true := by
    simp [commitsTo, hmb, hIE]
  have hpoll : ∃ jf pcf pf acqf scf, X.get (M, jf) =
      some ⟨pcf, .wait ((slot L c s).full 0) pf true acqf scf⟩ := by
    have hk1 : ((X.tr M).take kc).countP (commitsTo ((slot L c s).empty 0)) + 1 ≤
        ((X.tr M).take ka).countP (commitsTo ((slot L c s).empty 0)) :=
      ClusterTrace.countP_take_lt (xs := X.tr M) hkc hec hcmb
    obtain ⟨jf, pcf, pf, acqf, scf, -, hf, -⟩ := MbarRing.Poll.exists_nth (X := X) (g := M)
      (k := ka) (m := (slot L c s).full 0) (n := 0)
      (by have hcs := hcm s; rw [hE0, hF0] at hcs; omega)
    exact ⟨jf, pcf, pf, acqf, scf, hf⟩
  obtain ⟨jf, pcf, pf, acqf, scf, hf⟩ := hpoll
  have hMeq := consumerOf_eq hX ht hcons hf
  -- the notifications before the loader's poll name every commit; one names this commit
  let f : Record Ref → Nat := fun x => match x.id with
    | .async i _ => i.2
    | _ => 0
  set xs := ((X.objects E).take jr).filter ((slot L c s).notification a b) with hxs
  have hnd : (X.objects E).Nodup := List.Nodup.of_map _ (hX.tma.2.2.1 E).1.1
  have hxsnd : xs.Nodup := (hnd.sublist (List.take_sublist _ _)).filter _
  have hcommit_of : ∀ x ∈ xs, ∃ jc pcx sp, x.id = .async (M, jc) (.tcNotify ⟨a.val, by omega⟩) ∧
      X.get (M, jc) = some ⟨pcx, .tc (.commit sp)⟩ ∧ sp.mbar = (slot L c s).empty 0 ∧
      x ∈ X.objects E := by
    intro x hx
    obtain ⟨hxt, hxn⟩ := List.mem_filter.mp hx
    obtain ⟨jc, pcx, sp, hid, hcx, hmbx, -⟩ :=
      notification_commit hX ht (List.mem_of_mem_take hxt) hxn
    rw [← hMeq] at hid hcx
    exact ⟨jc, pcx, sp, hid, hcx, hmbx, List.mem_of_mem_take hxt⟩
  obtain ⟨x, hx, hfx⟩ := exists_hit xs hxsnd (X.tr M) (commitsTo ((slot L c s).empty 0)) ka f
    (fun x hx => by
      obtain ⟨jc, pcx, sp, hid, hcx, hmbx, -⟩ := hcommit_of x hx
      have hfx : f x = jc := by simp only [f, hid]
      rw [hfx]
      refine ⟨commit_before_arrival hX ht hM hea harr hka1 hcx, ?_⟩
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
      rw [hcommits, hxs, ← List.countP_eq_length_filter]
      have := hnot b
      rw [← hE] at this
      omega)
    hkc (by change (X.get (M, kc)).any _ = true; rw [hec]; exact hcmb)
  obtain ⟨jc, pcx, sp, hid, -, -, hxm⟩ := hcommit_of x hx
  have hfx' : f x = jc := by simp only [f, hid]
  rw [hfx'] at hfx
  subst hfx
  -- the notification is present, and before the poll in the barrier's history
  have hobj : objectAction X X.async E (.async (M, jc) (.tcNotify ⟨a.val, by omega⟩)) =
      some x.action := by
    have h := ((hX.tma.2.2.1 _).2.1 x hxm).1
    rw [hid] at h
    exact h
  obtain ⟨-, -, -, -, hnotif⟩ := PairTmaRing.tcNotify_facts hobj
  obtain ⟨hxt, -⟩ := List.mem_filter.mp hx
  obtain ⟨ix, hix⟩ := List.getElem?_of_mem hxt
  have hixl : ix < jr := by
    have := (List.getElem?_eq_some_iff.mp hix).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hixl] at hix
  have hbefore : MBarrier.Before (X.objects E) (.async (M, jc) (.tcNotify ⟨a.val, by omega⟩))
      (.thread (gl, jw)) := ⟨ix, jr, x, w, hix, hid, hjr, hwid, hixl⟩
  refine ⟨hnotif, (gl, (X.tr gl).length - 1), pxl, hgl, hglc, exit_get hlastl, ?_⟩
  exact CompletedBefore.of_before hbefore (before_exit hX ht hlastl hww)

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
