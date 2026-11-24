-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.ExitCover
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Layout
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Blocker

@[expose] public section

/-! # An MMA completes before a CTA of its pair exits

An MMA of slot `s` is issued from the leader CTA of its pair. Once a CTA of the pair has exited,
the MMA thread has made its exit arrival (`ClusterExitAll`, `exit_arrival`), where its commits to
the slot's empty barrier are its full polls (`ThreadFacts.mma_exit_tasks`); at the MMA it had one
more full poll than commits (`ThreadFacts.mma_issue`). So it committed to the slot after the MMA,
and that commit tracks the MMA and notifies the slot's empty barrier in both CTAs of the pair
(`ThreadFacts.commit_ranks`). The notification completes the MMA first (`CommitOk`), and it
finished before an exit of the CTA (`CommitNotified`): so did the MMA (`mma_exit_commit`,
`mmaExitDone`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace InputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An event that commits to `m` is a commit whose mbarrier is `m`. -/
theorem commitsTo_form {m : Loc} {e : Event} (h : commitsTo m e = true) :
    ∃ sp, e.kind = .tc (.commit sp) ∧ sp.mbar = m := by
  obtain ⟨pc, k⟩ := e
  cases k with
  | tc op =>
    cases op with
    | commit sp => exact ⟨sp, rfl, by simpa [commitsTo] using h⟩
    | _ => simp [commitsTo] at h
  | _ => simp [commitsTo] at h

/-- **The commit after an MMA.** Once CTA `g / L.block + r` of the pair of an MMA `(g, k)` has
exited, a later commit of the MMA thread tracks the MMA, notified that CTA's barrier and finished
before an exit of it; the MMA has completed. -/
theorem mma_exit_commit (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hcn : CommitNotified L X) {g k pc dst : Nat}
    {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩) {r : Fin 16} (hr : r.val < 2)
    (hex : CtaExited L X (g / L.block + r.val)) :
    ∃ kc, TracksMma X (g, k) (g, kc) ∧
      SharedFinished L kernel Prod X (.async (g, kc) (.tcNotify r)) (g / L.block + r.val) ∧
      X.async.mmaDone (g, k) = true := by
  have hb := hpre.block
  have hgr := hpre.grid
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨m, s, j, rfl, hsite, heven, -, hcnt⟩ := ht.mma_issue hg he hσ rfl
  have hw := ht.role_warp hg (len_of_get he).le hσ
  simp only [roleWarp] at hw
  have hgc : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).mpr hg
  -- an exited thread of the CTA, and the MMA thread's exit arrival
  set g0 := (g / L.block + r.val) * L.block with hg0
  have hg0t : g0 < L.threads := by
    change _ < L.grid * L.block
    rw [hb] at heven hgc
    rw [hg0, hb, hgr]
    rw [hgr] at hgc
    omega
  have hg0c : g0 / L.block = g / L.block + r.val := by rw [hg0, hb]; omega
  obtain ⟨px, hlast⟩ := hex g0 hg0t hg0c
  have h2 := clusterExitAll hpre hX ht g0 px hg0t hlast g hg
    (by simp only [clusterOfCta_eq hpre]; omega)
  obtain ⟨ka, m', -, hσa, hsa, hka1, ea, hea, harr⟩ := exit_arrival hX ht hg hw.2 h2
  obtain ⟨-, -, -, hcm⟩ := ht.mma_exit_tasks hg hσa hsa
  -- the MMA is before the exit arrival
  have hkka : k < ka := by
    have hph := (ht.cluster hg he hσ).1
    simp only [ThreadD.clPhase, hsite] at hph
    by_contra hge
    have hne' : ka ≠ k := by
      rintro rfl
      rw [he] at hea
      obtain rfl := Option.some.inj hea
      simp [isClArrive] at harr
    have := ClusterTrace.countP_take_lt (xs := X.tr g) (p := isClArrive) (by omega : ka < k)
      hea harr
    change clArrives _ + 1 ≤ clArrives _ at this
    omega
  -- a commit to the slot follows the MMA before the exit arrival
  set em : Loc := ⟨.shared, g / L.block, L.sharedBase + 40 + 8 * s.val⟩ with hem
  set fm : Loc := ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩ with hfm
  have hmono : okPolls fm ((X.tr g).take k) ≤ okPolls fm ((X.tr g).take ka) :=
    ((List.take_prefix_take_left (l := X.tr g) hkka.le).sublist).countP_le
  obtain ⟨kc, ec, hec, hecm, hkc⟩ := MbarRing.Slot.exists_nth_countP (commitsTo em)
    (xs := (X.tr g).take ka) (c := ((X.tr g).take k).countP (commitsTo em))
    (by
      have h1 : ((X.tr g).take ka).countP (commitsTo em) = okPolls fm ((X.tr g).take ka) :=
        hcm s
      omega)
  have hkcka : kc < ka := by
    have := (List.getElem?_eq_some_iff.mp hec).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hkcka] at hec
  rw [List.take_take, Nat.min_eq_left hkcka.le] at hkc
  have hec' : X.get (g, kc) = some ec := hec
  have hkkc : k < kc := by
    by_contra hge
    have hne' : kc ≠ k := by
      rintro rfl
      rw [he] at hec'
      obtain rfl := Option.some.inj hec'
      simp [commitsTo] at hecm
    have := ClusterTrace.countP_take_lt (xs := X.tr g) (p := commitsTo em) (by omega : kc < k)
      hec hecm
    omega
  obtain ⟨csp, hck, hcmb⟩ := commitsTo_form hecm
  obtain ⟨dc, hσc⟩ := Frame.event_state ht.sound hX ht.tracked hec' (by rintro pc f rfl; cases hck)
  have hmb : csp.mbar = inputEmpty L (g / L.block) s := by
    rw [hcmb, ← emptyLoc_eq_inputEmpty]
    rfl
  have htarget := ht.commit_ranks s r hg hec' hσc hck hmb hr
  obtain ⟨pcc, kind⟩ := ec
  simp only at hck
  subst hck
  have hcommit : X.Commit (g, kc) csp := ⟨pcc, hec'⟩
  obtain ⟨hnot, hfin⟩ :=
    hcn (g, kc) csp r _ hcommit htarget (by simpa [inputEmpty, Bar.loc] using hex)
  have htrack : TracksMma X (g, k) (g, kc) :=
    ⟨rfl, hkkc, .inl ⟨dst, _, acc, mask, ⟨pc, he⟩⟩, csp, hcommit⟩
  exact ⟨kc, htrack, ⟨hnot, by simpa [inputEmpty, Bar.loc] using hfin⟩,
    (hX.tcCommit (g, kc) r hnot).2 (g, k) htrack⟩

/-- **The MMAs complete before the exits of their pairs.** -/
theorem mmaExitDone (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hcn : CommitNotified L X) : MmaExitDone L X := by
  intro ⟨g, k⟩ dst sp acc mask ⟨pc, he⟩ owner ho hex
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨m, s, j, rfl, -, heven, hsp, -⟩ := ht.mma_issue hg he hσ rfl
  obtain ⟨r, hr, rfl⟩ : ∃ r : Fin 16, r.val < 2 ∧ owner = g / L.block + r.val := by
    rw [hsp] at ho
    simp only [mmaSpec] at ho
    rcases ho with rfl | rfl
    · exact ⟨0, by decide, by simp only [Fin.val_zero]; omega⟩
    · exact ⟨1, by decide, by simp only [Fin.isValue, Fin.val_one]; omega⟩
  obtain ⟨kc, htrack, ⟨hnp, finish, pcx, hft, hfc, hfx, hchain⟩, hdone⟩ :=
    mma_exit_commit hpre hX ht hcn he hr hex
  have hnp' : X.AsyncPresent (g, kc) (.tcNotify r) := hnp
  exact ⟨hdone, finish, pcx, hft, hfc, hfx,
    CompletedBefore.of_stage hchain hnp' (.inr ⟨rfl, rfl, htrack, hdone, hnp'⟩)⟩

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
