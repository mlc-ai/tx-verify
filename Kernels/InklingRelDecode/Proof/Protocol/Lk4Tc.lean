-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk4Static
public import Kernels.InklingRelDecode.Proof.Interface.EpBw
public import Kernels.InklingRelDecode.Proof.Interface.Lk4Exit
public import Kernels.InklingRelDecode.Proof.Safety.Aligned

@[expose] public section

/-!
# `tcAligned` from the lockstep of the lanes

`Safety.Protocol.tcAligned` is `¬ AlignedClass.tc.Divergent` and `¬ AlignedClass.tc.Exited`:

* **Divergence.** Two lanes of a warp at their `k`-th warp-collective `tcgen05` events: the events
  are fired from states of the class (`isTcColl_state`), the lanes have made as many events of the
  class, so their states have one key (`class_key`), so one position; and the static parts of
  the events are those of the states (`tcStat_event`), which are equal for lanes of one warp at
  one key (`tcStat_lane`: the base word is 0 at every default-partition state, `tmz_inv`).
* **Exit.** A lane `f` that has exited with at most `k` events of the class, while another lane
  of its warp is at its `(k + 1)`-th: the other lane's state is at a synchronizing ordinal below the
  number of synchronizing states of `f` before its exit (`sy_lt_exit`), so `f` has a synchronizing
  state of that ordinal, which has the key of the other lane's, so is a state of the class, and
  `f` made its event.

The premises are the lockstep's: `LaneAgree` (the agreement at the synchronizing events, through
`lock_kernel`), and the facts of the threads' states (`ThreadFacts`, `BaseWordRead`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bar
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hb : BaseWordRead L X) (hA : LaneAgree Q L X)
include hpre hX hf

include hb hA

/-- **No two lanes of a warp diverge at a warp-collective `tcgen05` event**: the divergence half of
`Safety.Protocol.tcAligned`. -/
theorem tcDivergent_not : ¬ AlignedClass.tc.Divergent L kernel X := by
  rintro ⟨⟨g, i⟩, ⟨h, j⟩, pe, pf, ke, kf, hw, he, hf', hme, hmf, hord, -, hne⟩
  replace hw : SameWarp L g h := hw
  replace hord : ((X.tr g).take i).countP isTcColl = ((X.tr h).take j).countP isTcColl := hord
  have hS := hf.sound
  have ht := hf.tracked
  have hg : g < L.threads := hw.1.1
  have hh : h < L.threads := hw.1.2.1
  have hme' : isTcColl ⟨pe, ke⟩ = true := hme
  have hmf' : isTcColl ⟨pf, kf⟩ = true := hmf
  have hne1 : ∀ pc f', (⟨pe, ke⟩ : Event) ≠ ⟨pc, .ub f'⟩ := by
    rintro pc f' h'
    simp only [Event.mk.injEq] at h'
    rw [h'.2] at hme'
    simp [isTcColl] at hme'
  have hne2 : ∀ pc f', (⟨pf, kf⟩ : Event) ≠ ⟨pc, .ub f'⟩ := by
    rintro pc f' h'
    simp only [Event.mk.injEq] at h'
    rw [h'.2] at hmf'
    simp [isTcColl] at hmf'
  obtain ⟨s, hs⟩ := Frame.event_state hS hX ht he hne1
  obtain ⟨s', hs'⟩ := Frame.event_state hS hX ht hf' hne2
  have hs1 : St Q L X g i = some (some s) := hs
  have hs2 : St Q L X h j = some (some s') := hs'
  have hev : ClassEv isTcColl tcSt Q L X := fun {g k e s} hg he hσ =>
    isTcColl_state hpre hX hf hg he hσ
  have hcs : tcSt s = true := by rw [← isTcColl_state hpre hX hf hg he hs1]; exact hme'
  have hcs' : tcSt s' = true := by rw [← isTcColl_state hpre hX hf hh hf' hs2]; exact hmf'
  have hik : i ≤ (X.tr g).length := ev_le he
  have hjk : j ≤ (X.tr h).length := ev_le hf'
  have hkey := class_key (kernelSkel Q L) ht (lock_kernel ht hA) hev (fun hs => tcSt_sy hs)
    tcKey_class hw hik hjk hs1 hs2 hcs hcs' hord
  have h1 := (kernelSkel Q L).pc_key (g := g) (tcSt_sy hcs)
  have h2 := (kernelSkel Q L).pc_key (g := h) (tcSt_sy hcs')
  have hpc : TSt.pc s = TSt.pc s' := by rw [← h1, ← h2, hkey]
  have e1 := Frame.event_pc hS hX he hs
  have e2 := Frame.event_pc hS hX hf' hs'
  have hpe : pe = pf := by
    simp only at e1 e2
    rw [e1, e2]
    exact hpc
  rcases hne with hne | hne
  · exact hne hpe
  · obtain ⟨a, rfl⟩ := isTcColl_kind hme'
    obtain ⟨a', rfl⟩ := isTcColl_kind hmf'
    obtain ⟨p1, k1, he1, hst1⟩ := tcStat_event hpre hX hf hg he hs1 hcs
    obtain ⟨p2, k2, he2, hst2⟩ := tcStat_event hpre hX hf hh hf' hs2 hcs'
    simp only [Event.mk.injEq, Kind.tc.injEq] at he1 he2
    obtain ⟨-, rfl⟩ := he1
    obtain ⟨-, rfl⟩ := he2
    have hz := tmz_inv hpre hX hf hb hg i s hik hs1
    have hz' := tmz_inv hpre hX hf hb hh j s' hjk hs2
    have hl := tcStat_lane hw hcs hcs' hkey hz hz' (hf.reach hg hs1) (hf.reach hh hs2)
      (bwW_of hpre hX hf hg hs1) (bwW_of hpre hX hf hh hs2)
    apply hne
    simp only [AlignedClass.operands, Option.some.injEq, Kind.tc.injEq]
    rw [hst1, hst2]
    exact hl

omit hb in
/-- **No lane of a warp exits before another lane's warp-collective `tcgen05` event**: the exit
half of `Safety.Protocol.tcAligned`. -/
theorem tcExited_not : ¬ AlignedClass.tc.Exited L kernel X := by
  rintro ⟨⟨g, i⟩, ⟨h, j⟩, ev, hw, he, hm, -, hx⟩
  replace hw : SameWarp L g h := hw
  obtain ⟨⟨pcx, hfx⟩, hcnt⟩ := hx
  simp only [AlignedClass.exitMember, AlignedClass.member] at hm hcnt
  have hS := hf.sound
  have ht := hf.tracked
  have hg : g < L.threads := hw.1.1
  have hh : h < L.threads := hw.1.2.1
  have hne1 : ∀ pc f', ev ≠ ⟨pc, .ub f'⟩ := by
    rintro pc f' rfl
    simp [isTcColl] at hm
  obtain ⟨s, hs⟩ := Frame.event_state hS hX ht he hne1
  have hs1 : St Q L X g i = some (some s) := hs
  have hcs : tcSt s = true := by rw [← isTcColl_state hpre hX hf hg he hs1]; exact hm
  have hik : i ≤ (X.tr g).length := ev_le he
  have hjk : j ≤ (X.tr h).length := ev_le hfx
  have hsk := tcSt_sy hcs
  have hex : ∀ {g' h' : Nat} {s0 s' : TSt}, ExitState s0 → (kernelSkel Q L).sy s' →
      (kernelSkel Q L).key g' s0 ≠ (kernelSkel Q L).key h' s' := fun hx' hs' => exit_key_ne hx' hs'
  obtain ⟨sx, hsx, hxs⟩ : ∃ sx, St Q L X h j = some (some sx) ∧ ExitState sx := by
    rcases exit_event_state hX hS ht hfx with ⟨d, hσ, hd⟩ | ⟨x, hσ, hx⟩
    · exact ⟨_, hσ, hd⟩
    · exact ⟨_, hσ, hx⟩
  have hL := lock_kernel ht hA
  have hlt := sy_lt_exit (kernelSkel Q L) ht hL hA hex hw hik hjk hs1 hsk hsx hxs
  -- the exiting lane has a synchronizing state of the ordinal of the other lane's
  obtain ⟨b0, hb0, hsy0, hn0, -⟩ := exists_last (kernelSkel Q L) (X := X) h j
    (syN (kernelSkel Q L) X h j - 1) (by omega)
  obtain ⟨b, hbb, hsyb, hnb⟩ := exists_ordinal (kernelSkel Q L) (X := X) h
    (syN (kernelSkel Q L) X h j - 1 - syN (kernelSkel Q L) X g i) (a := b0)
    (n := syN (kernelSkel Q L) X g i) hsy0 (by omega)
  obtain ⟨sb, hsb, hsyb'⟩ := hsyb
  have hbl : b < (X.tr h).length := by
    have := (List.getElem?_eq_some_iff.mp hfx).1
    simp only at this
    omega
  obtain ⟨eb, heb⟩ : ∃ eb, (X.tr h)[b]? = some eb := ⟨_, List.getElem?_eq_getElem hbl⟩
  have hkey := hL _ hw hik (by omega) hs1 hsb hsk hsyb' rfl hnb
  have hcb : tcSt sb = true := by rw [← tcKey_class hw hsk hsyb' hkey]; exact hcs
  have hev : ClassEv isTcColl tcSt Q L X := fun {g k e s} hg he hσ =>
    isTcColl_state hpre hX hf hg he hσ
  have hebc : isTcColl eb = true := by
    rw [hev hh (show X.get (h, b) = some eb from heb) hsb]
    exact hcb
  have hc1 := lock_count (kernelSkel Q L) ht hL hev (fun hs => tcSt_sy hs) tcKey_class
    (syN (kernelSkel Q L) X g i) hw hik (by omega) hs1 hsb hsk hsyb' rfl hnb
  have hc2 := cnt_succ (X := X) isTcColl heb
  have hc3 := cnt_mono (X := X) isTcColl h (show b + 1 ≤ j by omega)
  have hc4 : cnt isTcColl X h j ≤ (X.tr h).countP isTcColl :=
    (List.take_sublist _ _).countP_le
  simp only [hebc, ↓reduceIte] at hc2
  have : cnt isTcColl X g i = ((X.tr g).take i).countP isTcColl := rfl
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.Bar
