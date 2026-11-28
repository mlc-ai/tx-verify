-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Mbar
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Coll
public import Lemmas.Protocol.CountNth
public import Lemmas.Kernel.CountClosed
public import Lemmas.Kernel.Safety.Handoff
public import Lemmas.Kernel.UbLast

@[expose] public section

/-! # The startup's side of the mbarrier channel: initialization before barrier 0

From the startup's export rows only (`Startup/Export/{Mbar,Coll}.lean`), over a launched thread
`g` of a consistent, followed execution and its events before its first barrier-0 event:

* `init_once`: the thread initializes an object at most once (the order `MbarFam.ofInit` is
  injective and the thread's initialization count rises at each);
* `won_inits`: a thread that won the election at pc 31 and passes barrier 0 initializes every one
  of the 23 objects of its CTA, with the object's count, before its barrier-0 event;
* `use_after_bar0`: an event that names an mbarrier and is no initialization follows a
  barrier-0 event of its thread.

What `noUninit.whole` still needs beyond these (see the report of lane A): (N1) every other role's
Mbar row: no initialization after barrier 0; (N2) the shuffle row: only warp 0 of a CTA reaches
the elections (the warp word lane 0 sends), so by `elect_leader` one thread of the CTA
initializes; (N3) the CTA barrier's publication (`Frame.Handoff.of_bar`): barrier 0's sources are
the 384 threads of the CTA by `bar.sync`, so an initialization before the initializer's barrier
is published to every event after the user's barrier. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The prefix count before a later position is at least the count before an earlier one plus
the earlier event's. -/
private theorem count_lt {p : Event → Bool} {i k : Nat} {e : Event} (he : X.get (g, i) = some e)
    (hp : p e = true) (hik : i < k) :
    ((X.tr g).take i).countP p + 1 ≤ ((X.tr g).take k).countP p := by
  have h := Frame.Handoff.countP_take_succ_ge (es := X.tr g) (e := k - 1) he hp (by omega)
  rwa [show k - 1 + 1 = k by omega] at h

private theorem count_mono {p : Event → Bool} {i k : Nat} (hik : i ≤ k) :
    ((X.tr g).take i).countP p ≤ ((X.tr g).take k).countP p :=
  (List.take_sublist_take_left (l := X.tr g) hik).countP_le

/-- The object's offset names the family. -/
private theorem loc_inj {c : Nat} {f f' : MbarFam} (h : mbarLoc L c f = mbarLoc L c f') :
    f = f' := by
  simp only [mbarLoc, Loc.mk.injEq, true_and] at h
  exact MbarFam.off_inj (by omega)

/-- **The startup initializes an object at most once per thread.** -/
theorem init_once (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i k pci pck : Nat} {l : Loc} {ci ck : Nat}
    (hi : X.get (g, i) = some ⟨pci, .mbInit l ci⟩) (hk : X.get (g, k) = some ⟨pck, .mbInit l ck⟩)
    (h0i : ((X.tr g).take i).countP isBar0 = 0) (h0k : ((X.tr g).take k).countP isBar0 = 0) :
    i = k := by
  obtain ⟨j1, hl1, -, hc1⟩ := startup_mbInit hp hX hFw hi rfl h0i
  obtain ⟨j2, hl2, -, hc2⟩ := startup_mbInit hp hX hFw hk rfl h0k
  have hf := loc_inj (hl1.symm.trans hl2)
  obtain ⟨j, -, huniq⟩ := MbarFam.ofInit_bij (MbarFam.ofInit j1)
  have hj : j1 = j2 := (huniq j1 rfl).trans (huniq j2 hf.symm).symm
  subst hj
  rcases Nat.lt_trichotomy i k with h | h | h
  · have := count_lt (p := isMbInit) hi rfl h
    omega
  · exact h
  · have := count_lt (p := isMbInit) hk rfl h
    omega

/-- **A thread that won the election at pc 31 initializes every object of its CTA before its
barrier-0 event.** -/
theorem won_inits (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {j kb pcj pcb mk inst : Nat} {cnt : Option Nat} {mode : BarMode}
    (hj : X.get (g, j) = some ⟨pcj, .elect mk inst (PTX.laneOf L g)⟩) (hpc : pcj = 31)
    (hb : X.get (g, kb) = some ⟨pcb, .bar 0 cnt mode⟩)
    (h0j : ((X.tr g).take j).countP isBar0 = 0) (h0 : ((X.tr g).take kb).countP isBar0 = 0)
    (f : MbarFam) :
    ∃ i < kb, ∃ pc, X.get (g, i) = some ⟨pc, .mbInit (mbarLoc L (g / L.block) f) f.count⟩ := by
  -- the election is before the barrier
  have hjb : j < kb := by
    rcases Nat.lt_or_ge j kb with h | h
    · exact h
    · rcases Nat.eq_or_lt_of_le h with h | h
      · subst h; rw [hb] at hj; cases hj
      · have := count_lt (p := isBar0) hb rfl h
        omega
  -- the event after the election is an initialization, so the barrier's count is 23
  have hlen : j + 1 < (X.tr g).length := by
    have hb' : (X.tr g)[kb]? = some ⟨pcb, .bar 0 cnt mode⟩ := hb
    have := (List.getElem?_eq_some_iff.mp hb').1
    omega
  obtain ⟨e', he'⟩ : ∃ e', X.get (g, j + 1) = some e' :=
    ⟨_, List.getElem?_eq_getElem hlen⟩
  have h23 : ((X.tr g).take kb).countP isMbInit = 23 := by
    rcases startup_won hp hX hFw hj rfl hpc h0j he' with hk' | ⟨fl, hk'⟩
    · obtain ⟨-, -, hn⟩ := startup_bar0 hp hX hFw hb rfl h0
      rcases Nat.eq_or_lt_of_le (show j + 1 ≤ kb by omega) with h | h
      · subst h; rw [hb] at he'; cases he'; cases hk'
      · have := count_lt (p := isMbInit) he' (by simp [isMbInit, hk']) h
        omega
    · obtain ⟨pc', kd⟩ := e'
      simp only at hk'
      subst hk'
      have := ub_last hX he' hb
      have hk : kb = j + 1 := by omega
      subst hk
      rw [hb] at he'
      cases he'
  -- the initialization of `f` is the one with its index in the order
  obtain ⟨jf, hjf, -⟩ := MbarFam.ofInit_bij f
  obtain ⟨i, ev, hiev, hpi, hci⟩ := MbarRing.Slot.exists_nth_countP isMbInit
    (xs := (X.tr g).take kb) (c := jf.val) (by omega)
  have hikb : i < kb := by
    have := (List.getElem?_eq_some_iff.mp hiev).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hikb.le] at hci
  have hget : X.get (g, i) = some ev := by
    change (X.tr g)[i]? = some ev
    rw [← hiev, List.getElem?_take_of_lt hikb]
  obtain ⟨pc, kd⟩ := ev
  cases kd <;> simp [isMbInit] at hpi
  rename_i l c
  have h0i : ((X.tr g).take i).countP isBar0 = 0 :=
    Nat.eq_zero_of_le_zero (h0 ▸ count_mono hikb.le)
  obtain ⟨j', hl, hc, hcount⟩ := startup_mbInit hp hX hFw hget rfl h0i
  have : j' = jf := Fin.ext (hcount.symm.trans hci)
  subst this
  subst hjf
  exact ⟨i, hikb, pc, by rw [hget, hl, hc]⟩

/-- **A use of an mbarrier follows its thread's barrier-0 event.** -/
theorem use_after_bar0 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} {e : Event} {l : Loc} (he : X.get (g, k) = some e)
    (hm : Frame.MbarOf e l) (hni : ∀ c, e.kind ≠ .mbInit l c) :
    0 < ((X.tr g).take k).countP isBar0 := by
  rcases Nat.eq_zero_or_pos (((X.tr g).take k).countP isBar0) with h | h
  · obtain ⟨c, hc⟩ := startup_mbarOf hp hX hFw he hm h
    exact absurd hc (hni c)
  · exact h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
