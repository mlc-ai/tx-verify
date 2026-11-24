-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LkBar

@[expose] public section

/-!
# Warp lockstep: counts of events up to an ordinal, and the barrier-1 count

`lock_count` (`LkCount.lean`) asks for the lockstep at every ordinal. The agreement premise
`LaneAgree` only gives it up to the ordinal of the event it is asked at, so `lock_count_le` states
the same count equality from the lockstep at the smaller ordinals. `b1N_lock` is its use for the
barrier-1 events: two lanes of a warp at synchronizing states of one ordinal have made the same
number of barrier-1 events.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Lk (syPc)
open Classical

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {κ : Type}

/-- **The counts of a class at one ordinal, from the lockstep at the smaller ordinals.** -/
theorem lock_count_le (sk : Skel Q L κ) (ht : Frame.Tracked (code L Q) X)
    {c : Event → Bool} {Cs : TSt → Bool} (hev : ClassEv c Cs Q L X)
    (hsy : ∀ {s}, Cs s = true → sk.sy s)
    (hkey : ∀ {g h : Nat} {s s' : TSt}, SameWarp L g h → sk.sy s → sk.sy s' →
      sk.key g s = sk.key h s' → Cs s = Cs s') :
    ∀ n, (∀ m, m < n → Lock sk X m) → ∀ {g h a b : Nat} {s s' : TSt}, SameWarp L g h →
      a ≤ (X.tr g).length → b ≤ (X.tr h).length → St Q L X g a = some (some s) →
      St Q L X h b = some (some s') → sk.sy s → sk.sy s' → syN sk X g a = n → syN sk X h b = n →
      cnt c X g a = cnt c X h b := by
  intro n
  induction n with
  | zero =>
    intro _ g h a b s s' hw ha hb hs hs' hsy1 hsy2 hn hn'
    rw [cnt_zero sk ht hev hsy hw.1.1 hs ha
        (fun i hi => (no_sy_of_zero sk g hn) i (Nat.zero_le _) hi) a le_rfl,
      cnt_zero sk ht hev hsy hw.1.2.1 hs' hb
        (fun i hi => (no_sy_of_zero sk h hn') i (Nat.zero_le _) hi) b le_rfl]
  | succ n ih =>
    intro hL g h a b s s' hw ha hb hs hs' hsy1 hsy2 hn hn'
    have hg : g < L.threads := hw.1.1
    have hh : h < L.threads := hw.1.2.1
    obtain ⟨a', ha', hsa', hna', hno⟩ := exists_prev sk (X := X) g ⟨s, hs, hsy1⟩ hn
    obtain ⟨b', hb', hsb', hnb', hno'⟩ := exists_prev sk (X := X) h ⟨s', hs', hsy2⟩ hn'
    obtain ⟨sa, hsa, hsya⟩ := hsa'
    obtain ⟨sb, hsb, hsyb⟩ := hsb'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[a']? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨e', he'⟩ : ∃ e', (X.tr h)[b']? = some e' := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hih := ih (fun m hm => hL m (by omega)) hw (by omega) (by omega) hsa hsb hsya hsyb hna'
      hnb'
    have hk := hL n (by omega) hw (by omega) (by omega) hsa hsb hsya hsyb hna' hnb'
    have hcs := hkey hw hsya hsyb hk
    have h1 := cnt_stretch sk ht hev hsy hg hs ha (fun i h1 h2 => hno i h1 h2) a
      (by omega) le_rfl
    have h2 := cnt_stretch sk ht hev hsy hh hs' hb (fun i h1 h2 => hno' i h1 h2) b
      (by omega) le_rfl
    rw [h1, h2, cnt_succ c he, cnt_succ c he', hih, hev hg (show X.get (g, a') = some e from he)
      hsa, hev hh (show X.get (h, b') = some e' from he') hsb, hcs]

/-! ### The barrier-1 events -/

/-- The state's instruction is `barrier.sync 1`. -/
def bar1St (s : TSt) : Bool :=
  barSt s && decide ((match kernel.code[TSt.pc s]? with
    | some ins => (barIdCnt ins).1
    | none => 0) = 1)

theorem bar1St_class :
    ∀ {g h : Nat} {s s' : TSt}, SameWarp L g h → (kernelSkel Q L).sy s → (kernelSkel Q L).sy s' →
      (kernelSkel Q L).key g s = (kernelSkel Q L).key h s' → bar1St s = bar1St s' := by
  intro g h s s' hw hs hs' hk
  have h1 := (kernelSkel Q L).pc_key (g := g) hs
  have h2 := (kernelSkel Q L).pc_key (g := h) hs'
  have hpc : TSt.pc s = TSt.pc s' := by rw [← h1, ← h2, hk]
  simp only [bar1St, barSt, hpc]

theorem bar1St_sy {s : TSt} (h : bar1St s = true) : tSy s := by
  simp only [bar1St, Bool.and_eq_true] at h
  exact barSt_sy h.1

theorem isBar_form {a : Event} (h : Execution.isBar a = true) :
    ∃ pc id c m, a = ⟨pc, .bar id c m⟩ := by
  obtain ⟨pc, kd⟩ := a
  cases kd <;> simp [Execution.isBar] at h
  rename_i id c m
  exact ⟨pc, id, c, m, rfl⟩

/-- **A barrier-1 event is fired from a state that is `barrier.sync 1`, and only such an event.** -/
theorem bar1_classEv (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hb : L.block ≠ 128) :
    ClassEv (Execution.isBarId 1) bar1St Q L X := by
  intro g k e s hg he hσ
  have hbar := isBar_state hX hS hb he hσ
  have hpc := Frame.event_pc hS hX he hσ
  cases hq : barSt s
  · rw [hq] at hbar
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp_all [Execution.isBar, Execution.isBarId, bar1St]
  · rw [hq] at hbar
    obtain ⟨pc, id, cnt, m, rfl⟩ := isBar_form hbar
    obtain ⟨ins, hc, hic⟩ := bar_event_idcnt hX hb (i := (g, k)) he
    have hpc' : pc = TSt.pc s := hpc
    have hc' : kernel.code[TSt.pc s]? = some ins := by rw [← hpc']; exact hc
    have hid : id = (barIdCnt ins).1 := by
      have := congrArg Prod.fst hic
      exact this
    simp only [bar1St, hq, hc', Bool.true_and, Execution.isBarId, hid]
    by_cases h1 : (barIdCnt ins).1 = 1 <;> simp [h1]

/-- **Two lanes of a warp at synchronizing states of one ordinal have made the same number of
barrier-1 events**, from the lockstep of the keys at the smaller ordinals. -/
theorem b1N_lock (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X) :
    ∀ n, (∀ m, m < n → Lock (kernelSkel Q L) X m) → ∀ {g h a b : Nat} {s s' : TSt},
      SameWarp L g h → a ≤ (X.tr g).length → b ≤ (X.tr h).length →
      St Q L X g a = some (some s) → St Q L X h b = some (some s') → (kernelSkel Q L).sy s →
      (kernelSkel Q L).sy s' → syN (kernelSkel Q L) X g a = n → syN (kernelSkel Q L) X h b = n →
      ((X.tr g).take a).countP (Execution.isBarId 1) =
        ((X.tr h).take b).countP (Execution.isBarId 1) := by
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  exact lock_count_le (kernelSkel Q L) ht (bar1_classEv hX hS hb) (fun hs => bar1St_sy hs)
    bar1St_class

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
