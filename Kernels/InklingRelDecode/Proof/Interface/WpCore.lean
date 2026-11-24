-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk3Event
public import Kernels.InklingRelDecode.Proof.Interface.Lk4Exit
public import Kernels.InklingRelDecode.Proof.Interface.RsElect
public import Lemmas.Flow.PollRendezvous
public import Lemmas.Flow.NthEv

@[expose] public section

/-!
# Two lanes' polls met through a warp collective

Two lanes `g` and `h` of a warp poll at events `k` and `k'`. If `g` has made at most `n` shuffles
before its poll and `h` more than `n` before its own, then `h` made its shuffle of ordinal `n`
before its poll. That shuffle has returned, so `g` has the shuffle of the same ordinal, or `g`
exited before it (`Step.shfl_lane_of_ready`, DEP-WARP-INSTANCE). `g` does not exit before it: by
the lockstep of the warp (`Interface.Lk.lock_kernel`), a lane at a shuffle state has made fewer
shuffles than a lane of its warp at its exit (`shfl_lt_exit`, the argument of
`Progress.Lk4.wc_lt_exit` for the class of shuffles). So `g` makes the shuffle after its poll,
and its issue precedes the return of `h`'s, which precedes `h`'s poll in the execution-dependency
order (`coll_depBefore`): the poll of `g` is ordered before that of `h` (`PollBefore`,
`meet_shfl`). The same holds for elections (`meet_elect`): every election of the kernel has the
full mask (`elect_full`), so `h`'s election has a partner in `g` (`ElectOrd.partner`) of the same
ordinal (`electOrdinal`), with no exit case.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Interface.Lk

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The elections of one instance in a warp have one ordinal, in every consistent execution of
the kernel (all its elections have the full mask). -/
theorem electOrd (hX : Consistent L kernel asms mem0 X) : ElectOrdinal L X :=
  electOrdinal hX (ElectMutual.of_full fun he => elect_full hX he)

/-- **A lane at a shuffle state has made fewer shuffles than a lane of its warp at its exit.** -/
theorem shfl_lt_exit (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hA : LaneAgree Q L X) {g h a j pc : Nat} {s : TSt} (hw : SameWarp L g h)
    (ha : a ≤ (X.tr g).length) (hs : St Q L X g a = some (some s)) (hc : shflSt s = true)
    (hx : X.get (h, j) = some ⟨pc, .exit⟩) :
    cnt Execution.isShfl X g a < cnt Execution.isShfl X h j := by
  have ht := hf.tracked
  have hh : h < L.threads := hw.1.2.1
  have hev : ClassEv Execution.isShfl shflSt Q L X := isShfl_state hX hf
  have hjl : j < (X.tr h).length := (List.getElem?_eq_some_iff.mp hx).1
  have hsk := shflSt_sy hc
  obtain ⟨sx, hsx, hxs⟩ : ∃ sx, St Q L X h j = some (some sx) ∧ ExitState sx := by
    rcases exit_event_state hX hf.sound hf.tracked hx with ⟨d, hσ, hd⟩ | ⟨x, hσ, hx'⟩
    · exact ⟨_, hσ, hd⟩
    · exact ⟨_, hσ, hx'⟩
  have hL := lock_kernel ht hA
  have hlt := sy_lt_exit (kernelSkel Q L) ht hL hA (fun hx' hs' => exit_key_ne hx' hs') hw ha
    (by omega) hs hsk hsx hxs
  obtain ⟨b0, hb0, hsy0, hn0, -⟩ := exists_last (kernelSkel Q L) (X := X) h j
    (syN (kernelSkel Q L) X h j - 1) (by omega)
  obtain ⟨b, hbb, hsyb, hnb⟩ := exists_ordinal (kernelSkel Q L) (X := X) h
    (syN (kernelSkel Q L) X h j - 1 - syN (kernelSkel Q L) X g a) (a := b0)
    (n := syN (kernelSkel Q L) X g a) hsy0 (by omega)
  obtain ⟨sb, hsb, hsyb'⟩ := hsyb
  obtain ⟨eb, heb⟩ : ∃ eb, (X.tr h)[b]? = some eb := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hkey := hL _ hw ha (by omega) hs hsb hsk hsyb' rfl hnb
  have hcb : shflSt sb = true := by rw [← shflKey_class hw hsk hsyb' hkey]; exact hc
  have hebc : Execution.isShfl eb = true := by
    rw [hev hh (show X.get (h, b) = some eb from heb) hsb]
    exact hcb
  have hc1 := lock_count (kernelSkel Q L) ht hL hev (fun hs => shflSt_sy hs) shflKey_class
    (syN (kernelSkel Q L) X g a) hw ha (by omega) hs hsb hsk hsyb' rfl hnb
  have hc2 := cnt_succ (X := X) Execution.isShfl heb
  have hc3 := cnt_mono (X := X) Execution.isShfl h (show b + 1 ≤ j by omega)
  simp only [hebc, ↓reduceIte] at hc2
  omega

/-- **Polls met through a shuffle.** Lane `g` has made at most `n` shuffles before its event `k`,
which is no shuffle, and lane `h` of its warp more than `n` before its event `k'`: an event of `g`
after `k` precedes `(h, k')` in the execution-dependency order. -/
theorem meet_shfl (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hA : LaneAgree Q L X) {g h k k' n : Nat} {e : Event} (hw : SameWarp L g h)
    (he : X.get (g, k) = some e) (hne : Execution.isShfl e = false)
    (hg : cnt Execution.isShfl X g k ≤ n) (hh : n < cnt Execution.isShfl X h k')
    (hk' : k' < (X.tr h).length) : PollBefore L kernel X (g, k) (h, k') := by
  obtain ⟨b, eb, hb, hgetb, hpb, hcb⟩ := exists_nthEv (X := X) (p := Execution.isShfl) (g := h)
    (k := k') (n := n) (by unfold cnt at hh; omega)
  have hKb : X.ShflK (h, b) n := by
    obtain ⟨pc, kd⟩ := eb
    cases kd <;> simp [Execution.isShfl] at hpb
    exact ⟨⟨_, _, _, _, _, _, _, hgetb⟩, hcb⟩
  obtain ⟨pcb, mb, ab, bb, cb, rb, ob, hgb⟩ := hKb.1
  rcases Step.shfl_lane_of_ready hX hgb hKb (sameWarp_symm hw) with ⟨j, hKj⟩ | ⟨x, pcx, hex, hcx⟩
  · obtain ⟨⟨pcj, mj, aj, bj, cj, rj, oj, hgj⟩, hcj⟩ := id hKj
    have hjk : k < j := by
      by_contra hjk
      rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hjk) with h1 | h1
      · have h2 := countP_take_succ (p := Execution.isShfl) hgj rfl
        have h3 := countP_take_mono Execution.isShfl (X.tr g) (show j + 1 ≤ k by omega)
        simp only at hcj
        unfold cnt at hg
        omega
      · subst h1
        rw [he] at hgj
        cases hgj
        simp [Execution.isShfl] at hne
    exact ⟨j, hjk, coll_depBefore (c := (false, n)) hX (electOrd hX) hw hKj hKb hb hk'⟩
  · exfalso
    have hhg : h < L.threads := hw.1.2.1
    obtain ⟨sb, hsb⟩ := Frame.event_state hf.sound hX hf.tracked hgb (by intro pc f h; cases h)
    have hcb' : shflSt sb = true := by
      rw [← isShfl_state hX hf hhg hgb hsb]
      rfl
    have := shfl_lt_exit hX hf hA (sameWarp_symm hw)
      (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hgb).1) hsb hcb' hex
    unfold cnt at this
    rw [hcb] at this
    omega

/-- **Polls met through an election.** Lane `g` has made at most `n` elections before its event
`k`, which is no election, and lane `h` of its warp more than `n` before its event `k'`: an event
of `g` after `k` precedes `(h, k')` in the execution-dependency order. -/
theorem meet_elect (hX : Consistent L kernel asms mem0 X) {g h k k' n : Nat} {e : Event}
    (hw : SameWarp L g h) (he : X.get (g, k) = some e) (hne : isElectEv e = false)
    (hg : elections X g k ≤ n) (hh : n < elections X h k') (hk' : k' < (X.tr h).length) :
    PollBefore L kernel X (g, k) (h, k') := by
  obtain ⟨b, eb, hb, hgetb, hpb, hcb⟩ := exists_nthEv (X := X) (p := isElectEv) (g := h)
    (k := k') (n := n) (by unfold elections at hh; omega)
  obtain ⟨pcb, mask, inst, l, hEb⟩ : ∃ pc mask inst l, X.Elect (h, b) pc mask inst l := by
    obtain ⟨pc, kd⟩ := eb
    cases kd <;> simp [isElectEv] at hpb
    exact ⟨_, _, _, _, hgetb⟩
  have hmf : mask = 4294967295 := elect_full hX hEb
  subst hmf
  have hm : electMember 4294967295 (laneOf L g) := by
    have hl : laneOf L g < 32 := Nat.mod_lt _ (by decide)
    revert hl
    generalize laneOf L g = lane
    revert lane
    decide
  obtain ⟨j, pc1, pc2, m1, m2, i1, l1, l2, hy, hj⟩ := ElectOrd.partner hX (sameWarp_symm hw) hEb hm
  have hm2 : m2 = 4294967295 := elect_full hX hj
  subst hm2
  have hord := electOrd hX (e := (h, b)) (f := (g, j)) (sameWarp_symm hw) hy hj
  have hcj : elections X g j = n := by
    have : elections X h b = n := hcb
    unfold elections at this ⊢
    simp only at hord
    omega
  have hjk : k < j := by
    by_contra hjk
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hjk) with h1 | h1
    · have h2 := ElectOrd.elections_succ hj
      have h3 := countP_take_mono isElectEv (X.tr g) (show j + 1 ≤ k by omega)
      unfold elections at h2 hcj hg
      omega
    · subst h1
      have hj' : X.get (g, j) = some ⟨pc2, .elect 4294967295 i1 l2⟩ := hj
      rw [he] at hj'
      cases hj'
      simp [isElectEv] at hne
  exact ⟨j, hjk, coll_depBefore (c := (true, n)) hX (electOrd hX) hw ⟨⟨_, _, _, hj⟩, hcj⟩
    ⟨⟨_, _, _, hEb⟩, hcb⟩ hb hk'⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Wp
