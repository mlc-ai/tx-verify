-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Lk4Warp
public import Kernels.InklingRelDecode.Proof.Interface.Lk4Exit

@[expose] public section

/-!
# `WarpCollFacts.exit` from the lockstep of the lanes

`WarpCollFacts.exit` asks for a number `N` of the warp: a lane at a warp collective has made fewer
warp collectives than `N`, and a lane that exits has made at least `N`. The lanes of a warp that
exit have made one number of warp collectives (`wc_exit_eq`), and every lane of the warp at a
warp-collective state has made fewer (`wc_lt_exit`):

* the number of synchronizing states before an exit is one number for the exiting lanes of a warp:
  a lane with more of them has a synchronizing state of the ordinal that the other's exit would
  have to exceed (`sy_lt_exit`);
* the lanes' last synchronizing states before their exits have one key, so one class, and the
  warp-collective events the lanes made are those of the synchronizing states before (`cnt_stretch`
  and `lock_count`);
* a lane at a warp-collective state has a synchronizing state of an ordinal below the number of the
  exiting lane (`sy_lt_exit`), so the exiting lane has a synchronizing state of that ordinal, in
  the class, whose event it made.

A warp none of whose lanes exits takes a number above every lane's trace length.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Lk4
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hA : LaneAgree Q L X)
include hX hf

/-- The exit's state: an exit event fires from a state of the exit. -/
theorem exit_state {g j pc : Nat} (hx : X.get (g, j) = some ⟨pc, .exit⟩) :
    ∃ sx, St Q L X g j = some (some sx) ∧ ExitState sx := by
  rcases exit_event_state hX hf.sound hf.tracked hx with ⟨d, hσ, hd⟩ | ⟨x, hσ, hx'⟩
  · exact ⟨_, hσ, hd⟩
  · exact ⟨_, hσ, hx'⟩

omit hX hf in
private theorem exit_hex : ∀ {g' h' : Nat} {s0 s' : TSt}, ExitState s0 → (kernelSkel Q L).sy s' →
    (kernelSkel Q L).key g' s0 ≠ (kernelSkel Q L).key h' s' := fun hx' hs' => exit_key_ne hx' hs'

include hA

/-- **A lane at a warp-collective state has made fewer warp collectives than a lane of its warp
that exits.** -/
theorem wc_lt_exit {g h a j pc : Nat} {s : TSt} (hw : SameWarp L g h)
    (ha : a ≤ (X.tr g).length) (hs : St Q L X g a = some (some s)) (hc : wcSt s = true)
    (hx : X.get (h, j) = some ⟨pc, .exit⟩) :
    ((X.tr g).take a).countP Sched.isWarpColl < ((X.tr h).take j).countP Sched.isWarpColl := by
  have ht := hf.tracked
  have hh : h < L.threads := hw.1.2.1
  have hev : ClassEv Sched.isWarpColl wcSt Q L X := fun {g k e s} hg he hσ =>
    isWarpColl_state hX hf hg he hσ
  have hjl : j < (X.tr h).length := (List.getElem?_eq_some_iff.mp hx).1
  have hsk := wcSt_sy hc
  obtain ⟨sx, hsx, hxs⟩ := exit_state hX hf hx
  have hL := lock_kernel ht hA
  have hlt := sy_lt_exit (kernelSkel Q L) ht hL hA exit_hex hw ha (by omega) hs hsk hsx hxs
  obtain ⟨b0, hb0, hsy0, hn0, -⟩ := exists_last (kernelSkel Q L) (X := X) h j
    (syN (kernelSkel Q L) X h j - 1) (by omega)
  obtain ⟨b, hbb, hsyb, hnb⟩ := exists_ordinal (kernelSkel Q L) (X := X) h
    (syN (kernelSkel Q L) X h j - 1 - syN (kernelSkel Q L) X g a) (a := b0)
    (n := syN (kernelSkel Q L) X g a) hsy0 (by omega)
  obtain ⟨sb, hsb, hsyb'⟩ := hsyb
  obtain ⟨eb, heb⟩ : ∃ eb, (X.tr h)[b]? = some eb := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hkey := hL _ hw ha (by omega) hs hsb hsk hsyb' rfl hnb
  have hcb : wcSt sb = true := by rw [← wcKey_class hw hsk hsyb' hkey]; exact hc
  have hebc : Sched.isWarpColl eb = true := by
    rw [hev hh (show X.get (h, b) = some eb from heb) hsb]
    exact hcb
  have hc1 := lock_count (kernelSkel Q L) ht hL hev (fun hs => wcSt_sy hs) wcKey_class
    (syN (kernelSkel Q L) X g a) hw ha (by omega) hs hsb hsk hsyb' rfl hnb
  have hc2 := cnt_succ (X := X) Sched.isWarpColl heb
  have hc3 := cnt_mono (X := X) Sched.isWarpColl h (show b + 1 ≤ j by omega)
  simp only [hebc, ↓reduceIte] at hc2
  have e1 : cnt Sched.isWarpColl X g a = ((X.tr g).take a).countP Sched.isWarpColl := rfl
  have e2 : cnt Sched.isWarpColl X h j = ((X.tr h).take j).countP Sched.isWarpColl := rfl
  omega

/-- No lane of a warp that exits has more synchronizing states before its exit than another
exiting lane of the warp. -/
theorem exit_sy_le {f f' j j' pc pc' : Nat} (hw : SameWarp L f f')
    (hx : X.get (f, j) = some ⟨pc, .exit⟩) (hx' : X.get (f', j') = some ⟨pc', .exit⟩) :
    ¬ syN (kernelSkel Q L) X f j < syN (kernelSkel Q L) X f' j' := by
  intro hlt
  have ht := hf.tracked
  have hL := lock_kernel ht hA
  obtain ⟨sx, hsx, hxs⟩ := exit_state hX hf hx
  have hjl : j < (X.tr f).length := (List.getElem?_eq_some_iff.mp hx).1
  have hjl' : j' < (X.tr f').length := (List.getElem?_eq_some_iff.mp hx').1
  obtain ⟨b0, hb0, hsy0, hn0, -⟩ := exists_last (kernelSkel Q L) (X := X) f' j'
    (syN (kernelSkel Q L) X f' j' - 1) (by omega)
  obtain ⟨b, hbb, hsyb, hnb⟩ := exists_ordinal (kernelSkel Q L) (X := X) f'
    (syN (kernelSkel Q L) X f' j' - 1 - syN (kernelSkel Q L) X f j) (a := b0)
    (n := syN (kernelSkel Q L) X f j) hsy0 (by omega)
  obtain ⟨sb, hsb, hsyb'⟩ := hsyb
  have := sy_lt_exit (kernelSkel Q L) ht hL hA exit_hex (sameWarp_symm hw) (by omega)
    (by omega) hsb hsyb' hsx hxs
  omega

/-- **The lanes of a warp that exit have made one number of warp collectives.** -/
theorem wc_exit_eq {f f' j j' pc pc' : Nat} (hw : SameWarp L f f')
    (hx : X.get (f, j) = some ⟨pc, .exit⟩) (hx' : X.get (f', j') = some ⟨pc', .exit⟩) :
    ((X.tr f).take j).countP Sched.isWarpColl = ((X.tr f').take j').countP Sched.isWarpColl := by
  have ht := hf.tracked
  have hL := lock_kernel ht hA
  have hf1 : f < L.threads := hw.1.1
  have hf2 : f' < L.threads := hw.1.2.1
  have hev : ClassEv Sched.isWarpColl wcSt Q L X := fun {g k e s} hg he hσ =>
    isWarpColl_state hX hf hg he hσ
  obtain ⟨sx, hsx, hxs⟩ := exit_state hX hf hx
  obtain ⟨sx', hsx', hxs'⟩ := exit_state hX hf hx'
  have hjl : j < (X.tr f).length := (List.getElem?_eq_some_iff.mp hx).1
  have hjl' : j' < (X.tr f').length := (List.getElem?_eq_some_iff.mp hx').1
  have h1 := exit_sy_le hX hf hA hw hx hx'
  have h2 := exit_sy_le hX hf hA (sameWarp_symm hw) hx' hx
  have hN : syN (kernelSkel Q L) X f j = syN (kernelSkel Q L) X f' j' := by omega
  have e1 : cnt Sched.isWarpColl X f j = ((X.tr f).take j).countP Sched.isWarpColl := rfl
  have e2 : cnt Sched.isWarpColl X f' j' = ((X.tr f').take j').countP Sched.isWarpColl := rfl
  rw [← e1, ← e2]
  cases hn : syN (kernelSkel Q L) X f j with
  | zero =>
    have hn' : syN (kernelSkel Q L) X f' j' = 0 := by omega
    rw [cnt_zero (kernelSkel Q L) ht hev (fun hs => wcSt_sy hs) hf1 hsx hjl.le
      (fun i hi => no_sy_of_zero (kernelSkel Q L) f hn i (Nat.zero_le _) hi) j le_rfl,
      cnt_zero (kernelSkel Q L) ht hev (fun hs => wcSt_sy hs) hf2 hsx' hjl'.le
      (fun i hi => no_sy_of_zero (kernelSkel Q L) f' hn' i (Nat.zero_le _) hi) j' le_rfl]
  | succ m =>
    have hn' : syN (kernelSkel Q L) X f' j' = m + 1 := by omega
    obtain ⟨b, hbj, hsyb, hnb, hnob⟩ := exists_last (kernelSkel Q L) (X := X) f j m hn
    obtain ⟨b', hbj', hsyb', hnb', hnob'⟩ := exists_last (kernelSkel Q L) (X := X) f' j' m hn'
    obtain ⟨sb, hsb, hsyb2⟩ := hsyb
    obtain ⟨sb', hsb', hsyb2'⟩ := hsyb'
    obtain ⟨eb, heb⟩ : ∃ eb, (X.tr f)[b]? = some eb :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨eb', heb'⟩ : ∃ eb', (X.tr f')[b']? = some eb' :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hkey := hL m hw (by omega) (by omega) hsb hsb' hsyb2 hsyb2' hnb hnb'
    have hcls := wcKey_class hw hsyb2 hsyb2' hkey
    have hcnt := lock_count (kernelSkel Q L) ht hL hev (fun hs => wcSt_sy hs) wcKey_class m hw
      (by omega) (by omega) hsb hsb' hsyb2 hsyb2' hnb hnb'
    have s1 := cnt_stretch (kernelSkel Q L) ht hev (fun hs => wcSt_sy hs) hf1 hsx hjl.le
      (fun i h1 h2 => hnob i h1 h2) j (by omega) le_rfl
    have s2 := cnt_stretch (kernelSkel Q L) ht hev (fun hs => wcSt_sy hs) hf2 hsx' hjl'.le
      (fun i h1 h2 => hnob' i h1 h2) j' (by omega) le_rfl
    rw [s1, s2, cnt_succ Sched.isWarpColl heb, cnt_succ Sched.isWarpColl heb', hcnt,
      hev hf1 (show X.get (f, b) = some eb from heb) hsb,
      hev hf2 (show X.get (f', b') = some eb' from heb') hsb', hcls]

omit hX hf hA in
/-- Two threads with one warp key are lanes of one warp. -/
theorem sameWarp_of_key {g h : Nat} (hg : g < L.threads) (hh : h < L.threads)
    (hk : warpKey L g = warpKey L h) : SameWarp L g h := by
  simp only [warpKey, Prod.mk.injEq] at hk
  exact ⟨⟨hg, hh, hk.1⟩, hk.2⟩

/-- **`WarpCollFacts.exit`**: the number of warp collectives of the exiting lanes of a warp, or,
for a warp none of whose lanes exits, a number above every lane's trace length. -/
theorem warpColl_exit : ∃ N : Nat × Nat → Nat,
    (∀ {g : Nat} {d : TSt}, g < L.threads → St Q L X g (X.tr g).length = some (some d) →
      nextKind d = .warp → (X.tr g).countP Sched.isWarpColl < N (warpKey L g)) ∧
    (∀ {g k pc : Nat} {d : TSt}, g < L.threads → St Q L X g k = some (some d) →
      X.get (g, k) = some ⟨pc, .exit⟩ →
        N (warpKey L g) ≤ ((X.tr g).take k).countP Sched.isWarpColl) := by
  classical
  let E : Nat × Nat → Prop := fun W =>
    ∃ g k pc, g < L.threads ∧ warpKey L g = W ∧ X.get (g, k) = some ⟨pc, .exit⟩
  let N : Nat × Nat → Nat := fun W =>
    if h : E W then ((X.tr h.choose).take h.choose_spec.choose).countP Sched.isWarpColl
    else (Finset.range L.threads).sup
      (fun g => if warpKey L g = W then (X.tr g).length + 1 else 0)
  have hN : ∀ W (h : E W), ∃ g k pc, g < L.threads ∧ warpKey L g = W ∧
      X.get (g, k) = some ⟨pc, .exit⟩ ∧ N W = ((X.tr g).take k).countP Sched.isWarpColl := by
    intro W h
    have hs := h.choose_spec.choose_spec.choose_spec
    exact ⟨h.choose, h.choose_spec.choose, _, hs.1, hs.2.1, hs.2.2,
      by simp only [N, h, ↓reduceDIte]⟩
  refine ⟨N, ?_, ?_⟩
  · intro g d hg hσ hk
    have hc : wcSt d = true := (nextKind_warp d).mp hk
    by_cases hE : E (warpKey L g)
    · obtain ⟨f, j, pc, hf1, hw, hx, hNW⟩ := hN _ hE
      have hsw := sameWarp_of_key hg hf1 hw.symm
      rw [hNW]
      have := wc_lt_exit hX hf hA hsw le_rfl hσ hc hx
      rwa [List.take_length] at this
    · have : N (warpKey L g) = (Finset.range L.threads).sup
          (fun g' => if warpKey L g' = warpKey L g then (X.tr g').length + 1 else 0) := by
        simp only [N, hE, ↓reduceDIte]
      rw [this]
      have h1 := Finset.le_sup (f := fun g' =>
        if warpKey L g' = warpKey L g then (X.tr g').length + 1 else 0)
        (Finset.mem_range.mpr hg)
      simp only [↓reduceIte] at h1
      have h2 : (X.tr g).countP Sched.isWarpColl ≤ (X.tr g).length := List.countP_le_length
      omega
  · intro g k pc d hg hσ hx
    have hE : E (warpKey L g) := ⟨g, k, pc, hg, rfl, hx⟩
    obtain ⟨f, j, pc', hf1, hw, hx', hNW⟩ := hN _ hE
    have hsw := sameWarp_of_key hg hf1 hw.symm
    rw [hNW]
    exact (wc_exit_eq hX hf hA hsw hx hx').ge

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Lk4
