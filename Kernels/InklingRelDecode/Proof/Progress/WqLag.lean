-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WqMono
public import Kernels.InklingRelDecode.Proof.Progress.WnAll

@[expose] public section

/-!
# `WarpCollFacts.lag`: a lane behind a lane at a warp collective is earlier

Lane `g` is at a warp-collective state `d` after `n` warp collectives, released, in a maximal
execution; lane `h` of its warp has made at most `n` and is not at a warp-collective state after
exactly `n`. Then `threadTime h < time g d` (`lag_of`):

* `h` has not exited: it would have made more warp collectives (`Lk4.warpColl_exit`).
* `h` has not stopped (`St … = none`): if its last event is released, the machine's undefined
  behaviour extends the execution (`Step.dead_counted_extension`), against maximality; otherwise
  its last event blocks, so it is a synchronizing event `x` fired from a synchronizing state of
  some ordinal `M`, and `M < N`, `g`'s ordinal (`Wn.lag_ordinal`). `g`'s synchronizing state of
  ordinal `M` made `x` too (`Wn.made_of_ord`), and that event of the released `g` is ready, so
  `h`'s is (`released_of_sync`), against the assumption.
* So `h` is at a state `sh` of ordinal `m ≤ N`. `g`'s state of ordinal `m` (`d` if `m = N`, an
  earlier synchronizing state otherwise) has the key time of `sh` (`Lk.kx_lock`, with the
  loader's and the MMA warp's counters at their `bar0` and the dispatch's first round from the
  invariants `ipre_inv`, `late_inv`). If `m = N`, `sh` is not synchronizing, so its time is below
  its key time, which is `d`'s time; if `m < N`, `sh`'s time is at most its key time, which is
  below `d`'s along `g`'s trace (`kx_mono`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wq
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX.Kernels.InklingRelDecode.Proof.Progress.Lk4

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The number the worker lanes' synchronizing states are valid with: the CTA's `num_pre`. -/
def npOf (Q : Params) (L : Launch) (g : Nat) : Nat :=
  ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x)

theorem npOf_eq {g h : Nat} (hw : SameWarp L g h) : npOf Q L g = npOf Q L h := by
  have hc : g / L.block = h / L.block := hw.1.2.2
  simp only [npOf, ProA.cta, hc]

/-- **The worker lanes' synchronizing states are valid**: the loader's counter at `bar0` is the
CTA's `num_pre`, the MMA warp's is 0, and the dispatch's first shuffle is not in a later round. -/
theorem valid_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X) {g k : Nat}
    {s : WComp.WSt} (_hg : g < L.threads) (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w s))) (_hsy : tSy (.w s)) :
    PTX.Kernels.InklingRelDecode.Proof.Lk.WValid (npOf Q L g) s := by
  have hI := ipre_inv hpre hX hf hp k _ hσ
  cases s with
  | worker w =>
    intro hs
    obtain ⟨site, P⟩ := w
    simp only at hs
    subst hs
    exact ((Wu.late_inv hpre hX hf.sound hR k _ hk.le hσ).1 P .shfl
      (Or.inr (Or.inr (Or.inr rfl))) rfl).2
  | loader d P => exact fun h0 => hI (.inr h0)
  | mma d P => exact fun h0 => hI (.inr (.inr h0))
  | idle d => trivial
  | exit x => trivial

/-- **`WarpCollFacts.lag`** in a maximal execution, for a released thread at the collective. -/
theorem lag_of (hpre : Pre Q L mem0) (hmax : Maximal L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hA : LaneAgree Q L X) (hR : RoleReads L X)
    (hp : NumPreRead Q L X) (hub : ¬ HasUb X) {g h : Nat} {d : TSt} (hg : g < L.threads)
    (hh : h < L.threads) (hw : SameWarp L g h)
    (hσ : St Q L X g (X.tr g).length = some (some d)) (hk : nextKind d = .warp)
    (hrel : Step.Released L X g)
    (hle : (X.tr h).countP Sched.isWarpColl ≤ (X.tr g).countP Sched.isWarpColl)
    (hno : ¬ ((X.tr h).countP Sched.isWarpColl = (X.tr g).countP Sched.isWarpColl ∧
      ∃ d', St Q L X h (X.tr h).length = some (some d') ∧ nextKind d' = .warp)) :
    0 < Wt.time g d ∧ Sched.threadTime (timed Wt.time Q L) X h < Wt.time g d := by
  have hX := hmax.1
  have hS := hf.sound
  have ht := hf.tracked
  refine ⟨by have := Wt.time_ge_two g d; omega, ?_⟩
  have hc : wcSt d = true := (nextKind_warp d).mp hk
  have hsyd : tSy d := wcSt_sy hc
  -- `h` has not exited
  have hnx : ∀ j pc, X.get (h, j) ≠ some ⟨pc, .exit⟩ := by
    intro j pc hj
    obtain ⟨N, hT1, hT2⟩ := warpColl_exit hX hf hA
    obtain ⟨dx, hdx⟩ := Frame.state_of_noUb hS hX ht hub hj
    have h1 := hT1 hg hσ hk
    have h2 := hT2 hh hdx hj
    have hjl : j ≤ (X.tr h).length := (len_of_get hj).le
    have h3 := Flow.countP_take_mono Sched.isWarpColl (X.tr h) hjl
    rw [List.take_length] at h3
    rw [← warpKey_eq hw] at h2
    omega
  have hph := pending_of_noExit hX hh hnx
  have hord := Wn.lag_ordinal hX hf hA hw hσ hk hle hno
  have hw2 : g % L.block / 32 = h % L.block / 32 := hw.2
  rcases Wu.end_cases hX hS ht hub hh hnx with ⟨sh, hσh, hIh⟩ | ⟨sp, ep, hlen, hσp, hσn, -, hep⟩
  · -- `h` is at a state
    rw [threadTime_eq hσh]
    have hlock := kx_lock ht hA (npOf Q L) npOf_eq
      (fun hg' hk' hσ' hsy' => valid_of hpre hX hf hR hp hg' hk' hσ' hsy')
    have hcls : ∀ {a : Nat} {s : TSt}, a ≤ (X.tr g).length → St Q L X g a = some (some s) →
        (sh.isD ↔ s.isD) := fun {a} {s} ha hs => by
      rw [cls_inv _ sh le_rfl hσh, cls_inv _ s ha hs]
      constructor <;> intro <;> omega
    rcases Nat.lt_or_ge (syN (kernelSkel Q L) X h (X.tr h).length)
      (syN (kernelSkel Q L) X g (X.tr g).length) with hlt | hge
    · -- an earlier ordinal: `g`'s synchronizing state of that ordinal
      obtain ⟨a, ha, hsa, hna⟩ := exists_ordinal (kernelSkel Q L) (X := X) g
        (syN (kernelSkel Q L) X g (X.tr g).length - syN (kernelSkel Q L) X h (X.tr h).length)
        ⟨d, hσ, hsyd⟩ (n := syN (kernelSkel Q L) X h (X.tr h).length) (by omega)
      have ha' : a < (X.tr g).length := by
        rcases Nat.lt_or_ge a (X.tr g).length with h1 | h1
        · exact h1
        · exfalso
          have : a = (X.tr g).length := by omega
          rw [this] at hna
          omega
      obtain ⟨sa, hsa, hsya⟩ := hsa
      have hx := hlock _ (sameWarp_symm hw) le_rfl ha hσh hsa rfl hna
      have hkey := lock_any ht hA _ (sameWarp_symm hw) le_rfl ha hσh hsa rfl hna
      have h1 : Wt.time h sh ≤ kx L h sh := by
        by_cases hs : tSy sh
        · rw [kx_sy hs]
        · exact (kx_lt hs hIh hsya (hcls ha hsa) hkey).le
      have h2 := (kx_mono hpre hX hS ht hR hg hσ hsyd a (X.tr g).length ha'.le le_rfl hsa hσ).2
        hsya ha'
      rw [kx_sy hsyd] at h2
      omega
    · -- the same ordinal: `h` is not at a synchronizing state
      have heq : syN (kernelSkel Q L) X h (X.tr h).length =
          syN (kernelSkel Q L) X g (X.tr g).length := le_antisymm hord.1 hge
      have hns := hord.2 heq sh hσh
      have hx := hlock _ (sameWarp_symm hw) le_rfl le_rfl hσh hσ rfl heq.symm
      have hkey := lock_any ht hA _ (sameWarp_symm hw) le_rfl le_rfl hσh hσ rfl heq.symm
      have := kx_lt hns hIh hsyd (hcls le_rfl hσ) hkey
      rw [hx, kx_sy hsyd] at this
      exact this
  · -- `h` stopped at its last event: impossible in a maximal execution
    exfalso
    obtain ⟨u, hrun⟩ := Frame.run_some hX hub hph
    have hne : X.tr h ≠ [] := by
      intro h0
      rw [h0] at hlen
      simp at hlen
    by_cases hrh : Step.Released L X h
    · obtain ⟨Y, hY, hXY, hsz⟩ := Step.dead_counted_extension hX hh hne hrh
        (fun _ _ => asms_wfStep.quiet hX le_snoc rfl (Execution.noNewRead_snoc rfl)) hrun
        (Frame.end_dead hS hh hrun hσn)
      have := hmax.2 Y hY hXY
      omega
    · have hu : ¬ Sched.Unblocking ep.kind := fun hu => hrh (Sched.released_of_unblocking hep hu)
      have hsyp := Wn.sy_of_blocking hpre hX hf hh hep hσp hu
      obtain ⟨x, hx, hxh⟩ := Wn.sync_self hpre hX hf hh hep hu
      have hNh : syN (kernelSkel Q L) X h (X.tr h).length =
          syN (kernelSkel Q L) X h ((X.tr h).length - 1) + 1 := by
        have := syN_succ (kernelSkel Q L) (X := X) h ((X.tr h).length - 1)
        rw [Nat.sub_add_cancel hlen] at this
        have hi : IsSy (kernelSkel Q L) X h ((X.tr h).length - 1) := ⟨sp, hσp, hsyp⟩
        simp only [this, hi, ↓reduceIte]
      have hmN := hord.1
      obtain ⟨a, ha, hsa, hna⟩ := exists_ordinal (kernelSkel Q L) (X := X) g
        (syN (kernelSkel Q L) X g (X.tr g).length -
          syN (kernelSkel Q L) X h ((X.tr h).length - 1))
        ⟨d, hσ, hsyd⟩ (n := syN (kernelSkel Q L) X h ((X.tr h).length - 1)) (by omega)
      have ha' : a < (X.tr g).length := by
        rcases Nat.lt_or_ge a (X.tr g).length with h1 | h1
        · exact h1
        · exfalso
          have : a = (X.tr g).length := by omega
          rw [this] at hna
          omega
      obtain ⟨sa, hsa, hsya⟩ := hsa
      have hxg := Wn.made_of_ord hpre hX hf hA hw ha' (by omega) hsa hσp hsya hsyp hna hep hu hx
      exact hrh (released_of_sync hX hw hrel hxg hxh
        (allocStored_of hpre hX hf hg hσ (by rw [hk]; decide)))

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wq
