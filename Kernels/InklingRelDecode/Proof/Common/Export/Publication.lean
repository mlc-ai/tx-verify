-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Occurs
import Kernels.InklingRelDecode.Proof.Common.OccursSite
import Kernels.InklingRelDecode.Proof.Common.PublicationPrefix
import Lemmas.Kernel.Safety.TableU
import Kernels.InklingRelDecode.Proof.Lib.ResPcs
import Lemmas.Flow.NotBulk

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow

/-- Barrier-1 generations at stores into the query tile, the role word and the count pair. -/
def publishedAt : Nat → Option Nat
  | 526 | 532 | 538 | 544 | 550 | 556 | 562 | 568 | 570 | 571 => some 0
  | 2250 => some 2
  | 2848 => some 3
  | _ => none

private def phaseOneModThree (p : Nat) :=
  p == 2340 || p == 2345 || p == 2423 || p == 2853 || p == 2855

/-- Mbarrier uses after the first two full-CTA rendezvous. -/
def afterInit (p : Nat) :=
  999≤p && p≤2326 || 2374≤p && p≤2412 || 2462≤p && p≤2553 || p==2565 || p==2850

private def fits (p n : Nat) : Bool :=
  (publishedAt p).all (· == n) && ((!phaseOneModThree p || n%3 == 1) &&
    (!afterInit p || decide (2≤n)))

private theorem pro_sites (s : Prologue.Site) : fits s.pc (Prologue.publicationPhase s) = true := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem soft_sites (s : Softmax.Site) : fits s.pc (Softmax.publicationPhase s) = true := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem epi_sites (s : Epilogue.Site) : fits s.pc (Epilogue.publicationPhase s) = true := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem worker_round {p n} (r : Nat) (clear : publishedAt p = none)
    (valid : fits p n = true) : fits p (3*r+n) = true := by
  simp only [fits,clear,Option.all_none,Bool.true_and,Bool.and_eq_true] at valid ⊢
  refine ⟨by simpa [Nat.add_mod] using valid.1,?_⟩
  cases h : afterInit p <;> simp [h] at valid ⊢
  omega

private theorem loader_sites (s : Loader.Site) : publishedAt s.pc = none ∧
    fits s.pc (Loader.publicationPhase s) = true := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem mma_sites (s : Mma.Site) : publishedAt s.pc = none ∧
    fits s.pc (Mma.publicationPhase s) = true := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem dispatch_sites (s : Dispatch.Site) : publishedAt s.pc = none ∧
    fits s.pc (Dispatch.publicationOffset s) = true := by cases s <;> decide

private theorem state_fits {Q L g} (s : (thread Q L g).D) :
    fits ((thread Q L g).pc s) (publication s) = true := by
  obtain ⟨s,n⟩ := s
  rcases s with s | ⟨r,s⟩
  · change fits s.site.pc 0 = true
    generalize s.site = site
    cases site <;> first | decide | (rename_i r; cases r <;> decide)
  · rcases r with r | r
    · cases r with
      | prologue w =>
        rcases s with s | ⟨ent,s | ⟨_,s⟩⟩
        · exact pro_sites s.site
        · exact soft_sites s.site
        · exact epi_sites s.site
      | dispatch w x =>
        rcases s with s | ⟨r,s⟩
        · exact worker_round _ (dispatch_sites s.site).1 (dispatch_sites s.site).2
        · cases r with
          | loader => exact worker_round _ (loader_sites s.site).1 (loader_sites s.site).2
          | mma => exact worker_round _ (mma_sites s.site).1 (mma_sites s.site).2
    · change fits r.pc 0 = true
      cases r <;> decide

private theorem observed_at {Q L m X g k s} {e : Event} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (nu : Frame.NoUbBefore X g k) (hs : Frame.stateAt (thread Q L) X g k = some (some s))
    (pc : e.pc = (thread Q L g).pc s) :
    fits e.pc (((X.tr g).take k).countP (Execution.isBarId 1)) = true := by
  rw [pc, publication_prefix hp hX hg nu hs]
  exact state_fits s

private theorem observed {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k) = some e)
    (hu : ∀ f, e.kind ≠ .ub f) :
    fits e.pc (((X.tr g).take k).countP (Execution.isBarId 1)) = true := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (fun _ f eq => hu f (congrArg Event.kind eq))
      ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  exact observed_at hp hX hg (Frame.noUbBefore_of_get hX he) hs
    (Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs hu)

theorem publication_store {Q L m X g k pc a bs phase} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k) = some ⟨pc,.wr a bs⟩)
    (site : publishedAt pc = some phase) :
    ((X.tr g).take k).countP (Execution.isBarId 1) = phase := by
  have both := observed hp hX he (by simp)
  simp only [fits,Bool.and_eq_true] at both
  have h := both.1
  change (publishedAt pc).all _ = true at h
  rw [site] at h
  exact (beq_iff_eq.mp h).symm

theorem publication_read {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k) = some ⟨pc,.rd a bs⟩)
    (site : pc = 2340 ∨ pc = 2345 ∨ pc = 2423) :
    ((X.tr g).take k).countP (Execution.isBarId 1) % 3 = 1 := by
  have both := observed hp hX he (by simp)
  simp only [fits,Bool.and_eq_true] at both
  have h := both.2.1
  rcases site with rfl | rfl | rfl <;> simpa [phaseOneModThree] using h

theorem after_initialization {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some e)
    (ordinary : ∀ f, e.kind≠.ub f) (site : afterInit e.pc) :
    2≤((X.tr g).take k).countP (Execution.isBarId 1) := by
  have h := observed hp hX he ordinary
  simp only [fits,Bool.and_eq_true] at h
  simpa [site] using h.2.2

/-- An event that occurs (in the trace, or the lane's next) after initialization has crossed the
first two publication barriers. -/
theorem after_initialization_occ {Q L m X g k} {e : Event} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (he : Occurs L X g k e)
    (ordinary : ∀ f, e.kind≠.ub f) (site : afterInit e.pc) :
    2≤((X.tr g).take k).countP (Execution.isBarId 1) := by
  obtain ⟨s,hs,pc,-⟩ := he.site hp hX hf ordinary
  have h := observed_at hp hX (he.lt hX) (he.noUb hX) hs pc
  simp only [fits,Bool.and_eq_true] at h
  simpa [site] using h.2.2

/-- The worker's final rendezvous follows a positive number of publication barriers. -/
theorem exit_sync_publication {Q L m X g k cnt} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨2853,.bar 0 cnt .sync⟩) :
    1≤((X.tr g).take k).countP (Execution.isBarId 1) := by
  have h := observed hp hX he (by simp)
  change (true && ((_ % 3 == 1) && true)) = true at h
  simp only [Bool.true_and,Bool.and_true,beq_iff_eq] at h
  omega

/-- Even a worker taking the earliest possible exit has crossed generation zero. -/
theorem publication_exit {Q L m X g k pc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k) = some ⟨pc,.exit⟩) :
    1 ≤ (X.tr g).countP (Execution.isBarId 1) := by
  obtain ⟨_,bad⟩ | ⟨_,_,_,_,code,fire⟩ := get_source hX he
  · cases bad
  have site := Lib.ret_pc' code fire rfl
  obtain rfl : pc=2855 := by simpa [Lib.retPcs] using site
  have pos := observed hp hX he (by simp)
  change (true && ((_ % 3 == 1) && true)) = true at pos
  simp only [Bool.true_and,Bool.and_true,beq_iff_eq] at pos
  have bound := (List.take_sublist k (X.tr g)).countP_le (p := Execution.isBarId 1)
  omega

end PTX.Kernels.InklingRelDecode.Proof.Export
