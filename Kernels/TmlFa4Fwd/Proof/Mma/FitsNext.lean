-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Fits
public import Kernels.TmlFa4Fwd.Proof.Mma.Ref
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A step keeps the MMA warp's fits, from its count conjuncts -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (laneW paramW chosen Picked)

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ns nv : Nat}

set_option maxHeartbeats 4000000 in
/-- **The step into the second pass**: the pipeline's broadcasts are the full pipeline's of the
picked tile, from the loop's round count at the tail (`RefQ.tail`). -/
theorem mfits_pass2 {d : D} {n : Cnt → Nat} (hs : d.site = .ce 11 ∨ d.site = .cm 11)
    (hF : MFits p L g d ns nv) (hJ : RefCounts p L g (d, n)) :
    MFits p L g (passStart p L g true d) ns nv := by
  have hpm : d.site.pmid := by rcases hs with h | h <;> rw [h] <;> exact pmid_of rfl
  obtain ⟨R, bal, hC, hB⟩ := bs_ref hpm hF
  obtain ⟨s, v⟩ := d
  obtain ⟨hps, -, -, -, -⟩ := mfits_main hpm.2.1 hF
  obtain ⟨hPk, -⟩ := id hC
  have hq : 60 ≤ s.ord ∧ s.ord < 100 ∧ shAt s.ord = shAt 100 := by
    rcases hs with h | h <;> simp only at h <;> subst h <;>
      refine ⟨by decide, by decide, funext fun r => ?_⟩ <;> simp [Site.ord, shAt, pq]
  obtain ⟨r, w, hQ, -⟩ := hJ
  have hr : r = (Bs p L g (refV p L g R bal) - 1).toNat := by
    have := hQ.tail ⟨hq.1, hq.2.1⟩
    rw [hB] at this
    omega
  have hps' : v.ps = pipeN p L g R bal := by
    rw [hQ.ps, hq.2.2, hr]; rfl
  have hP2 := Epilogue.fits_pass2 (p := p) (L := L) (g := g) hC
  simp only [passStart, ↓reduceIte]
  split <;> rename_i hb <;> simp only [hb, ↓reduceIte] at hP2 <;>
    simp only [MFits, scAt, Site.early, Bool.false_eq_true, ↓reduceIte] <;>
    exact ⟨hps, hP2, by simp [Site.pipe], fun _ => ⟨R, bal, hPk, hps'⟩,
      by simp [Site.late, Epilogue.Scan.late]⟩

/-- A commit's successor keeps the reference values: the pipeline, or the second pass. -/
theorem ceNext_mfits {d : D} {n : Cnt → Nat} {c : Fin 12} (hs : d.site = .ce c ∨ d.site = .cm c)
    (hF : MFits p L g d ns nv) (hJ : RefCounts p L g (d, n)) :
    MFits p L g (ceNext p L g d c) ns nv := by
  by_cases hc : c = 11
  · subst hc
    exact mfits_pass2 hs hF hJ
  · obtain ⟨h1, h2, h3, h4⟩ := ceNext_pipe (p := p) (L := L) (g := g) (d := d) hc
    exact mfits_pipe (k := 0) (by rcases hs with h | h <;> rw [h] <;> exact pmid_of rfl) h1 hF h2
      h3 h4

set_option maxHeartbeats 8000000 in
/-- **The pipeline's and the end's steps keep the reference values**, except the step into the
second pass. -/
theorem mfits_quiet {d d' : D} {e : Event} (hs : d.site.sched = false)
    (hs2 : d.site ≠ .tiles false) (hs3 : d.site.early = false)
    {n : Cnt → Nat} (hJ : RefCounts p L g (d, n)) (hF : MFits p L g d ns nv)
    (hE : MExpect p L g d ns e) (hev : Ev p L g d e) (hn : succ p L g d e = some (some d')) :
    MFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  have hz : ∀ k : Kind, (∀ m a b c r o, k ≠ .shfl m a b c r o) → (∀ m a b, k ≠ .vote m a b) →
      (∀ md m a b, k ≠ .voteMode md m a b) →
      Epilogue.sh ⟨pc, k⟩ = 0 ∧ Epilogue.vt ⟨pc, k⟩ = 0 := by
    intro k hk hv hw
    cases k
    case shfl => exact absurd rfl (hk _ _ _ _ _ _)
    case vote => exact absurd rfl (hv _ _ _)
    case voteMode => exact absurd rfl (hw _ _ _ _)
    all_goals simp [Epilogue.sh, Epilogue.vt, Execution.isShfl, isFullVote, voteClass]
  cases s <;> simp only [Site.sched, Site.early, reduceCtorEq] at hs hs3
  case tiles l => cases l <;> simp_all
  case uk =>
    simp only [Ev] at hev
    rcases hev with ⟨bs, hk⟩ | ⟨f, hk⟩ <;> subst hk <;> simp only [succ, reduceCtorEq] at hn
    simp only [MExpect] at hE
    rw [hE] at hn
    simp only [word32, Option.some.injEq] at hn
    subst hn
    rw [(hz _ (by simp) (by simp) (by simp)).1, (hz _ (by simp) (by simp) (by simp)).2]
    exact mfits_keep rfl rfl hF rfl rfl rfl (fun _ => .inl rfl) rfl
      (fun h => by simp [Site.pipe] at h) (fun h => absurd rfl h)
  case relinq l | bar2 l | dealloc l =>
    simp only [Ev] at hev
    have hzz := hz kind (by
      intro m a b c r o h; subst h; first | simp at hev | (rcases hev with h | h <;> simp at h))
      (by intro m a b h; subst h; first | simp at hev | (rcases hev with h | h <;> simp at h))
      (by intro md m a b h; subst h; first | simp at hev | (rcases hev with h | h <;> simp at h))
    rw [hzz.1, hzz.2]
    simp only [succ, Option.some.injEq] at hn
    subst hn
    exact mfits_keep rfl rfl hF rfl rfl rfl (fun h => by simp [Site.pipe] at h) rfl
      (fun _ => rfl) (fun h => absurd rfl h)
  case exit l => simp [succ] at hn
  case sh k =>
    simp only [Ev] at hev
    obtain ⟨recv, ok, hk⟩ := hev
    subst hk
    simp only [MExpect] at hE
    obtain ⟨x, rfl⟩ := hE
    simp only [succ, word32, Option.some.injEq] at hn
    subst hn
    have h1 : Epilogue.sh ⟨pc, .shfl .idx (.bits 32 (shSrc L v k)) 0 31 (.bits 32 x) ok⟩ = 1 := rfl
    have h2 : Epilogue.vt ⟨pc, .shfl .idx (.bits 32 (shSrc L v k)) 0 31 (.bits 32 x) ok⟩ = 0 := rfl
    rw [h1, h2, Nat.add_zero]
    exact mfits_pipe (pmid_of rfl) (pmid_shNext k) hF (by fin_cases k <;> rfl)
      (by fin_cases k <;> rfl) rfl
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals subst_vars
  all_goals rw [(hz _ (by simp) (by simp) (by simp)).1, (hz _ (by simp) (by simp) (by simp)).2]
  all_goals simp only [Nat.add_zero]
  all_goals simp only [succ, reduceCtorEq, Option.some.injEq] at hn
  all_goals first | (cases hn; done) | skip
  all_goals first
    | (subst hn; exact mfits_pipe (k := 0) (pmid_of rfl) (pmid_ite (pmid_of rfl) (pmid_qkDone _))
        hF rfl rfl rfl)
    | (subst hn; exact mfits_pipe (k := 0) (pmid_of rfl) (pmid_ite (pmid_qkDone _) (pmid_of rfl))
        hF rfl rfl rfl)
    | (subst hn; exact mfits_pipe (k := 0) (pmid_of rfl) (pmid_ite (pmid_of rfl) (pmid_of rfl))
        hF rfl rfl rfl)
    | (subst hn; exact mfits_pipe (k := 0) (pmid_of rfl)
        (pmid_ite (pmid_of rfl) (pmid_ite (pmid_pvDone _) (pmid_of rfl))) hF rfl rfl rfl)
    | (split at hn <;> subst hn
       · exact mfits_pipe (k := 0) (pmid_of rfl) (pmid_wtNext _) hF rfl rfl rfl
       · exact mfits_pipe (k := 0) (pmid_of rfl) (pmid_of rfl) hF rfl rfl rfl)
    | (split at hn <;> subst hn
       · exact mfits_pipe (k := 0) (pmid_of rfl) (pmid_ite (pmid_of rfl) (pmid_pvDone _)) hF rfl
          rfl rfl
       · exact mfits_pipe (k := 0) (pmid_of rfl) (pmid_of rfl) hF rfl rfl rfl)
    | (split at hn
       · subst hn; exact mfits_pipe (k := 0) (pmid_of rfl) (pmid_of rfl) hF rfl rfl rfl
       · subst hn; exact ceNext_mfits (.inl rfl) hF hJ)
    | (subst hn; exact ceNext_mfits (.inr rfl) hF hJ)



/-- **Every step of an MMA lane on an event that returns what the reference says keeps the
reference values**, with the shuffle and ballot it adds. -/
theorem mfits_next {d d' : D} {e : Event} {n : Cnt → Nat} (hF : MFits p L g d ns nv)
    (hE : MExpect p L g d ns e) (hev : Ev p L g d e) (hJ : RefCounts p L g (d, n))
    (hn : succ p L g d e = some (some d')) :
    MFits p L g d' (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  by_cases hs : d.site.sched = true
  · exact mfits_sched hs hF hE hev hn
  by_cases ht : d.site = .tiles false
  · exact mfits_tiles ht hF hE hn
  by_cases hb : d.site = .bcast
  · exact mfits_bcast hb hF hev hn
  cases he : d.site.early
  · exact mfits_quiet (by simpa using hs) ht he hJ hF hE hev hn
  · obtain ⟨s, v⟩ := d
    obtain ⟨pc, kind⟩ := e
    simp only at hb he
    cases s <;> simp only [Site.early, reduceCtorEq, not_true_eq_false] at he hb
    all_goals simp only [Ev] at hev
    all_goals simp only [MFits, Site.early, ↓reduceIte] at hF
    · rw [hev] at hn
      simp only [succ, Option.some.injEq] at hn
      subst hn
      simpa [MFits, Site.early, Epilogue.sh, Epilogue.vt, hev, Execution.isShfl, isFullVote,
        voteClass] using hF
    · rcases hev with ⟨a, bs, hk⟩ | ⟨f, hk⟩ <;> subst hk <;> simp only [succ, reduceCtorEq] at hn
      split at hn <;> simp only [reduceCtorEq, Option.some.injEq] at hn
      subst hn
      simpa [MFits, Site.early, Epilogue.sh, Epilogue.vt, Execution.isShfl, isFullVote,
        voteClass] using hF

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
