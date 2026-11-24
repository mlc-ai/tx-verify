-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepBase
public import Lemmas.Assumption.Facts
public import Lemmas.Flow.PackMul
public import Lemmas.Flow.EventCont
public import Lemmas.Flow.SegDead
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The kernel's assumptions at the correction warps' code

The steps of the correction warps that rely on assumptions beyond `idealArith` and
`clusterMbar` (the implicit `tcgen05.wait::ld` after each load, the exact reciprocal) are stated
under the kernel's full list `asms` (`Assumptions.all`). At the correction code (from pc 3700 on):

* no assumption takes a segment (`segFree`): the software-`exp2` segments and the peer-bit
  steps start below it;
* `mul.f32x2` and `setp.f32` are read as exact real arithmetic (`idealAt`);
* each Tensor Memory load of the rescale and of the final normalization is followed by the
  implicit wait (`tcLdWait_rld`, `tcLdWait_fld`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- Every segment of the kernel's assumptions starts at a software-`exp2` or peer-bit site. -/
theorem segSites : Assumption.SegSites asms
    (Assumptions.swExp2Sites ++ Assumptions.peerBitSites) := by
  seg_sites

/-- No segment at the correction code. -/
theorem segFree {pc : Nat} (h : 3700 ≤ pc) : Assumption.SegFreePc asms pc :=
  segSites.pc (by
    simp only [Assumptions.swExp2Sites, Assumptions.peerBitSites, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    omega)

/-- `mul.f32x2` and `setp.f32` are exact at the correction code. -/
theorem idealAt {f : Assumption.FloatForm} (hf : f = .mulF32x2 ∨ f = .setp .f32 ∨
    f = .cvtRnF16x2F32) {L : Launch} {g : Nat} {t : TState} (h : 3700 ≤ t.pc) :
    Assumption.IdealAt asms f L g t := by
  show Assumption.IdealAt (Assumption.idealReal _ _ _ :: _) f L g t
  exact Assumption.idealAt_head (by rcases hf with rfl | rfl | rfl <;> decide)
    (segFree h).tail

/-- At the correction code a floating form the ideal rule declines takes the Core rule. -/
theorem declineAt {f : Assumption.FloatForm} {L : Launch} {g : Nat} {t : TState}
    (h : 3700 ≤ t.pc) : DeclineAt asms f L g t := by
  intro op hf hn
  rw [(segFree h).exec rfl, execLocalRule_of_none]
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Assumptions.idealArith, Assumption.idealReal, hf]
    split_ifs
    · exact hn
    · rfl
  · rfl
  · exact Assumption.approxExact_localRule_none fun f' h' => by
      rw [Flow.approxForm_none_of_float hf] at h'; cases h'
  all_goals rfl

/-- At the correction code `rcp.approx.f32` is the exact reciprocal (ASM-APPROX) on a finite
operand and takes the Core rule on another. -/
theorem approxAt_rcp {L : Launch} {g : Nat} {t : TState} (h : 3700 ≤ t.pc) :
    ApproxAt asms (.rcp .f32) L g t ∧ ApproxDeclineAt asms (.rcp .f32) L g t := by
  have key : ∀ op, Assumption.ApproxForm.ofOp op = some (.rcp .f32) →
      execLocalA asms L g t op = match Assumption.execApproxExact t op with
        | some r => r
        | none => execLocal L g t op := by
    intro op hf
    rw [(segFree h).exec rfl]
    have h1 : Assumptions.idealArith.localRule L g t op = none :=
      Assumption.idealReal_localRule_none fun f' h' => by
        rw [Flow.floatForm_none_of_approx hf] at h'; cases h'
    have h3 : Assumptions.approx.localRule L g t op = Assumption.execApproxExact t op :=
      Assumption.approxExact_localRule_of hf (by simp)
    simp only [execLocalRule, asms, Assumptions.all, List.findSome?, h1, h3]
    rcases Assumption.execApproxExact t op with _ | r <;> rfl
  exact ⟨fun op hf e he => by rw [key op hf, he], fun op hf he => by rw [key op hf, he]⟩

/-- The pack `mov.b64 d, {r, r}` of the reciprocal of `l` at the correction code, between facts
by the role's table. -/
theorem seg_packRecip {L : Launch} {g pc dst src : Nat} {d : D} {liveT : List Nat}
    (hc : kernel.code[pc]? = some ⟨none, .move ⟨.pack, .int .b 64, [some dst],
      [.reg src, .reg src]⟩⟩) (hpc : 3700 ≤ pc) (hs : valueOf L g d src = recipV d.aw)
    (hsl : src ∈ Flow.live pc) (hd : valueOf L g d dst = fcPair d)
    (hcov : ∀ r ∈ liveT, r = dst ∨ (r ≠ dst ∧ r ∈ Flow.live pc)) :
    Seg kernel asms L g 1 pc (factsAt L g pc d) (pc + 1)
      (Flow.factsFrom liveT (valueOf L g d)) := by
  have hD := SegD.one (K := kernel) (A := asms) (L := L) (g := g) (E := packE (recipV d.aw)
      (recipV d.aw)) (d := dst) (liveS := Flow.live pc) (liveT := liveT) (v := valueOf L g d)
    hc rfl (fun t ht => by
      have hr : t.regs src = some (recipV d.aw) := by
        rw [← hs]; exact holds_mem ht.2.2.2.2 (mem_factsFrom hsl)
      rw [exec_pack (fun _ _ _ _ _ _ => asms_localRule_none) hr hr (segFree (ht.1 ▸ hpc))]
      simp [packE, recipV_bytes, Except.map])
    (fun x hx _ => by rw [hd, packE_eq hx]; rfl) hcov
  intro t ht
  exact (hD t ht).1 (packE_ok (recipV_bytes _) (recipV_bytes _))

/-- A load the data-flow assumption selects has the implicit wait. -/
theorem tcLdWait_of {pc : Nat} (h : Assumptions.tcLd.tcLdWait pc = true) :
    asms.any (·.tcLdWait pc) = true :=
  List.any_eq_true.mpr ⟨_, by simp [asms, Assumptions.all], h⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The loads of the rescale have the implicit wait. -/
theorem tcLdWait_rld (st : Fin 2) (j : Fin 8) :
    asms.any (·.tcLdWait (Site.rld st j).pc) = true := by
  apply tcLdWait_of
  fin_cases st <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The loads of the final normalization have the implicit wait. -/
theorem tcLdWait_fld (st : Fin 2) (j : Fin 8) :
    asms.any (·.tcLdWait (Site.fld st j).pc) = true := by
  apply tcLdWait_of
  fin_cases st <;> fin_cases j <;> decide +kernel

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
