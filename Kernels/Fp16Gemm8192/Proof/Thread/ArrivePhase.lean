-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Fire
public import Kernels.Fp16Gemm8192.Proof.Thread.ClusterDefs
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaLeader
public import Lemmas.Flow.NotArrive

@[expose] public section

/-! # mbarrier arrivals come before the exit arrival

An mbarrier arrival is fired at a site of the arrival kind (`site_kindOp`), and no such site is in
a role's exit stage: the thread has made at most its first cluster arrival (`arrive_phase_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The sites of the arrival kind are before the exit stage. -/
theorem arrive_kind_phase {d : ThreadD} (h : nextKind d = .arrive) : d.clPhase ≤ 1 := by
  rcases d with p | (l | m | s | c)
  · cases hs : p.site <;> simp [nextKind, prologueKind, hs] at h
  · cases hs : l.site <;> simp [nextKind, loaderKind, hs, ThreadD.clPhase] at h ⊢
  · cases hs : m.site <;> simp [nextKind, mmaKind, hs, ThreadD.clPhase] at h ⊢
  · cases hs : s.site <;> simp [nextKind, schedKind, hs, ThreadD.clPhase] at h ⊢
  · cases hs : c.site <;> simp [nextKind, consKind, hs, ThreadD.clPhase] at h ⊢

/-- **An mbarrier arrival is before the thread's exit arrival.** -/
theorem arrive_phase_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) {k : Nat} {e : Event} {d : ThreadD}
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k = some (some d)) {m : Loc}
    {tx c : Nat} {rel : Bool} {sc : MbarScope} (hk : e.kind = .arrive m tx c rel sc) :
    d.clPhase ≤ 1 := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hop : arriveOp ins.op = true := by
    cases h : arriveOp ins.op
    · exact absurd hk (fires_notArrive (eventTmpl_notArrive (arriveOp_ne h)) hf _ _ _ _ _)
    · rfl
  have hk' := site_kindOp d hc
  apply arrive_kind_phase
  revert hk'
  cases hop' : ins.op <;> simp [arriveOp, hop'] at hop
  cases nextKind d <;> simp [kindOp]

end

end PTX.Kernels.Fp16Gemm8192.Proof
