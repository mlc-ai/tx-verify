-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ProgressFacts

@[expose] public section

/-! # The accumulator commits' targets

An accumulator commit of an MMA thread of a leader CTA notifies its buffer's accumulator-full
barrier in both CTAs of the cluster: rank `r < 2` targets the barrier of CTA `g / L.block + r`,
since the commit's mask selects both ranks and its cluster base is the leader's (`Mma.accSpec`).
This is the accumulator analogue of `commit_ranks_fact`, the input commits' targets. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
/-- An accumulator commit of an MMA thread `g` of a leader CTA, to the accumulator-full barrier of
buffer `j`, targets that barrier in CTA `g / L.block + r` at rank `r < 2`. -/
theorem acc_commit_ranks_fact {P : Params} {L : Launch} {mem0 : Mem0} {g k : Nat} {X : Execution}
    {e : Event} {d : ThreadD} {sp : TcCommit.Spec} {j : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads)
    (rank : Fin 16) (he : X.get (g, k) = some e)
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) = some (some d))
    (hk : e.kind = .tc (.commit sp)) (hm : sp.mbar = Bar.loc L (g / L.block) ⟨.acc, j.val, true⟩)
    (hr : rank.val < 2) :
    TcCommit.target sp rank = some (Bar.loc L (g / L.block + rank.val) ⟨.acc, j.val, true⟩) := by
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  obtain ⟨m, rfl, hsite⟩ := commit_role hat hc hfire hk
  rcases hsite with ⟨s0, hs0⟩ | hacc
  · -- an input commit targets an input empty barrier, never the accumulator-full barrier
    obtain rfl := Mma.commit_event hpre hg s0 hs0 hat hc hfire
    have hsp : Mma.commitSpec L g s0 = sp := TcKind.commit.inj (Kind.tc.inj hk)
    subst hsp
    exfalso
    have h1 := congrArg Loc.addr hm
    simp [Mma.commitSpec, Bar.loc, Bar.off] at h1
    have := s0.isLt
    have := j.isLt
    omega
  · -- the accumulator commit: its specification is `accSpec` of the thread's warp
    obtain rfl := Mma.accCommit_spec hpre hg hacc hat hc hfire
    have hsp : Mma.accSpec L g m.w = sp := TcKind.commit.inj (Kind.tc.inj hk)
    subst hsp
    have hjw : m.w % 2 = j.val := by
      have h1 := congrArg Loc.addr hm
      simp [Mma.accSpec, Bar.loc, Bar.off] at h1
      have := j.isLt
      omega
    have heven : g / L.block % 2 = 0 := by
      have hlead : Mma.Lead L g m := hinv.2.2
      rcases hlead with h | h | h | h <;> first | exact h | simp [hacc] at h
    have hcond : rank.val < (Mma.accSpec L g m.w).clusterSize ∧
        (Mma.accSpec L g m.w).mask.toNat / 2 ^ rank.val % 2 = 1 := by
      have : rank.val = 0 ∨ rank.val = 1 := by omega
      rcases this with h | h <;> simp [Mma.accSpec, h]
    have hev2 : g / L.block / 2 * 2 = g / L.block := by omega
    unfold TcCommit.target
    simp only [hcond.1, hcond.2, and_self, ↓reduceIte]
    simp [Mma.accSpec, Bar.loc, Bar.off, hjw, hev2, Nat.add_assoc]
    try omega

end
end PTX.Kernels.Fp16Gemm8192.Proof
