-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.InputIssues
public import Kernels.Fp16Gemm8192.Proof.Thread.ProgressFacts

@[expose] public section

/-! # The Tensor Core instructions' operands

Static facts of the MMA thread's sites. An MMA writes the accumulator of its warp's buffer, at
column `256 * (w % 2)` of the Tensor Memory, with no output lane masked (`mma_dst_fact`). A commit
is the MMA thread's, on a leader CTA: a slot's commit to its input empty barrier, or the
accumulator commit to its buffer's full barrier, both multicast to the CTA pair
(`commit_spec_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An MMA writes its warp's accumulator buffer, at column `256 * (w % 2)`, unmasked. -/
theorem mma_dst_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {e : Event} {d : ThreadD} {dst : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) (hk : e.kind = .tc (.mma dst sp acc mask)) :
    dst = 256 * (g % L.block / 32 % 2) ∧ mask = List.replicate 8 0 := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  obtain ⟨m, s, j, rfl, hs⟩ := mma_state (OpPcsFast.mem kernel_mma_pcs hc (fires_tcMma_op hfire hk))
  have he' := Mma.mma_event hpre hg s j hs hat hc hfire
  rw [he'] at hk
  simp only [Kind.tc.injEq, TcKind.mma.injEq] at hk
  obtain ⟨rfl, -, -, rfl⟩ := hk
  have hw := role_warp hpre hX hg k (List.getElem?_eq_some_iff.mp he).1.le _ hσ
  simp only [roleWarp] at hw
  exact ⟨by rw [hw.1], rfl⟩

set_option maxHeartbeats 4000000 in
/-- A commit is the MMA thread's, on a leader CTA: a slot's input commit or its accumulator
commit, both to its own CTA's barrier with the pair's mask. -/
theorem commit_spec_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {e : Event} {d : ThreadD} {sp : TcCommit.Spec} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k = some (some d))
    (hk : e.kind = .tc (.commit sp)) :
    ∃ m : Mma.D, d = .inr (.mma m) ∧ g / L.block % 2 = 0 ∧
      ((∃ s : Fin 4, m.site = .commit s ∧
          sp = ⟨.two, ⟨.shared, g / L.block, L.sharedBase + 40 + 8 * s.val⟩, 3,
            g / L.block / 2 * 2, 2⟩) ∨
        (m.site = .accCommit ∧ sp = ⟨.two, ⟨.shared, g / L.block,
          L.sharedBase + 8 * (g % L.block / 32 % 2) + 72⟩, 3, g / L.block / 2 * 2, 2⟩)) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  obtain ⟨m, rfl, hsite⟩ := commit_role hat hc hfire hk
  have hlead : Mma.Lead L g m := hinv.2.2
  refine ⟨m, rfl, ?_⟩
  rcases hsite with ⟨s0, hs0⟩ | hacc
  · obtain rfl := Mma.commit_event hpre hg s0 hs0 hat hc hfire
    have hsp : Mma.commitSpec L g s0 = sp := TcKind.commit.inj (Kind.tc.inj hk)
    subst hsp
    refine ⟨?_, .inl ⟨s0, hs0, rfl⟩⟩
    rcases hlead with h | h | h | h <;> first | exact h | simp [hs0] at h
  · obtain rfl := Mma.accCommit_spec hpre hg hacc hat hc hfire
    have hsp : Mma.accSpec L g m.w = sp := TcKind.commit.inj (Kind.tc.inj hk)
    subst hsp
    have hw := role_warp hpre hX hg k (List.getElem?_eq_some_iff.mp he).1.le _ hσ
    simp only [roleWarp] at hw
    refine ⟨?_, .inr ⟨hacc, ?_⟩⟩
    · rcases hlead with h | h | h | h <;> first | exact h | simp [hacc] at h
    · simp only [Mma.accSpec, hw.1]

end

end PTX.Kernels.Fp16Gemm8192.Proof
