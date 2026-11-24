-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Async
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InputBytes
public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global
import Kernels.TmlFa4Fwd.Proof.Lib.GlobalWrites
import Lemmas.Flow.NotAsyncWait
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The sources of the input copies

The TMA copies' sources are fixed when the input arrays are not written (`tensorSources`). The
`cp.async` copies are whole 16-byte copies of no group wait (`cpSources`); their sources are
bytes of the K/V caches (`cpInputs`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The `cp.async` copies read initialized bytes of the input arrays.** -/
def CpInputs (p : Params) (m : Mem0) (X : Execution) : Prop :=
  ∀ i s, X.Copy i s → ∀ k < s.src.size, m (s.src.loc.at k) ≠ none ∧
    ∃ r ∈ p.inputRegions, r.Contains (s.src.loc.at k)

/-- **The row copies' sources are input bytes.** -/
theorem cpInputs (hp : Pre p L m) (hS : CpSrc p X) : CpInputs p m X := by
  intro i s hi k hk
  have hl : s.src.Covers (s.src.loc.at k) := by
    refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only [Loc.at] <;> omega
  obtain ⟨page, hpg, h, hh, r, hr, d, hd, y, hy, he⟩ := hS i s _ hi hl
  have hval : ∀ {l : Loc} {v : Value} {y : Nat}, HasValue m l v → y < v.bytes →
      m (l.at y) ≠ none := fun h hy hn => by rw [h _ hy] at hn; cases hn
  obtain ⟨hkv, hvv⟩ := hp.kvBytes page hpg h hh r hr d hd
  have hreg : ∀ c : CacheLayout, c ∈ [p.kLayout, p.vLayout] →
      (c.region p.pages p.kvHeads).Contains ((c.loc page h r d).at y) := by
    intro c _
    have h1 := Nat.mul_le_mul_right c.pageStride (show page ≤ p.pages - 1 by omega)
    have h2 := Nat.mul_le_mul_right c.headStride (show h ≤ p.kvHeads - 1 by omega)
    have h3 := Nat.mul_le_mul_right c.rowStride (show r ≤ 15 by omega)
    refine ⟨rfl, rfl, ?_, ?_⟩ <;>
      simp only [CacheLayout.region, CacheLayout.loc, globalLoc, Loc.at] <;> omega
  rcases he with he | he <;> rw [he]
  · exact ⟨hval hkv hy, _, by simp [Params.inputRegions], hreg p.kLayout (by simp)⟩
  · exact ⟨hval hvv hy, _, by simp [Params.inputRegions], hreg p.vLayout (by simp)⟩

/-- **The TMA copies' sources are fixed.** -/
theorem tensorSources (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hIn : InputsUnwritten p X) : TensorSources L m X := by
  intro i addr s hi
  obtain ⟨pc, he⟩ := id hi
  obtain ⟨-, j, org, mb, -, rfl⟩ := input_box hp hX hFw he
  refine ⟨actualTensorRoute hX hi, ?_, ?_, ?_⟩
  · obtain ⟨-, -, -, -, hBias, -⟩ := hp.maps 11 p.biasMapAddress ⟨2, p.biasMap⟩ (by simp)
    obtain ⟨-, -, -, -, hQ, -⟩ := hp.maps 9 p.qMapAddress ⟨2, p.qMap⟩ (by simp)
    show TensorDescriptor.Valid (Loader.inputMap p (Loader.inputSite j))
    unfold Loader.inputMap
    split
    · exact hBias
    · exact hQ
  · rw [input_bytes hp hX hFw he]; decide
  · intro slot a hsrc
    rcases input_source hp hIn (org := org) slot with ⟨a', ha, hm, hun⟩ | ⟨ha, -⟩
    · have hga : TensorBox.globalAddress (inputSpec p L (i.1 / L.block) j org mb).toTensorBox
          slot = some a' := ha
      simp only [TensorCopy.source, hga, TensorTransfer.Source.global.injEq] at hsrc
      subst hsrc
      exact ⟨_, hm, hun⟩
    · have hga : TensorBox.globalAddress (inputSpec p L (i.1 / L.block) j org mb).toTensorBox
          slot = none := ha
      simp [TensorCopy.source, hga] at hsrc

private theorem noAsyncWait : kernel.code.all (fun ins => !Flow.asyncWaitOp ins.op) = true := by
  decide +kernel

/-- **The `cp.async` copies' sources are fixed**, when they are input bytes. -/
theorem cpSources (hX : Consistent L kernel Assumptions.all m X) (hIn : InputsUnwritten p X)
    (hcp : CpInputs p m X) : Sched.CpSources m X := by
  intro i s hi
  have hs := actualCopyShape hX hi
  refine ⟨hs.completion, hs.whole, hs.noData, ?_, hs.srcSize, fun k hk => (hcp i s hi k hk).1,
    fun k hk w t bs hw => ?_⟩
  · rintro (mode | _) w hgw
    · exact not_bulkWaitsFor_of_copy hi (by rw [hs.completion]; simp) hgw
    · obtain ⟨pc, n, hget, -⟩ : AsyncGroupWaitsFor X i w := hgw
      exact no_kind_of_code hX asyncWaitOp (fun k => ∃ n, k = .asyncWait n)
        (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, h⟩ => fires_asyncWait_op hf h) noAsyncWait hget
        ⟨n, rfl⟩
  · obtain ⟨-, r, hr, hc⟩ := hcp i s hi k hk
    exact hIn r hr _ hc w t bs hw

end PTX.Kernels.TmlFa4Fwd.Proof
