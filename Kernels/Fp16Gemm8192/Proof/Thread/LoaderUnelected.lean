-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.MmaUnelected
public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # The loader warp's path to its role election

A thread of warp 11 runs the common prologue (its shuffle, its fence, its arrival and wait at the
cluster barrier, its register count) and then reaches its role election (`Prologue.roleElect`,
time 56). The first five prologue steps are those of warps 8 and 9 (`mmaPath1`–`mmaPath5`). A
seventh event would fire the role election's template, and the full mask in its register makes that
template an election event. So a warp-11 thread without an election event has at most six events,
and its final state is a prologue state (no exit, time at most 56). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxHeartbeats 4000000 in
/-- The register count of warp 11 is followed by its role election. -/
theorem loaderPath6 (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat}
    (hg : g < L.threads) (hw : Prologue.warpOf L g = 11) (h5 : 5 < (X.tr g).length) :
    Frame.stateAt (code L) X g 6 = some (some (.inl ⟨.roleElect, Prologue.warpOf L g⟩)) := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[5]? = some e := ⟨_, List.getElem?_eq_getElem h5⟩
  show Frame.stateAt (code L) X g (5 + 1) = _
  rw [stateAt_succ_inl he (mmaPath5 hpre hX hg (by omega) (by omega) (by omega))]
  simp [Prologue.next, hw]

set_option maxHeartbeats 8000000 in
/-- **A warp-11 thread without an election is before its role election.** Its trace has at most six
events, and its final state is a prologue state with no exit and time at most 56. -/
theorem loader_unelected_thm (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ∀ {g : Nat}, g < L.threads → g % L.block / 32 = 11 →
    (∀ j pc mask inst leader, ¬ X.Elect (g, j) pc mask inst leader) →
    ∃ d, Frame.stateAt (code L) X g (X.tr g).length = some (some d) ∧ (∃ p, d = .inl p) ∧
      d.exitOff = none ∧
      d.vtime L g (X.tr g) ≤ 56 := by
  intro g hg hw hnoel
  have hw11 : Prologue.warpOf L g = 11 := hw
  -- A seventh event would fire the role election's template, which the full mask makes an election.
  have hn6 : (X.tr g).length ≤ 6 := by
    by_contra hlt
    obtain ⟨e6, he6⟩ : ∃ e, (X.tr g)[6]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hm6 := loaderPath6 hpre hX hg hw11 (by omega)
    obtain ⟨t, ins, _, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he6 hm6
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_1)
    have hmask : readBits L g t 32 (.reg 649) = .ok (BitVec.ofNat 64 4294967295) :=
      readBits_b32 (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom
        (show 649 ∈ Flow.live Prologue.Site.roleElect.pc by table_decide))) (by decide)
    obtain ⟨inst, leader, rfl⟩ := fires_elect_full hmask (by decide) hfire
    exact hnoel 6 _ 4294967295 inst leader he6
  rcases (show (X.tr g).length = 0 ∨ (X.tr g).length = 1 ∨ (X.tr g).length = 2 ∨
      (X.tr g).length = 3 ∨ (X.tr g).length = 4 ∨ (X.tr g).length = 5 ∨
      (X.tr g).length = 6 by omega) with h | h | h | h | h | h | h
  · refine ⟨.inl ⟨.shfl, 0⟩, ?_, ⟨_, rfl⟩, rfl, ?_⟩
    · rw [h]
      exact stateAt_zero L X g
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inl ⟨.fence, Prologue.warpOf L g⟩, ?_, ⟨_, rfl⟩, rfl, ?_⟩
    · rw [h]
      exact mmaPath1 hpre hX hg (by omega) (by omega)
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inl ⟨.fenceInit, Prologue.warpOf L g⟩, ?_, ⟨_, rfl⟩, rfl, ?_⟩
    · rw [h]
      exact mmaPath2 hpre hX hg (by omega) (by omega)
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inl ⟨.arrive, Prologue.warpOf L g⟩, ?_, ⟨_, rfl⟩, rfl, ?_⟩
    · rw [h]
      exact mmaPath3 hpre hX hg (by omega) (by omega)
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inl ⟨.wait, Prologue.warpOf L g⟩, ?_, ⟨_, rfl⟩, rfl, ?_⟩
    · rw [h]
      exact mmaPath4 hpre hX hg (by omega) (by omega)
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inl ⟨.setMaxReg, Prologue.warpOf L g⟩, ?_, ⟨_, rfl⟩, rfl, ?_⟩
    · rw [h]
      exact mmaPath5 hpre hX hg (by omega) (by omega) (by omega)
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inl ⟨.roleElect, Prologue.warpOf L g⟩, ?_, ⟨_, rfl⟩, rfl, ?_⟩
    · rw [h]
      exact loaderPath6 hpre hX hg hw11 (by omega)
    · simp [ThreadD.vtime, Prologue.Site.vtime]

end
end PTX.Kernels.Fp16Gemm8192.Proof
