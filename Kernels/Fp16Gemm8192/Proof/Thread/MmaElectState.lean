-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.MmaLeader
public import Kernels.Fp16Gemm8192.Proof.Thread.ClusterStart
public import Kernels.Fp16Gemm8192.Proof.Thread.Tracked

@[expose] public section

/-! # An elected MMA lane's final state is an MMA state

An elected lane of a leader CTA's warp 8 or 9 has its election at event 6 (`elect_index`), fired
from a role state: a prologue state there would be an election only at warp 0 or warp 11
(`Prologue.Canon`). After the election the MMA states go on (`stateAt_seven`, `mma_run`), so the
lane's state at the end of its trace is an MMA state or none. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
/-- **The state of an elected MMA lane at the end of its trace.** -/
theorem mma_elect_state {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g j pc mask inst : Nat}
    (hg : g < L.threads) (hl : g / L.block % 2 = 0)
    (hw : g % L.block / 32 = 8 ∨ g % L.block / 32 = 9)
    (hel : X.Elect (g, j) pc mask inst (laneOf L g)) :
    Frame.stateAt (code L) X g (X.tr g).length = none ∨
      ∃ m, Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) := by
  have hj6 := elect_index hpre hX hg hw hl hel
  subst hj6
  have hE : X.get (g, 6) = some ⟨pc, .elect mask inst (laneOf L g)⟩ := hel
  have hlen : 6 < (X.tr g).length := (List.getElem?_eq_some_iff.mp
    (show (X.tr g)[6]? = some ⟨pc, .elect mask inst (laneOf L g)⟩ from hE)).1
  obtain ⟨e6, he6⟩ : ∃ e, (X.tr g)[6]? = some e := ⟨_, List.getElem?_eq_getElem hlen⟩
  have hget : X.get (g, 6) = some e6 := he6
  have he6eq : e6 = ⟨pc, .elect mask inst (laneOf L g)⟩ := Option.some.inj (hget.symm.trans hE)
  -- the state before the election is a live state
  obtain ⟨σ, hσ⟩ : ∃ σ, Frame.stateAt (code L) X g 6 = some σ := by
    rcases (Frame.trace (fun _ => sound hpre) hX hg).fired hget with ⟨τ, -, ha, -⟩ | ⟨-, hub⟩
    · exact ⟨τ, ha⟩
    · obtain ⟨pc', f, hf⟩ := hub
      subst hf
      cases he6eq
  obtain ⟨d, hd⟩ : ∃ d, Frame.stateAt (code L) X g 6 = some (some d) := by
    cases σ with
    | none => exact absurd hσ (tracked hpre hX g 6 hg)
    | some d => exact ⟨d, hσ⟩
  -- the pre-state of the election is an MMA state
  obtain ⟨m6, hm6⟩ : ∃ m6, Frame.stateAt (code L) X g 6 = some (some (.inr (.mma m6))) := by
    cases d with
    | inl p =>
      exfalso
      obtain ⟨-, hwp, hcp⟩ := (onPath_all hpre hX hg 6 (by omega)).1 p hd
      have hwarp : p.w = g % L.block / 32 := by
        rw [hwp (by omega)]
      have hk : e6.kind = .elect mask inst (laneOf L g) := by rw [he6eq]
      by_cases hs : p.site = .elect
      · have hw0 := hcp.1 (Or.inl hs)
        omega
      · by_cases hs' : p.site = .roleElect
        · have hw11 := hcp.2.2.2.2 hs'
          omega
        · exact prologue_not_elect hpre hX hg hget hd hs hs' mask inst (laneOf L g) hk
    | inr r =>
      have hrw := role_warp hpre hX hg 6 (by omega) r hd
      cases r with
      | loader l =>
        simp only [roleWarp, Prologue.warpOf] at hrw
        omega
      | sched s =>
        simp only [roleWarp, Prologue.warpOf] at hrw
        omega
      | cons c =>
        simp only [roleWarp, Prologue.warpOf] at hrw
        omega
      | mma m6 => exact ⟨m6, hd⟩
  have hs7 := stateAt_seven hm6 he6
  have hrun := mma_run hs7 ((X.tr g).length - 7)
  rw [show 7 + ((X.tr g).length - 7) = (X.tr g).length by omega] at hrun
  rcases hrun (by omega) with h | ⟨m, hm, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨m, hm⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof
