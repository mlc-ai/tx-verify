-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLive
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Bar
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Ev

@[expose] public section

/-! # An index lane's states

For the index warp's time exports (`Index/Export/Time.lean`, which imports this file privately):
under `Follow`, a state of a lane of warp 7 at any prefix of its trace is a startup state before
time `100` (`glue_gate`), a state of warpgroup 1's head (time at most `102`) or an index
state with the role's reference invariant at an element of its site (`ix_state`); the state
behind an `exit` of such a lane is the index warp's exit, with the reference invariant at the
prefix counts and the CTA's block count (`ix_exit_at`); the machine moves on at its arrivals
(`ix_arr_next`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A state of a lane of warp 7**: before time `103`, or an index state with the role's
reference invariant at its counts. -/
theorem ix_state (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g = 7) (hg : g < L.threads)
    {i : Nat} {σ : (thread P L g).D} (hσ : Frame.stateAt (thread P L) X g i = some (some σ)) :
    time P L g σ ≤ 102 ∨ ∃ d n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n) ∧
      (n .ub = 0 → Index.Ref P L g d (fun c => n (.index c))) ∧ d.el < d.site.elems := by
  have hJ := (follow_iff.mp hFw g hg i).2 σ hσ
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨e | r, d⟩
  · left
    have hx : Startup.exitOf d = none := by simpa [startupEnter] using glue_gate hσ
    have := Startup.time_lt hx
    simp only [time]
    omega
  · cases e with
    | wg1 =>
      obtain ⟨-, hR, -, -⟩ := hJ
      rcases d with s | ⟨j | r, d⟩
      · left
        have := Wg1.time_le s
        simp only [time, fragTime, wg1Time, roleBase]
        omega
      · have hwo : warpOf L g = 7 := by simp only [warp] at hw; simp only [warpOf, tidOf]; omega
        cases j with
        | index =>
          obtain ⟨-, hel, -⟩ := ix_ok hp hX hσ d n rfl
          exact .inr ⟨d, n, rfl, hR.2.2, hel⟩
        | mma | tma => simp [wg1J, subOk, hwo] at hR
        | idle => simp [wg1J, subOk, hwo] at hR
      · exact hR.elim
    | wg0 | dequant =>
      obtain ⟨-, -, -, h⟩ := hJ
      simp only [Entry.wg, wgOf, tidOf] at h
      simp only [warp] at hw
      omega
  · exact hJ.elim

/-- **The state behind an `exit` of a lane of warp 7** is the index warp's exit, with the
reference invariant at the prefix counts and the CTA's block count. -/
theorem ix_exit_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g = 7) {k pc : Nat}
    (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    ∃ d : Index.D, Index.Ref P L g d (fun c => ((X.tr g).take k).countP (Index.cls c)) ∧
      d.site = .exit ∧ roundsOf d.c.l0 d.c.l1 = blocksOf P L (g / L.block) := by
  have h103 := startup_exit hp hX hFw he
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he (fun _ h => by cases h)
  have h := state_role hJ hi
  rw [← hpc] at h
  simp only at h
  cases h with
  | index d n hR _ hpc' hr =>
    have hE : Index.Ev P L g d ⟨pc, .exit⟩ := hev
    have hs : d.site = .exit := by
      obtain ⟨-, hk⟩ := hE
      obtain ⟨site, el, ac, c⟩ := d
      cases site <;> simp [Index.EvK, Index.NcEv, Index.NcAt, Index.PollEv, Index.ShflEv,
          Index.StoreEv] at hk ⊢
    refine ⟨d, ?_, hs, ix_rounds hp hX hσ (by rw [hs]; simp) (by rw [hs]; simp)⟩
    have hc : (fun c => n (.index c)) = fun c => ((X.tr g).take k).countP (Index.cls c) :=
      funext fun c => state_count hσ (.index c)
    rw [← hc]
    exact hR (state_ub hX hσ he)
  | startup _ _ _ _ _ _ hr => omega
  | head s _ hs =>
    have hE : Wg1.Ev L g s ⟨pc, .exit⟩ := hev
    rcases hs with rfl | rfl <;> simp [Wg1.Ev] at hE
  | idle _ _ _ hw' => simp only [warp] at hw; simp only [warpOf, tidOf] at hw'; omega
  | dequant _ _ _ hw' => omega
  | mma _ _ _ _ _ hw' => omega
  | tma _ _ _ _ _ hw' => omega
  | wg0 _ _ _ hw' => omega

/-- **The index warp's machine moves on at its arrivals.** -/
theorem ix_arr_next {d : Index.D} {n : Cls → Nat} {f : Event}
    (hs : d.site = .arrA ∨ d.site = .arrB) :
    (thread P L g).toMachine.next (some (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n)) f ≠
      none := by
  rcases hs with hs | hs <;>
    simp [Code.toMachine, Code.glue, Code.withStubs, Code.withStubsAt, frag, wg1Code,
      Code.roleLoop, Code.loopGlue, subFrag, indexCode, Index.succ, hs]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
