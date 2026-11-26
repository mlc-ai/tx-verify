-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NoUb
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ref

@[expose] public section

/-! # The control words of a state of warpgroup 0 at its ring and pointer sites

`w0State_of_ref`: the reference invariant of a state (`RefCore`: the ring words are those of the
block it is in) and the launch facts (`LaunchOk`) give the slot words and the length pointers
`w0_nonub` needs (`W0State`), with the sink pointer a hypothesis (only the step from the
`setmaxnreg` reaches the sink load, and only when the pointer is set: `afterSmr_sink`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem w0State_of_ref {d : Control.D} {n : Cnt → Nat} (hc : RefCore L g d n)
    (hL : LaunchOk P L g d) (hsink : d.site = .sink → eqz64 (pw8 (P.sinkBase.getD 0)) = false) :
    W0State P d := by
  refine ⟨fun hs => ?_, fun hs => ?_, hsink, fun h => hL.1 h, fun h => hL.2.1 h⟩
  · have hr : d.site.reg = .loop := by rcases hs with h | h | h <;> simp [h, Site.reg]
    unfold RefCore RefAt at hc
    rw [hr] at hc
    obtain ⟨r, ⟨-, -, -, -, -, hv, -⟩, -⟩ := hc
    exact ⟨r % 4, Nat.mod_lt _ (by norm_num), hv⟩
  · rcases hs with hs | hs | hs
    · have hr : d.site.reg = .loop := by simp [hs, Site.reg]
      unfold RefCore RefAt at hc
      rw [hr] at hc
      obtain ⟨r, ⟨-, -, -, -, -, -, -, hv, -⟩, -⟩ := hc
      exact ⟨r % 2, Nat.mod_lt _ (by norm_num), hv⟩
    · have hr : d.site.reg = .loop := by simp [hs, Site.reg]
      unfold RefCore RefAt at hc
      rw [hr] at hc
      obtain ⟨r, ⟨-, -, -, -, -, -, -, hv, -⟩, -⟩ := hc
      exact ⟨r % 2, Nat.mod_lt _ (by norm_num), hv⟩
    · have hr : d.site.reg = .epi := by simp [hs, Site.reg]
      unfold RefCore RefAt at hc
      rw [hr] at hc
      obtain ⟨⟨hv, -⟩, -⟩ := hc
      exact ⟨_, Nat.mod_lt _ (by norm_num), hv⟩

theorem afterSmr_sink {d : Control.D} (h : (Control.afterSmr P L g w d).site = .sink) :
    eqz64 (pw8 (P.sinkBase.getD 0)) = false := by
  unfold Control.afterSmr at h
  by_cases hc : (eqz64 (pw8 (P.sinkBase.getD 0)) || scmp .ge .s (Control.r10W L g) (pw 64)) = true
  · simp only [hc, ↓reduceIte] at h
    unfold Control.afterSink Control.finish Control.afterA at h
    split_ifs at h
  · simp only [Bool.or_eq_true, not_or] at hc
    simpa using hc.1

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
