-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Loader.Base
import Kernels.TmlFa4Fwd.Proof.Loader.StepsArrPrime
import Kernels.TmlFa4Fwd.Proof.Loader.StepsDrain
import Kernels.TmlFa4Fwd.Proof.Loader.StepsLw
import Kernels.TmlFa4Fwd.Proof.Loader.StepsPgPrime
import Kernels.TmlFa4Fwd.Proof.Loader.StepsPgSteady
import Kernels.TmlFa4Fwd.Proof.Loader.StepsPgWarm
import Kernels.TmlFa4Fwd.Proof.Loader.StepsPkEnd
import Kernels.TmlFa4Fwd.Proof.Loader.StepsPtP
import Kernels.TmlFa4Fwd.Proof.Loader.StepsPtR
import Kernels.TmlFa4Fwd.Proof.Loader.StepsPtS
import Kernels.TmlFa4Fwd.Proof.Loader.StepsReq
import Kernels.TmlFa4Fwd.Proof.Loader.StepsRowsPrimeK
import Kernels.TmlFa4Fwd.Proof.Loader.StepsRowsPrimeV
import Kernels.TmlFa4Fwd.Proof.Loader.StepsRowsSteadyK
import Kernels.TmlFa4Fwd.Proof.Loader.StepsRowsSteadyV
import Kernels.TmlFa4Fwd.Proof.Loader.StepsRowsWarmK
import Kernels.TmlFa4Fwd.Proof.Loader.StepsRowsWarmV
import Kernels.TmlFa4Fwd.Proof.Loader.StepsScanFirst
import Kernels.TmlFa4Fwd.Proof.Loader.StepsScanLoop
import Kernels.TmlFa4Fwd.Proof.Loader.StepsScanLoop2
import Kernels.TmlFa4Fwd.Proof.Loader.StepsScanSecond
import Kernels.TmlFa4Fwd.Proof.Loader.StepsSelect
import Kernels.TmlFa4Fwd.Proof.Loader.StepsSlot
import Kernels.TmlFa4Fwd.Proof.Loader.StepsTma
import Kernels.TmlFa4Fwd.Proof.Loader.StepsTmaCopy
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Gen.StepEarly

@[expose] public section

/-! # The loader warps' obligations

Every state of the loader's machine satisfies its step obligation (`stepAt`): the site files
prove them by `site_cases`, one theorem per kind of site, checked in parallel (the first block's V
arrival, the transition into the later blocks, by a segment cut in `StepsArrPrime.lean`); a state
at a sub-step its site does not have holds vacuously (`stepAt_junk`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

theorem stepAt (hp : Pre p L m) (hg : g < L.threads) (hw : w = 14 ∨ w = 15) (d : D) :
    (code p L g w ent).StepAt d := by
  obtain ⟨s, v, k⟩ := d
  by_cases hk : k = 0
  case neg =>
    cases s with
    | lw per b h => exact stepAt_lw hp hg hw _ ⟨per, b, h, rfl⟩
    | _ => exact stepAt_junk (by rintro (h | h) <;> first | exact hk h | exact h)
  subst hk
  cases s with
  | lw per b h => exact stepAt_lw hp hg hw _ ⟨per, b, h, rfl⟩
  | setmax => exact stepAt_scan_first hp hg hw _ rfl (by simp)
  | word sc | down sc | up sc _ | total sc =>
    cases sc
    · exact stepAt_scan_first hp hg hw _ rfl (by simp)
    · exact stepAt_scan_loop hp hg hw _ rfl (by simp)
    · exact stepAt_scan_second hp hg hw _ rfl (by simp)
    · exact stepAt_scan_loop2 hp hg hw _ rfl (by simp)
  | vote l | pre l => exact stepAt_select hp hg hw _ rfl (by simp)
  | tiles l =>
    cases l
    · exact stepAt_select hp hg hw _ rfl (.inr (.inr (.inr rfl)))
    · exact stepAt_select hp hg hw _ rfl (.inr (.inr (.inl rfl)))
  | q0 => exact stepAt_req hp hg hw _ rfl (.inl rfl)
  | q1 => exact stepAt_req hp hg hw _ rfl (.inr rfl)
  | uk => exact stepAt_pg_prime hp hg hw _ rfl (.inl rfl)
  | pgLd per it | pgSt per it | rwSt per it =>
    cases per
    · exact stepAt_pg_prime hp hg hw _ rfl (by simp)
    · exact stepAt_pg_warm hp hg hw _ rfl (by simp)
    · exact stepAt_pg_steady hp hg hw _ rfl (by simp)
  | slot per b => exact stepAt_slot hp hg hw _ rfl ⟨per, b, rfl⟩
  | ptP per b it => exact stepAt_ptP hp hg hw _ rfl ⟨per, b, it, rfl⟩
  | ptR per b it => exact stepAt_ptR hp hg hw _ rfl ⟨per, b, it, rfl⟩
  | ptS per b it => exact stepAt_ptS hp hg hw _ rfl ⟨per, b, it, rfl⟩
  | xl per b i | xh per b i | cp per b i _ =>
    cases per <;> cases b
    · exact stepAt_rows_primeK hp hg hw _ rfl (by simp)
    · exact stepAt_rows_primeV hp hg hw _ rfl (by simp)
    · exact stepAt_rows_warmK hp hg hw _ rfl (by simp)
    · exact stepAt_rows_warmV hp hg hw _ rfl (by simp)
    · exact stepAt_rows_steadyK hp hg hw _ rfl (by simp)
    · exact stepAt_rows_steadyV hp hg hw _ rfl (by simp)
  | commit per b => exact stepAt_pk_end hp hg hw _ rfl (.inl ⟨per, b, rfl⟩)
  | arrive per b =>
    by_cases hpb : per = .prime ∧ b = true
    · obtain ⟨rfl, rfl⟩ := hpb
      exact stepAt_arr_prime hp hg hw _ rfl rfl
    · exact stepAt_pk_end hp hg hw _ rfl (.inr ⟨per, b, rfl, hpb⟩)
  | tw t => exact stepAt_tma hp hg hw _ rfl (.inl ⟨t, rfl⟩)
  | te t e => exact stepAt_tma hp hg hw _ rfl (.inr (.inl ⟨t, e, rfl⟩))
  | ta t => exact stepAt_tma hp hg hw _ rfl (.inr (.inr ⟨t, rfl⟩))
  | tc t c => exact stepAt_tma_copy hp hg hw _ rfl ⟨t, c, rfl⟩
  | dw k' => exact stepAt_drain hp hg hw _ rfl (.inl ⟨k', rfl⟩)
  | dq => exact stepAt_drain hp hg hw _ rfl (.inr (.inl rfl))
  | de => exact stepAt_drain hp hg hw _ rfl (.inr (.inr (.inl rfl)))
  | da => exact stepAt_drain hp hg hw _ rfl (.inr (.inr (.inr (.inl rfl))))
  | exit => exact stepAt_drain hp hg hw _ rfl (.inr (.inr (.inr (.inr rfl))))

end PTX.Kernels.TmlFa4Fwd.Proof.Loader
