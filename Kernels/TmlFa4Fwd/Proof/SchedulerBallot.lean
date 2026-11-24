-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part045
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Lemmas.Arith.WarpPrefix
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Local
public import Lemmas.Flow.SegChain
public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry
public import Kernels.TmlFa4Fwd.Proof.SchedulerArith

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- Popcount of a ballot containing exactly the lanes before a given lane. -/
theorem ballotPrefixPopcount {n : Nat} (hn : n ≤ 32) :
    ((List.range 32).filter (2 ^ n - 1).testBit).length = n := by
  have hn32 : 32 = n + (32 - n) := by omega
  conv_lhs => rw [hn32, List.range_add]
  rw [List.filter_append]
  have hTake : (List.range n).filter (2 ^ n - 1).testBit = List.range n := by
    apply List.filter_eq_self.mpr
    simp [Nat.testBit_two_pow_sub_one]
  have hDrop : ((List.range (32 - n)).map (n + ·)).filter (2 ^ n - 1).testBit = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    simp [Nat.testBit_two_pow_sub_one]
  simp [hTake, hDrop]

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
