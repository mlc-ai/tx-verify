-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderTransparency
public import Kernels.TmlFa4Fwd.Flow.Code.Part010
public import Kernels.TmlFa4Fwd.Flow.Code.Part014
public import Kernels.TmlFa4Fwd.Flow.Code.Part017
public import Kernels.TmlFa4Fwd.Flow.Code.Part020
public import Kernels.TmlFa4Fwd.Flow.Code.Part025
public import Kernels.TmlFa4Fwd.Flow.Code.Part027
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Lemmas.Flow.LoadShared
public import Lemmas.Protocol.CpAsync

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The six decoded ordinary-copy group commits. -/
def copyCommitPc : Fin 6 → Nat
  | 0 => 673
  | 1 => 903
  | 2 => 1136
  | 3 => 1341
  | 4 => 1601
  | 5 => 1734

/-- The address operand of the no-increment arrival immediately after each commit. -/
def copyArrivalAddress : Fin 6 → Nat × Nat
  | 0 => (2535, 32)
  | 1 => (2535, 40)
  | 2 => (1122, 32)
  | 3 => (1141, 32)
  | 4 => (1151, 32)
  | 5 => (1171, 32)

theorem copyCommitCode (site : Fin 6) :
    kernel.code[copyCommitPc site]? = some ⟨none, .cpAsyncCommit⟩ ∧
    kernel.code[copyCommitPc site + 1]? = some
      ⟨none, .cpAsyncArrive true (copyArrivalAddress site).1
        (copyArrivalAddress site).2 false⟩ := by
  fin_cases site
  · exact ⟨Flow.code_673, Flow.code_674⟩
  · exact ⟨Flow.code_903, Flow.code_904⟩
  · exact ⟨Flow.code_1136, Flow.code_1137⟩
  · exact ⟨Flow.code_1341, Flow.code_1342⟩
  · exact ⟨Flow.code_1601, Flow.code_1602⟩
  · exact ⟨Flow.code_1734, Flow.code_1735⟩

/-- Resolve a loader group's commit and following no-increment arrival. -/
theorem copyCommitTemplates {l : Launch} (site : Fin 6) {g base : Nat} {t : TState}
    (ht : At t (copyCommitPc site) [((copyArrivalAddress site).1,b32 base)])
    (hBound : base+(copyArrivalAddress site).2 < 2^32) (hAlign : base%8 = 0) :
    let loc : Loc := ⟨.shared,g/l.block,base+(copyArrivalAddress site).2⟩
    out kernel Assumptions.all l g t = .ev (.asyncCommit (next t)) ∧
    out kernel Assumptions.all l g (next t) = .ev (.asyncArrive loc true (next (next t))) := by
  have hLo : 174 ≤ copyCommitPc site := by fin_cases site <;> decide
  have hHi : copyCommitPc site + 1 < 1901 := by fin_cases site <;> decide
  have hCode := copyCommitCode site
  have hStart : out kernel [] l g t = .ev (.asyncCommit (next t)) := by
    rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact hCode.1) rfl rfl]
    rfl
  have hAt := ht.next
  let loc : Loc := ⟨.shared, g / l.block, base + (copyArrivalAddress site).2⟩
  have hAddr : mbarLoc l g (next t) (copyArrivalAddress site).1 (copyArrivalAddress site).2 =
      .ok loc := by
    have hOff : (copyArrivalAddress site).2 % 8 = 0 := by fin_cases site <;> decide
    have hAligned : loc.addr % 8 = 0 := by dsimp [loc]; omega
    unfold mbarLoc
    rw [effAddr_b32_off hAt.2.2.2.2.1 hBound]
    simp [loc, hAligned, bind, Except.bind, pure, Except.pure]
  have hCore : out kernel [] l g (next t) = .ev (.asyncArrive loc true (next (next t))) := by
    rw [out_event hAt.2.2.2.1 (by rw [hAt.1]; exact hCode.2) rfl rfl]
    exact congrArg Out.ev (cpAsyncTmpl_arrive_noinc hAddr)
  exact ⟨(loaderOutCore (by rw [ht.1]; omega) (by rw [ht.1]; omega)).trans hStart,
    (loaderOutCore (by rw [hAt.1]; omega) (by rw [hAt.1]; omega)).trans hCore⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
