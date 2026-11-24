-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTmemLoads
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part133
import Kernels.TmlFa4Fwd.Flow.Code.Part134
import Kernels.TmlFa4Fwd.Flow.Code.Part135
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Flow.Code.Part138
import Kernels.TmlFa4Fwd.Flow.Code.Part139
import Kernels.TmlFa4Fwd.Flow.Code.Part140
import Kernels.TmlFa4Fwd.Flow.Code.Part141

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem finalizeWaitCode (stage : Fin 2) (chunk : Fin 16) :
    kernel.code[finalizeLoadPc stage chunk + 5]? = some ⟨none, .tcWaitLd⟩ := by
  fin_cases stage <;> fin_cases chunk
  · exact Flow.code_8485
  · exact Flow.code_8504
  · exact Flow.code_8523
  · exact Flow.code_8542
  · exact Flow.code_8560
  · exact Flow.code_8577
  · exact Flow.code_8594
  · exact Flow.code_8611
  · exact Flow.code_8628
  · exact Flow.code_8645
  · exact Flow.code_8662
  · exact Flow.code_8679
  · exact Flow.code_8696
  · exact Flow.code_8713
  · exact Flow.code_8730
  · exact Flow.code_8747
  · exact Flow.code_8781
  · exact Flow.code_8800
  · exact Flow.code_8819
  · exact Flow.code_8838
  · exact Flow.code_8856
  · exact Flow.code_8873
  · exact Flow.code_8890
  · exact Flow.code_8907
  · exact Flow.code_8924
  · exact Flow.code_8941
  · exact Flow.code_8958
  · exact Flow.code_8975
  · exact Flow.code_8992
  · exact Flow.code_9009
  · exact Flow.code_9026
  · exact Flow.code_9043

/-- The finalization wait has a fixed callback and needs no data operands. -/
theorem finalizeWaitTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (stage : Fin 2) (chunk : Fin 16) {g : Nat} {t : TState} {F : List (Nat × Value)}
    (ht : At t (finalizeLoadPc stage chunk + 5) F) :
    out kernel Assumptions.all l g t = .ev (.tc .waitLd (next t)) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  rw [out_event ht.2.2.2.1 (ht.1.symm ▸ finalizeWaitCode stage chunk) rfl rfl]
  change Out.ev (tcTmpl l g t .tcWaitLd) = _
  simp [tcTmpl, hBlock, ofExec, pure, Except.pure]

/-- The explicit wait in every output chunk follows its four pack instructions. -/
theorem observeFinalizeWait {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g pos : Nat} {t : TState} {F : List (Nat × Value)} (hp : Pre p l m)
    (stage : Fin 2) (chunk : Fin 16) (ht : At t (finalizeLoadPc stage chunk + 5) F)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    X.get (g, pos) = some ⟨finalizeLoadPc stage chunk + 5, .tc .waitLd⟩ ∧
    At (next t) (finalizeLoadPc stage chunk + 6) F ∧
    Run kernel Assumptions.all l g (next t) ((X.tr g).drop (pos + 1)) none := by
  have hn : Next kernel Assumptions.all l g t t (.tc .waitLd (next t)) :=
    ⟨.refl,finalizeWaitTemplate hp stage chunk ht⟩
  obtain ⟨_, _, he, hFire, hTail⟩ := hn.continuing_at (by
    rintro _ ⟨_, hBad⟩
    cases hBad) hr
  obtain ⟨rfl, hu⟩ := hFire
  obtain rfl := Option.some.inj hu
  exact ⟨ht.1 ▸ he, ht.next, hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
