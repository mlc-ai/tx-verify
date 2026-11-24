-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaInitialValueSend
import Kernels.TmlFa4Fwd.Proof.MmaPvPrefixCut
import Kernels.TmlFa4Fwd.Proof.MmaElect
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

/-- The common release election is the synchronization point before the initial
value branch. Replay preserves the physical shared base in its continuation. -/
theorem initialValueAnchorFromKey {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} {target : Event}
    (hs : At s 2148 (readyFrame l)) (hw : Walk kernel Assumptions.all l g s es vs)
    (he : target ∈ es) (hLate : 2271 < target.pc) :
    ∃ inst leader u pre tail post,
      es = pre ++ ⟨2271, .elect (2^32-1) inst leader⟩ :: tail ∧
      At u 2272 (readyFrame l) ∧ Walk kernel Assumptions.all l g u tail post ∧
      target ∈ tail := by
  have hAudit : ((kernel.code.drop 2148).take (2271-2148)).all
      (pvCutCode 2148 2271 ((readyFrame l).map Prod.fst)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨hs.2.1.symm ▸ Nat.zero_le _, hs.2.2.1, fun _ => hs.2.1⟩, hs.2.2.2.2.2.1⟩
  have hBounds : 2148 ≤ s.pc ∧ s.pc ≤ 2271 := by rw [hs.1]; decide
  obtain ⟨t,pre,rest,visits,hSplit,htPc,htShape,htF,htW,hTarget,_⟩ :=
    pvWalkCut (by decide) (by decide) hAudit hw hBounds hShape hs.2.2.2.2 he hLate.le
  have hLater : t.pc < target.pc := htPc ▸ hLate
  have ht : At t (electSite 4).pc (readyFrame l) :=
    ⟨htPc, htShape.1.2.2 (by rw [htPc]; decide), htShape.1.2.1,
      normalBeforeLaterEvent htW hTarget hLater, htF⟩
  obtain ⟨u,e,tail,post,hEvent,hFires,_,hWalk,hTail⟩ :=
    pvWalkEvent htW (electTemplate 4 ht) hTarget hLater
  obtain ⟨inst,leader,rfl,hNew⟩ := hFires
  obtain rfl := Option.some.inj hNew
  have hAfter := electStateFrame (l := l) (g := g) 4 ht leader
    (by simp [electSite,readyFrame]) (by simp [electSite,readyFrame])
  refine ⟨inst,leader,_,pre,tail,post,?_, hAfter.mono ?_,hWalk,hTail⟩
  · simp [hSplit,hEvent,htPc]
  · exact hAfter.2.2.2.2.2

end
end PTX.Kernels.TmlFa4Fwd.Mma
