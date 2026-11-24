-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.IpLifeExit
public import Kernels.InklingRelDecode.Proof.Interface.IpTmOps
public import Kernels.InklingRelDecode.Proof.Protocol.TmemAccess

@[expose] public section

/-!
# Every deallocation follows a successful poll of `o_final`

`hpoll` of `Tmem1.mmaDoneDealloc_of` (`TmemAccess.lean`): every deallocation event of the kernel
is fired by a thread of warp 0 of its CTA from the epilogue's `dealloc` site
(`Interface.res_event_state`), and the epilogue has polled `o_final` successfully, with acquire, at
every site after its `wait` site (`Life.exitP_inv`: the poll measure of the second kernel fix, the
poll runs also when `num_iters < 1`). So an earlier event of the same thread is the poll.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.IpMma
open PTX PTX.Proof PTX.Flow AsyncCopy PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`hpoll` of `Tmem1.mmaDoneDealloc_of`**: a deallocation follows, in its own thread, a
successful acquire poll of its CTA's `o_final`. -/
theorem dealloc_poll (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) :
    ∀ {d : EvId} {pc a n : Nat} {grp : CtaGroup} {dst : Option Loc},
      X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩ →
      ∃ h j pc' p sc, h < L.threads ∧ h / L.block = d.1 / L.block ∧
        X.get (h, j) = some ⟨pc', .wait (EvW.oFinal L (d.1 / L.block)) p true true sc⟩ := by
  rintro ⟨g, k⟩ pc a n grp dst he
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨-, h | h | ⟨d, hσ, hs, -, -⟩⟩ := res_event_state hpre hX hf he
  · obtain ⟨tm, -, -, hact⟩ := h
    cases hact
  · obtain ⟨tm, -, -, hact⟩ := h
    cases hact
  · obtain ⟨j, hj, pc', p, sc, hev⟩ := Life.exitP_inv hpre hX hf hg k _ hk.le hσ (by
      simp only [Life.exitP, SO.epiPolled, hs]
      omega)
    exact ⟨g, j, pc', p, sc, hg, rfl, hev⟩

end
end PTX.Kernels.InklingRelDecode.Proof.IpMma
