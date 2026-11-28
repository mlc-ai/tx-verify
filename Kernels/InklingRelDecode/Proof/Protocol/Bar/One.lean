-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Protocol.NamedBarSources
public import Lemmas.Protocol.NamedBarMember
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Kernels.InklingRelDecode.Proof.Lib.NoBarArrive

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Bar
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Every arrival on barrier 1 is a lane of a warp of the CTA passing no count.** -/
theorem one_sources (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    NamedBar.Sources L X none (Finset.range (CtaBarrier.warps L.block)) 1 := by
  intro e pc cnt ⟨mode,he⟩ hg
  have hb : L.block=256 := hp.block
  rcases (Lib.recorded_bar hX hb he).2 with one | ⟨h,_⟩ | ⟨h,_⟩
  · refine ⟨?_,one.2.1⟩
    have := Nat.mod_lt e.1 (show L.block>0 by omega)
    simp only [Finset.mem_range,CtaBarrier.warps,hb] at this ⊢
    omega
  all_goals omega

/-- **The group of barrier 1**: all 8 warps, without a thread count. -/
theorem one_shape (hp : Pre Q L m) :
    NamedBar.Shape L none (Finset.range (CtaBarrier.warps L.block)) 1 := by
  have hb : L.block=256 := hp.block
  refine ⟨?_,?_,?_,by decide⟩
  · simp [CtaBarrier.warps,hb]
  · simp [CtaBarrier.target]
  · intro w hw
    simp only [Finset.mem_range,CtaBarrier.warps,hb] at hw ⊢
    omega

/-- **Two threads of one CTA synchronize through barrier-1 arrivals of one ordinal.** -/
theorem one_baseCausality (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g h i j before after pc pc'} (hsame : SameCta L g h)
    (he : X.IsBarrier (g,i) 1 none pc) (hf : X.IsBarrier (h,j) 1 none pc')
    (hpassed : j+1 < (X.tr h).length)
    (hordinal : ((X.tr g).take i).countP (Execution.isBarId 1)=
      ((X.tr h).take j).countP (Execution.isBarId 1))
    (hbefore : before < i) (hafter : j < after) (hlen : after < (X.tr h).length) :
    baseCausality L X (g,before) (h,after) :=
  (one_sources hp hX).same_ordinal_baseCausality hX (one_shape hp) hsame he hf hpassed
    hordinal hbefore hafter hlen

/-- **Every thread of the CTA has the barrier-1 arrival that a passed thread passed**, an
exiting thread by `exited`. -/
theorem one_member (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {f : EvId} {pc : Nat} (hf : X.IsBarrier f 1 none pc) (hpassed : f.2+1 < (X.tr f.1).length)
    {g : Nat} (hcta : g/L.block=f.1/L.block)
    (exited : (∃ j pcx, X.get (g,j)=some ⟨pcx,.exit⟩) →
      ∃ i pc', X.IsBarrier (g,i) 1 none pc' ∧ ((X.tr g).take i).countP (Execution.isBarId 1)=
        ((X.tr f.1).take f.2).countP (Execution.isBarId 1)) :
    ∃ i pc', X.IsBarrier (g,i) 1 none pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId 1)=
        ((X.tr f.1).take f.2).countP (Execution.isBarId 1) := by
  have hb : L.block=256 := hp.block
  refine (one_sources hp hX).member_arrival hX (one_shape hp) hf hpassed hcta ?_ exited
  have := Nat.mod_lt g (show L.block>0 by omega)
  simp only [Finset.mem_range,CtaBarrier.warps,hb] at this ⊢
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Bar
