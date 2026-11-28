-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Lemmas.Flow.Regs
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.MmaPcs
public import Kernels.InklingRelDecode.Proof.Lib.MmaFoot
public import Kernels.InklingRelDecode.Proof.Lib.MmaIssue
import Kernels.InklingRelDecode.Proof.Common.BaseWord
import Kernels.InklingRelDecode.Proof.Common.History
import Kernels.InklingRelDecode.Proof.Mma.OperandWords
import Lemmas.Flow.NotTcMma
import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.NotBulk
import Kernels.InklingRelDecode.Proof.Mma.Export.Operands

/-! # The Tensor Memory columns of an MMA issue

Every MMA of the kernel names its destination and its Tensor Memory A operand by the recorded
allocation word, which is zero (the recorded base word): a QK issue writes the score buffer of its
parity (`128 (b % 2)`), a PV issue writes the accumulator at column 256 and reads the P columns
`128 ((b - 1) % 2) + 8 j` of its parity; the lane masks are zero. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Proof PTX.Flow

private def positions := (List.finRange 8).map qkPc ++ (List.finRange 8).map pvPc

private theorem qk_eq (j : Fin 8) : qkPc j = Lib.qkIssue j := by
  fin_cases j <;> rfl

private theorem pv_eq (j : Fin 8) : pvPc j = Lib.pvIssue j := by
  fin_cases j <;> rfl

private theorem checked : OpPcsFast kernel.code tcMmaOp positions=true := by decide +kernel

private theorem site_form (s : Site) (hit : s.pc ∈ positions) :
    (∃ j,s=.qk j) ∨ ∃ j,s=.pv j := by
  cases s <;> first | exact .inl ⟨_,rfl⟩ | exact .inr ⟨_,rfl⟩ | exact absurd hit (by decide +kernel)

private theorem core {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (he : X.get (g,k)=some ⟨pc,.tc (.mma dst s acc mask)⟩) :
    (mask=[0,0,0,0] ∧ s.lowCta=g/L.block ∧ s.highCta=g/L.block ∧
      ∃ b, (∃ j : Fin 8, pc=Lib.qkIssue j ∧ dst=128*(b%2) ∧ s.aTmem=none ∧
        s.descriptor=Lib.qkDesc) ∨
      ∃ j : Fin 8, pc=Lib.pvIssue j ∧ dst=256 ∧ s.aTmem=some (128*((b-1)%2)+8*j.val) ∧
        s.descriptor=Lib.pvDesc) ∧ TcMma.IssueShape L (g,k) dst s mask := by
  obtain ⟨_,bad⟩|⟨_,_,_,_,code,fire⟩ := get_source hX he
  · cases bad
  have hit := OpPcsFast.mem checked code (fires_tcMma_op fire rfl)
  have range : ∀ p ∈ positions, 2422<p ∧ p<2557 := by decide +kernel
  obtain ⟨w,x,r,d,n,hs,pcEq⟩ := mma_state hp hX hf he (fun _ => nofun)
    (range _ hit).1 (range _ hit).2
  have hg := Frame.lt_of_get hX he
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have zero : w=b32 0 := recorded_zero hp hX base hk (Frame.noUbBefore_of_get hX he) hs
  obtain ⟨t,ins,o,ht,_,hc,ff⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hs
    (fun _ => nofun)
  change pc=d.site.pc at pcEq
  subst pc
  obtain ⟨site,i,v⟩ := d
  change site.pc ∈ positions at hit
  rcases site_form site hit with ⟨j,rfl⟩|⟨j,rfl⟩
  · obtain ⟨dstEq,ms,-⟩ := q_dst zero j ht hc ff
    obtain ⟨desc,atmem,sa,sb,ctas,grp,lo,hi⟩ := q_operands hp j ht hc ff
    obtain ⟨own,own'⟩ := owner hp hg grp lo hi
    have room := hp.sharedRange
    change L.sharedBase+213340≤2^18 at room
    have jq := j.isLt
    have qa : qWord L j * 16 < 2^18 := by dsimp [qWord,qLo]; omega
    have kb : kWord L i j * 16 < 2^18 := by dsimp [kWord,kLo]; omega
    have par : dst=0 ∨ dst=128 := by
      rw [dstEq]
      rcases Nat.mod_two_eq_zero_or_one i with h|h <;> simp [h]
    refine ⟨⟨ms,own,own',i,.inl ⟨j,qk_eq j,dstEq,atmem,desc⟩⟩,?_⟩
    refine Lib.qk_issueShape hg (by omega) (by omega) (by omega) (by omega) par ms desc atmem
      ?_ sa sb
    exact ⟨ctas,by simpa [desc,Lib.qkDesc] using grp,lo,hi⟩
  · obtain ⟨dstEq,aEq,ms,-⟩ := v_dst zero j ht hc ff
    obtain ⟨desc,-,same,sb,ctas,grp,lo,hi⟩ := v_operands hp j ht hc ff
    obtain ⟨own,own'⟩ := owner hp hg grp lo hi
    have room := hp.sharedRange
    change L.sharedBase+213340≤2^18 at room
    have jq := j.isLt
    have vb : vWord L i j * 16 < 2^18 := by dsimp [vWord,vLo]; omega
    have lt : 128*((i-1)%2)+8*j.val < 256 := by
      have := Nat.mod_lt (i-1) (show 0<2 by decide)
      omega
    refine ⟨⟨ms,own,own',i,.inr ⟨j,pv_eq j,dstEq,aEq,desc⟩⟩,?_⟩
    refine Lib.pv_issueShape hg (by omega) (by omega) dstEq ms desc aEq lt same ?_ sb
    exact ⟨ctas,by simpa [desc,Lib.pvDesc] using grp,lo,hi⟩

public theorem columns {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (he : X.get (g,k)=some ⟨pc,.tc (.mma dst s acc mask)⟩) :
    mask=[0,0,0,0] ∧ s.lowCta=g/L.block ∧ s.highCta=g/L.block ∧
      ∃ b, (∃ j : Fin 8, pc=Lib.qkIssue j ∧ dst=128*(b%2) ∧ s.aTmem=none ∧
        s.descriptor=Lib.qkDesc) ∨
      ∃ j : Fin 8, pc=Lib.pvIssue j ∧ dst=256 ∧ s.aTmem=some (128*((b-1)%2)+8*j.val) ∧
        s.descriptor=Lib.pvDesc :=
  (core hp hX hf base he).1

/-- **Every MMA issue passes `TcMma.IssueShape`.** -/
public theorem issue_shape {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (he : X.get (g,k)=some ⟨pc,.tc (.mma dst s acc mask)⟩) :
    TcMma.IssueShape L (g,k) dst s mask :=
  (core hp hX hf base he).2

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
