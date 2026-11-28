-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Common.Export.RegLedger

@[expose] public section

/-! # ERR-ALIGNED, the `setmaxnreg` class

Divergence: the lanes of a warp at their `k`-th request are at the position `Lib.reqPcOf` of
their warp and ordinal (`Export.request_pc`), and the operands of the class are not compared.
Early exit: a request has ordinal at most 2 in the default partition and 3 in a worker, and an
exit follows three requests in the default partition and four in a worker
(`Export.exit_requests`); the participants of a request are its warpgroup. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

theorem Safe.alignedReg (hp : Pre Q L m) (words : RoleBytes L X)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) :
    ¬ AlignedClass.setMaxReg.Divergent L kernel X ∧ ¬ AlignedClass.setMaxReg.Exited L kernel X := by
  have hb : L.block = 256 := hp.block
  constructor
  · rintro ⟨⟨g,k⟩,⟨h,j⟩,pe,pf,ke,kf,hw,he,hf',hme,hmf,hord,-,hne⟩
    obtain ⟨inc,n,inst,rfl⟩ := isRequest_kind hme
    obtain ⟨inc',n',inst',rfl⟩ := isRequest_kind hmf
    have p1 := (Export.request_pc hp hX hf words he).1
    have p2 := (Export.request_pc hp hX hf words hf').1
    have warp : g%L.block/32 = h%L.block/32 := hw.2
    have eqn : ((X.tr g).take k).countP SetMaxNReg.isRequest =
        ((X.tr h).take j).countP SetMaxNReg.isRequest := hord
    rw [warp,eqn] at p1
    rcases hne with hne | hne
    · exact hne (p1.trans p2.symm)
    · exact hne rfl
  · rintro ⟨⟨g,k⟩,⟨h,j⟩,⟨pe,ke⟩,hs,he,hm,-,⟨pcx,hx⟩,hle⟩
    obtain ⟨inc,n,inst,rfl⟩ := isRequest_kind hm
    obtain ⟨-,low,high⟩ := Export.request_pc hp hX hf words he
    obtain ⟨xlow,xhigh⟩ := Export.exit_requests hp hX hf words hx
    have grp : g%L.block/32/4 = h%L.block/32/4 := hs.2
    have part : (X.tr h).countP SetMaxNReg.isRequest ≥
        ((X.tr h).take j).countP SetMaxNReg.isRequest :=
      (List.take_sublist _ _).countP_le
    have hle' : (X.tr h).countP SetMaxNReg.isRequest ≤
        ((X.tr g).take k).countP SetMaxNReg.isRequest := hle
    by_cases d : g%L.block<128
    · have := low d
      have := xlow (by omega)
      omega
    · have := high (by omega)
      have := xhigh (by omega)
      omega

end PTX.Kernels.InklingRelDecode.Proof.Top
