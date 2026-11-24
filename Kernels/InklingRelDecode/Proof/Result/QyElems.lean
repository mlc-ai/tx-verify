-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.QyKv
public import Kernels.InklingRelDecode.Proof.Result.QyPRead
public import Kernels.InklingRelDecode.Proof.Result.QyOBase

@[expose] public section

/-!
# `Qx.ElemRest` and `Qx.SourceRest.a` on every consistent execution

`elemRest_of` collects the three fields of `Qx.ElemRest`: `b` (`Qy.elemB_of`, with
`Wz.kvCopiesF_of`), `pvA` (`Qy.pvA_of`) and `oBase` (`Qy.oBase_of`). `LdSmRest` is the one field
of `Qx.SourceRest` that `Qy.aSource_of` does not give; `sourceRest_of` builds `Qx.SourceRest`
from it.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Qy
open PTX PTX.Flow PTX.Proof PTX.TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Interface (St TSt ThreadFacts threadCode)
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk (DecAgree)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`Qx.ElemRest`** on every consistent execution. -/
theorem elemRest_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (hR : Interface.RoleReads L X) (hE : Interface.Bar1Exits L X)
    (hp : Interface.NumPreRead Q L X) (hb : Interface.BaseWordRead L X)
    (hn : Interface.NumWordRead Q L X) (hbox : Safety.BoxInBounds X)
    (hnc : ∀ e cp, ¬ X.CpIssue e cp) (hns : ∀ e s, ¬ X.ShiftIssue e s)
    (G : Sr.SrPkg L kernel Assumptions.all mem0 X) (hG : ∀ c, G.p0 c = Hs.p0Of L c)
    (st : Pr.MmaStates Q L G) (ht : Tmem1.Tmem1Facts L X 0) (hmd : Tmem1.MmaDoneDealloc L X)
    (hD : ∀ c j, DecAgree Q L X c j) (hO : OLoadSrcF Q L X) (hMB : Mma.MmaBcast L X)
    (hre : Interface.Lk.SmReal Q L X) : Qx.ElemRest Q L X where
  pvA := pvA_of hpre hX hf hb hn hnc hns G hG st ht hmd hD hre
  b := elemB_of hpre hX hf hT hR hE hp hbox G (Wz.kvCopiesF_of hpre hX hf hR hp G) hMB
  oBase := oBase_of hpre hX hf hb hn hnc hns G st ht hmd hR hO hMB

/-- **The registers of the softmax region's loads have read sources with values**
(`Qx.SourceRest.ldSm`). -/
def LdSmRest (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc a j : Nat} {vals : List Value} {sh : TcShape} {d : Sm.D} {cell : Cell},
    g < L.threads → X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩ →
    St Q L X g k = some (some (.d (.sm d))) → LoadCell L X (g, k) j cell →
    ∃ source value, ReadSource L X .ld source (g, k) cell ∧
      Wrote L Assumptions.all X source cell value

/-- **`Qx.SourceRest`** from the sources of the softmax region's loads (`LdSmRest`). -/
theorem sourceRest_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : Interface.BaseWordRead L X)
    (hn : Interface.NumWordRead Q L X)
    (hnc : ∀ e cp, ¬ X.CpIssue e cp) (hns : ∀ e s, ¬ X.ShiftIssue e s)
    (G : Sr.SrPkg L kernel Assumptions.all mem0 X) (hG : ∀ c, G.p0 c = Hs.p0Of L c)
    (st : Pr.MmaStates Q L G) (ht : Tmem1.Tmem1Facts L X 0) (hmd : Tmem1.MmaDoneDealloc L X)
    (hD : ∀ c j, DecAgree Q L X c j) (h : LdSmRest Q L X) : Qx.SourceRest Q L X where
  ldSm := h
  a := aSource_of hpre hX hf hb hn hnc hns G hG st ht hmd hD

end
end PTX.Kernels.InklingRelDecode.Proof.Qy
