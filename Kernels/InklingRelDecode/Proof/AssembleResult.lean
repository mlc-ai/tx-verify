-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.AssembleProtocol
public import Kernels.InklingRelDecode.Proof.Interface.PlAll
public import Kernels.InklingRelDecode.Proof.Result.OutAll
public import Kernels.InklingRelDecode.Proof.Result.RdAll
public import Kernels.InklingRelDecode.Proof.Result.RrAll
public import Kernels.InklingRelDecode.Proof.Result.RsAll
public import Kernels.InklingRelDecode.Proof.Result.SvAll
public import Kernels.InklingRelDecode.Proof.Result.SwAll
public import Kernels.InklingRelDecode.Proof.Result.PrAll
public import Kernels.InklingRelDecode.Proof.Protocol.Lk5Final
public import Kernels.InklingRelDecode.Proof.Result.KkAll
public import Kernels.InklingRelDecode.Proof.Result.LpAll
public import Kernels.InklingRelDecode.Proof.Interface.LpQTile
public import Kernels.InklingRelDecode.Proof.Result.HsAll
public import Kernels.InklingRelDecode.Proof.Interface.SxKvOrder
public import Kernels.InklingRelDecode.Proof.Result.PxAll

@[expose] public section

/-!
# `Result.Out.Inputs` from the proved result theorems

Nothing is left of `Out.Inputs` as a premise: every field of `Out.Inputs` for a complete
consistent execution `X` is built, given the handshake package of `ProtocolRest.srPkg`. Each field
of `Out.Inputs` and how it is obtained (`inputs_of`):

* `smOb`, `premises`: `Interface.smOb`, `Premises` of the base;
* `mmaWords`: `Rs.mmaWords_of` (`BaseWordRead`, `NumWordRead`);
* `qkChain`: `Pr.qkChain_of`, premise `mmaStates`;
* `pTile`: `Rs.pTile_of`, with `Kk.pReadSrc_of` (from `pkg` and `mmaStates`) and `Sv.SvPrem`;
* `oAcc`: `Rs.oAcc_of`, with `OAccPrem` built from `Rs.store_of` (`Rr.ostIter_of`),
  `Rr.oaccOstIter_of` and `Px.skip_of` (for `1 ≤ b < num_iters`);
* `smExit`: `Sv.smExit_of`, from `Sv.SvPrem`;
* `oSource`: `Rs.oSource_of`, with `OSrcPrem` built from `IpMma.final_first`,
  `IpMma.mma_before_final`, `Interface.epiTm_of` and `Rr.ostBound_of`;
* `Sv.SvPrem` is `Sv.svPrem_of` from `Rd.sLoadSrc_of` (`Sv.SLoadSrc`), `Rd.oLoadSrc_of`
  (`Rs.OLoadSrc`), `Interface.Lk.exchPrem_of_it`, `Lp.kvCopies_of` (`Out.Inputs.kvCopies`),
  `Lp.qTile_of` (`Out.Inputs.qTile`), and `kvOrder_base` (`Sx.kvOrder_of`, also the field
  `Out.Inputs.kvOrder`).

`Rd.sLoadSrc_of` and `Rd.oLoadSrc_of` take `Rd.softAll`, `Rr.sRdv_of`, `Kk.sPstAfter_of` and
`Kk.oRdv_of` (proved; the last two from the decisions of every iteration,
`Interface.Lk.decAgree_every`) and the premise `mmaStates`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Assemble
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`Out.Inputs.kvOrder`** (`Sx.kvOrder_of`), with the KV slots' consumer the handshake
package's committing lane. -/
theorem kvOrder_base (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (b : Base Q L mem0 X)
    (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) : KvOrder Q L X :=
  Sx.kvOrder_of hpre hX b.facts b.tmpl (Base.roleReads hpre hX) b.bar1
    (Base.numPreRead hpre hX) (Base.boxInBounds hpre hX) (ProtocolRest.srPkg hpre hX b hI)
    (Base.mmaBcast hpre hX b)

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hcomp : Complete L X)
  (b : Base Q L mem0 X)
  (hI : ∀ i, Interface.Lk.ScratchIt Q L X i)
include hpre hX hcomp b hI

/-- **`Sv.SvPrem`** from the read source of the S load and the exchange. -/
theorem svPrem_base : Sv.SvPrem Q L X := by
  have hR := Base.roleReads hpre hX
  have hkv : KvCopies Q L X := Lp.kvCopies_of hpre hX b.facts hR (Base.numPreRead hpre hX)
    (Base.numWordRead hpre hX) hcomp
  have hqt : QTile Q L X := Lp.qTile_of hpre hX b.facts b.tmpl hR b.bar1 hcomp
  let G := ProtocolRest.srPkg hpre hX b hI
  have hbw : BaseWordRead L X := Interface.baseWordRead_of hpre hX
  have hnw : NumWordRead Q L X := Base.numWordRead hpre hX
  have hmw : MmaWords Q L X := Rs.mmaWords_of hpre hX b.facts hbw hnw
  have ht := Proof2.tmem1Facts hpre hX
  have hms : Pr.MmaStates Q L G :=
    Hs.mmaStates_pkg hpre hX b.facts hR hbw hnw hI
      (Vx.pkgRest_of hpre hX b.facts hR (Base.mmaBcast hpre hX b))
  have hmd : Tmem1.MmaDoneDealloc L X :=
    Tmem1.mmaDoneDealloc_of hX
      (Vx.tmemLife_of hpre hX b.facts) (ProtocolRest.oFinal hpre hX b hI)
      (IpMma.dealloc_poll hpre hX b.facts)
  have hch : QkChain Q L X := Pr.qkChain_of hpre hX b.facts (Tmem1.no_cp hX) (no_shift hX) G
    hms ht hmd
  have hSL : Sv.SLoadSrc Q L X := Rd.sLoadSrc_of hpre hX b.facts (Base.mmaBcast hpre hX b) hR hbw
    hnw (Tmem1.no_cp hX)
    (no_shift hX) G hms ht
      (Vx.tmemLife_of hpre hX b.facts) (Rs.smBaseZero hpre hX b.facts hbw)
    (Rd.softAll G)
    (Rr.sRdv_of hpre hX b.facts hcomp G)
    (Kk.sPstAfter_of hpre hX b.facts hcomp (Interface.Lk.decAgree_every hpre hX b.facts hI) G)
  have hE : Sv.ExchPrem Q L X :=
    Interface.Lk.exchPrem_of_it hpre hX b.facts (ProtocolRest.smMaxOk hpre hX b hI)
      (Rs.smBaseZero hpre hX b.facts hbw) (fun hg hvr he hσ hs =>
      Sv.scoreEv_of hpre hX b.facts hcomp hkv (kvOrder_base hpre hX b hI) hmw hqt hch hSL hg
        hvr he hσ hs)
  exact Sv.svPrem_of hpre hX b.facts hcomp hkv (kvOrder_base hpre hX b hI) hmw hqt hch hSL hE
    (ProtocolRest.smMaxOk hpre hX b hI)

/-- **`Out.Inputs`** for a complete consistent execution. -/
theorem inputs_of : Result.Out.Inputs Q L mem0 X := by
  have hR := Base.roleReads hpre hX
  have hkv : KvCopies Q L X := Lp.kvCopies_of hpre hX b.facts hR (Base.numPreRead hpre hX)
    (Base.numWordRead hpre hX) hcomp
  have hqt : QTile Q L X := Lp.qTile_of hpre hX b.facts b.tmpl hR b.bar1 hcomp
  let G := ProtocolRest.srPkg hpre hX b hI
  have hbw : BaseWordRead L X := Interface.baseWordRead_of hpre hX
  have hnw : NumWordRead Q L X := Base.numWordRead hpre hX
  have hmw : MmaWords Q L X := Rs.mmaWords_of hpre hX b.facts hbw hnw
  have ht := Proof2.tmem1Facts hpre hX
  have hms : Pr.MmaStates Q L G :=
    Hs.mmaStates_pkg hpre hX b.facts hR hbw hnw hI
      (Vx.pkgRest_of hpre hX b.facts hR (Base.mmaBcast hpre hX b))
  have hmd : Tmem1.MmaDoneDealloc L X :=
    Tmem1.mmaDoneDealloc_of hX
      (Vx.tmemLife_of hpre hX b.facts) (ProtocolRest.oFinal hpre hX b hI)
      (IpMma.dealloc_poll hpre hX b.facts)
  have hz : Rs.SmBaseZero Q L X := Rs.smBaseZero hpre hX b.facts hbw
  have hP := svPrem_base hpre hX hcomp b hI
  have hOL : Rs.OLoadSrc Q L X := Rd.oLoadSrc_of hpre hX b.facts (Base.mmaBcast hpre hX b) hcomp hR
    hbw hnw
    (Tmem1.no_cp hX) (no_shift hX) G hms ht (Vx.tmemLife_of hpre hX b.facts) hz
    (Rd.softAll G)
    (Kk.oRdv_of hpre hX b.facts hcomp (Interface.Lk.decAgree_every hpre hX b.facts hI) G)
  refine
    { smOb := smOb
      premises := b.prem
      kvCopies := hkv
      kvOrder := kvOrder_base hpre hX b hI
      qTile := hqt
      mmaWords := hmw
      qkChain := Pr.qkChain_of hpre hX b.facts (Tmem1.no_cp hX) (no_shift hX) G
        hms ht hmd
      pTile := Rs.pTile_of hpre hX b.facts hcomp hP (ProtocolRest.smReal hpre hX b hI)
        (Kk.pReadSrc_of hpre hX b.facts hcomp hbw hnw (Tmem1.no_cp hX) (no_shift hX) G
          hms ht hmd) hmw hz (Tmem1.no_cp hX) (no_shift hX)
      oAcc := Rs.oAcc_of hpre hX b.facts (Base.mmaBcast hpre hX b) hcomp hbw hnw (Tmem1.no_cp hX)
        (no_shift hX) G
        hms
        { ostIter := Rr.oaccOstIter_of hpre hX b.facts G
          skip := Px.skip_of hpre hX b.facts hcomp hbw hR hI hP
          store := Rs.store_of hpre hX b.facts hP G hOL hz
            (Rr.ostIter_of hpre hX b.facts G) } ht hmd
      smExit := Sv.smExit_of hpre hX b.facts hP
      oSource := Rs.oSource_of hpre hX b.facts (Base.mmaBcast hpre hX b) hbw hnw (Tmem1.no_cp hX)
        (no_shift hX) G
        hms ?_ ht (Vx.tmemLife_of hpre hX b.facts) }
  exact
    { commit_once := fun c hc i pc sp he hm => by
        have hR := Base.roleReads hpre hX
        have l := G.lane c hc
        obtain ⟨-, hcmc⟩ := l.cm_ok
        have := IpMma.final_first hpre hX b.facts hR he (by rw [hcmc]; exact hm)
        rwa [hcmc] at this
      mma_before := fun c hc x hx hxc i pc sp he hm => by
        have l := G.lane c hc
        obtain ⟨-, hcmc⟩ := l.cm_ok
        have hxe := l.mma_thread hx hxc
        obtain ⟨pcx, dx, sx, ax, mx, hxget⟩ := hx.get
        obtain ⟨xg, xk⟩ := x
        simp only at hxe ⊢
        subst hxe
        exact IpMma.mma_before_final hpre hX b.facts hR hxget he (by rw [hcmc]; exact hm)
      epiTm := Interface.epiTm_of hpre hX b.facts (Interface.baseWordRead_of hpre hX)
      ostBound := Rr.ostBound_of hpre hX b.facts G }

end
end PTX.Kernels.InklingRelDecode.Proof.Assemble
