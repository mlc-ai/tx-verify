-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.AssembleBase
public import Kernels.InklingRelDecode.Proof.AssembleLock
public import Kernels.InklingRelDecode.Proof.AssembleLk4
public import Kernels.InklingRelDecode.Proof.Protocol.All
public import Kernels.InklingRelDecode.Proof.Protocol.IpAll
public import Kernels.InklingRelDecode.Proof.Protocol.BarAll
public import Kernels.InklingRelDecode.Proof.Protocol.BarLaneAll
public import Kernels.InklingRelDecode.Proof.Protocol.SrAll
public import Kernels.InklingRelDecode.Proof.Protocol.TmemAll
public import Kernels.InklingRelDecode.Proof.Protocol.KvAll
public import Kernels.InklingRelDecode.Proof.Safety.All
public import Kernels.InklingRelDecode.Proof.Safety.PlAll
public import Kernels.InklingRelDecode.Proof.Protocol.PlAll
public import Kernels.InklingRelDecode.Proof2.Safety.GlobalW
public import Kernels.InklingRelDecode.Proof.Interface.PlAll
public import Kernels.InklingRelDecode.Proof.Protocol.RrAll
public import Kernels.InklingRelDecode.Proof.Interface.FrAll
public import Kernels.InklingRelDecode.Proof.Protocol.FrAll
public import Kernels.InklingRelDecode.Proof.Protocol.HsAll
public import Kernels.InklingRelDecode.Proof.Protocol.VxAll
public import Lemmas.Flow.NotTcShift
public import Lemmas.Flow.NotBulk
public import Kernels.InklingRelDecode.Proof.Protocol.LpObs
public import Kernels.InklingRelDecode.Proof.Interface.LpPreProof
public import Kernels.InklingRelDecode.Proof.Protocol.SxAll
public import Kernels.InklingRelDecode.Proof.Result.QxAll
public import Kernels.InklingRelDecode.Proof.Result.QySmMax
public import Kernels.InklingRelDecode.Proof.Result.QxEpi
public import Kernels.InklingRelDecode.Proof.Result.QxSource
public import Kernels.InklingRelDecode.Proof.Result.QyAll
public import Kernels.InklingRelDecode.Proof.Protocol.QyAll
public import Kernels.InklingRelDecode.Proof.Result.RrOst
public import Kernels.InklingRelDecode.Proof.Result.HsMmaStates
public import Kernels.InklingRelDecode.Proof.Result.RsWords
public import Kernels.InklingRelDecode.Proof.Interface.WqUniform
public import Kernels.InklingRelDecode.Proof2.Safety.RegReq

@[expose] public section

/-!
# `Safety.Protocol` from the proved protocol theorems

`ProtocolRest Q L mem0 X` lists what is left of `Safety.Protocol` after every field that has a
proof is built from it (`protocol_of`). The fields of `Safety.Protocol` and how each is obtained:

* `odoneWait`, `boxInBounds`: `Interface.odoneWait`,
  `Proof2.box_in_bounds` (through `Base`);
* `mbarInit`, `objectsPublished`: `Bar.mbarInit_final`, `Bar.objectsPublished_final`;
* `regAligned`, `regAgree`, `regSync`: `Proof2.reg_aligned`, `Proof2.reg_agree`,
  `Proof2.reg_sync`;
* `ctaBar`: `Bar.ctaBar_of_roleReads`, premise `Bar.AlphaAgree` (`halpha`);
* `lifetime`: `Life.lifetime`, premise `pkg` (`Rr.sObserved_of`, `Lp.copyObserved_of` are
  proved);
* `tmemAccess`: `Tmem1.no_access_unsafe`, premises `tmemLife`, `pkg`, with `Tmem1.access_shape_of`
  (`Protocol/FrAccess.lean`);
* `tcInstr`: `Tmem1.tcInstr_of`, with `ProtocolRest.values` (`Qx.result_of`, with
  `Qy.elemRest_of`);
* `tcWrites`, `tcReads`: `Sr.no_writes_unsafe`, `Sr.no_reads_unsafe`, premise `pkg`;
* `recordsOk`: `Mbar.recordsOk_of_ctas`, premise `pkg` (the KV slots are `Lp.kv_of`, with
  `Lp.preRing_of`).

* `barLanes`, `barAligned`: `Base.barLanes`, `Base.barAligned` (`AssembleLock.lean`), from the
  lockstep of the lanes of a warp; the one premise is `hsm`, `Interface.Lk.LaneAgreeSm` (both lanes
  take the lazy-rescale branch of the softmax region or neither);
* `tcAligned`: `Base.tcAligned` (`AssembleLk4.lean`), from the same lockstep.

* `sharedPlaced`: `Proof2.sharedPlaced` (the second tree's role table, `Proof2/Safety/Placed.lean`);
* `faultFree`: `Interface.faultFree_of` (`Interface/PlFault.lean`) with `Interface.Lk.faultRest_of`
  (`Protocol/FrSm.lean`), with `ProtocolRest.epiLoad` (`Qx.epiLoad_of`: the source of the
  epilogue's load, `Rs.oSourceAll_of`, and the `f32` values of `ProtocolRest.resultF32`).

* `globalReads`, `globalPlaced`: `Proof2.global_reads`, `Proof2.global_placed` (the second
  tree's role table);
* `order`: `Sx.order_of` (`Protocol/SxOrder.lean`).
* `warpUniform`: `Wq.warpUniform_of` (`Interface/WqUniform.lean`) with `Proof2.poll_synced`
  (`Proof2/Safety/WarpPoll.lean`).

* `tcSource`: `Qx.tcSource_of` with `Qy.sourceRest_of` (the softmax region's loads `Qy.ldSm_of`,
  the PV MMAs' A reads `Qy.aSource_of`); `tcInstr` and `faultFree` through
  `ProtocolRest.values`, `ProtocolRest.epiLoad` (the operand elements and base accumulators are
  `Qy.elemRest_of`).

The other field has no proof: `pollSynced`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Assemble
open PTX PTX.Proof PTX.Flow AsyncCopy TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxRecDepth 100000 in
/-- **The kernel has no `tcgen05.shift`**: an audit of the program text. -/
theorem kernel_noTcShift : kernel.code.all (fun ins => !tcShiftOp ins.op) = true := by
  decide +kernel

/-- **A consistent execution of the kernel issues no `tcgen05.shift`.** -/
theorem no_shift (hX : Consistent L kernel asms mem0 X) : ∀ e s, ¬ X.ShiftIssue e s := by
  rintro e s ⟨pc, he⟩
  exact no_kind_of_code hX tcShiftOp (fun k => ∃ s, k = .tc (.shift s))
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_tcShift_op hf hk)
    kernel_noTcShift he ⟨s, rfl⟩

/-- **The handshake package** (`Hs.pkg_of`) from the base, with `Hs.PkgRest` proved
(`Vx.pkgRest_of`). -/
def ProtocolRest.srPkg (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (b : Base Q L mem0 X)
    (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) : Sr.SrPkg L kernel asms mem0 X :=
  Hs.pkg_of hpre hX b.facts (Base.roleReads hpre hX)
    (Interface.baseWordRead_of hpre hX) (Base.numWordRead hpre hX) hI
    (Vx.pkgRest_of hpre hX b.facts (Base.roleReads hpre hX) (Base.mmaBcast hpre hX b))

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (b : Base Q L mem0 X)
include hpre hX b

/-- **`Tmem1.OFinalFacts` of every launched CTA**, from the handshake package: the committing
lane of the package is the MMA lane, its first commit to `o_final` has no earlier one
(`IpMma.final_first`) and follows every MMA of the CTA (`IpMma.mma_before_final`). -/
theorem ProtocolRest.oFinal (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) :
    ∀ c < L.grid, Tmem1.OFinalFacts L X c := by
  intro c hc
  have hR := Base.roleReads hpre hX
  have l := (ProtocolRest.srPkg hpre hX b hI).lane c hc
  obtain ⟨hcm, hcmc⟩ := l.cm_ok
  refine ⟨(ProtocolRest.srPkg hpre hX b hI).cm c, (ProtocolRest.srPkg hpre hX b hI).p0 c,
    ((ProtocolRest.srPkg hpre hX b hI).ctx c hc).facts, hcm, hcmc,
    fun hx hxc => l.mma_thread hx hxc, ?_, ?_⟩
  · intro i pc sp he hm
    have := IpMma.final_first hpre hX b.facts hR he (by rw [hcmc]; exact hm)
    rwa [hcmc] at this
  · intro x hx hxc i pc sp he hm
    have hxe := l.mma_thread hx hxc
    obtain ⟨pcx, dx, sx, ax, mx, hxget⟩ := hx.get
    obtain ⟨xg, xk⟩ := x
    simp only at hxe ⊢
    subst hxe
    exact IpMma.mma_before_final hpre hX b.facts hR hxget he (by rw [hcmc]; exact hm)

/-- **The KV slots of every launched CTA** (`Lp.kv_of`, with the prologue's events
`Lp.preRing_of`): the slot's consumer is the package's committing lane. -/
theorem ProtocolRest.kv (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) :
    ∀ cta < L.grid, ∀ s : Fin 3, ∃ S : Ring.Kv.Slot,
    S.full = kvReady L cta s ∧ S.empty = kvEmpty L cta s ∧
      S.cm = (ProtocolRest.srPkg hpre hX b hI).cm cta ∧ Ring.Kv.Hyp L kernel asms X S :=
  Lp.kv_of hpre hX b.facts (Base.roleReads hpre hX) (Base.numPreRead hpre hX)
    (ProtocolRest.srPkg hpre hX b hI) (Lp.preRing_of hpre hX b.facts)

/-- **`Life.CopyObserved`** (`Lp.copyObserved_of`). -/
theorem ProtocolRest.copyObserved (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) :
    Life.CopyObserved L X :=
  Lp.copyObserved_of hpre hX b.facts (Base.roleReads hpre hX) (Base.numPreRead hpre hX)
    (Interface.baseWordRead_of hpre hX) (Base.numWordRead hpre hX)
    (ProtocolRest.srPkg hpre hX b hI)
    (Base.mmaBcast hpre hX b) (Lp.preRing_of hpre hX b.facts)

/-- **`Mbar.CtaRecords` of every launched CTA**, from the KV slots and the handshake package. -/
theorem ProtocolRest.records (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) :
    ∀ cta < L.grid, Mbar.CtaRecords L kernel asms mem0 X cta := by
  intro cta hc
  have hR := Base.roleReads hpre hX
  have l := (ProtocolRest.srPkg hpre hX b hI).lane cta hc
  obtain ⟨-, hcmc⟩ := l.cm_ok
  refine ⟨fun s =>
    (ProtocolRest.kv hpre hX b hI cta hc s).imp fun _ h => ⟨h.1, h.2.1, h.2.2.2⟩,
    (ProtocolRest.srPkg hpre hX b hI).cm cta, (ProtocolRest.srPkg hpre hX b hI).p0 cta,
    (ProtocolRest.srPkg hpre hX b hI).Soft cta, (ProtocolRest.srPkg hpre hX b hI).Mma cta,
    (ProtocolRest.srPkg hpre hX b hI).ctx cta hc, ?_⟩
  intro i pc sp he hm
  have := IpMma.final_first hpre hX b.facts hR he (by rw [hcmc]; exact hm)
  rwa [hcmc] at this

/-- **The QK MMAs have `f32` results** (`Qx.resultQk_of`), from the query elements
(`Qx.qk_a_real`) and the key elements (`Qy.elemB_of`) alone. -/
theorem ProtocolRest.resultQk (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) : Qx.ResultQk Q L X := by
  have hR := Base.roleReads hpre hX
  have hbw : BaseWordRead L X := Interface.baseWordRead_of hpre hX
  have hnw : NumWordRead Q L X := Base.numWordRead hpre hX
  let G := ProtocolRest.srPkg hpre hX b hI
  have hms : Pr.MmaStates Q L G :=
    Hs.mmaStates_pkg hpre hX b.facts hR hbw hnw hI
      (Vx.pkgRest_of hpre hX b.facts hR (Base.mmaBcast hpre hX b))
  have ht := Proof2.tmem1Facts hpre hX
  have hmd : Tmem1.MmaDoneDealloc L X :=
    Tmem1.mmaDoneDealloc_of hX (Vx.tmemLife_of hpre hX b.facts) (ProtocolRest.oFinal hpre hX b hI)
      (IpMma.dealloc_poll hpre hX b.facts)
  exact Qx.resultQk_of hpre hX b.facts
    (Pr.qkChain_of hpre hX b.facts (Tmem1.no_cp hX) (no_shift hX) G hms ht hmd)
    (fun hg he hσ hs _ hops hr hk => Qx.qk_a_real hpre hX b.facts b.tmpl hR b.bar1 hg he hσ hs
      hops hr hk)
    (fun hg he hσ hs hd hops hn hk => Qy.elemB_of hpre hX b.facts b.tmpl hR b.bar1
      (Base.numPreRead hpre hX) (Base.boxInBounds hpre hX) G
      (Wz.kvCopiesF_of hpre hX b.facts hR (Base.numPreRead hpre hX) G)
      (Base.mmaBcast hpre hX b) hg he hσ (.inl hs) hd hops hn hk)

/-- **The exchange of the row maximum receives score words** (`Interface.Lk.SmMaxOk`,
`Qy.smMaxOk_of`), from the QK MMAs' `f32` results. -/
theorem ProtocolRest.smMaxOk (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) :
    Interface.Lk.SmMaxOk Q L X := by
  have hR := Base.roleReads hpre hX
  have hbw : BaseWordRead L X := Interface.baseWordRead_of hpre hX
  have hnw : NumWordRead Q L X := Base.numWordRead hpre hX
  let G := ProtocolRest.srPkg hpre hX b hI
  have hms : Pr.MmaStates Q L G :=
    Hs.mmaStates_pkg hpre hX b.facts hR hbw hnw hI
      (Vx.pkgRest_of hpre hX b.facts hR (Base.mmaBcast hpre hX b))
  intro g k d e
  exact Qy.smMaxOk_of hpre hX b.facts hR hbw hnw (Tmem1.no_cp hX) (no_shift hX) G (fun _ => rfl)
    hms (Proof2.tmem1Facts hpre hX) (Vx.tmemLife_of hpre hX b.facts)
    (Rs.smBaseZero hpre hX b.facts hbw) (Interface.Lk.decAgree_every hpre hX b.facts hI)
    (Base.mmaBcast hpre hX b) (ProtocolRest.resultQk hpre hX b hI)

/-- **The softmax states have the real numbers** (`Interface.Lk.SmReal`): only the exchange of the
row maximum on words that are not score words clears the flag, and it receives score words
(`ProtocolRest.smMaxOk`). -/
theorem ProtocolRest.smReal (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) :
    Interface.Lk.SmReal Q L X :=
  Interface.Lk.smReal_of_max hX (ProtocolRest.smMaxOk hpre hX b hI)

/-- **The MMA warp's facts the values use**: the loop words (`Rs.mmaWords_of`), the accumulator
chains (`Pr.qkChain_of`, `Pr.oAccNext_of`) and the operand elements (`Qx.elemPrem_of` with
`Qy.elemRest_of`). -/
theorem ProtocolRest.mmaFacts (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) :
    Result.Mma.MmaWords Q L X ∧ Result.Mma.QkChain Q L X ∧ Qx.PvNext Q L X ∧
      Qx.ElemPrem Q L X := by
  have hR := Base.roleReads hpre hX
  have hbw : BaseWordRead L X := Interface.baseWordRead_of hpre hX
  have hnw : NumWordRead Q L X := Base.numWordRead hpre hX
  let G := ProtocolRest.srPkg hpre hX b hI
  have hms : Pr.MmaStates Q L G :=
    Hs.mmaStates_pkg hpre hX b.facts hR hbw hnw hI
      (Vx.pkgRest_of hpre hX b.facts hR (Base.mmaBcast hpre hX b))
  have ht := Proof2.tmem1Facts hpre hX
  have hmd : Tmem1.MmaDoneDealloc L X :=
    Tmem1.mmaDoneDealloc_of hX (Vx.tmemLife_of hpre hX b.facts) (ProtocolRest.oFinal hpre hX b hI)
      (IpMma.dealloc_poll hpre hX b.facts)
  exact ⟨Rs.mmaWords_of hpre hX b.facts hbw hnw,
    Pr.qkChain_of hpre hX b.facts (Tmem1.no_cp hX) (no_shift hX) G hms ht hmd,
    fun hj hσ hs => Pr.oAccNext_of hpre hX b.facts (Tmem1.no_cp hX) (no_shift hX) G hms ht hmd
      hj hσ hs,
    Qx.elemPrem_of hpre hX b.facts b.tmpl hR b.bar1
      (Qy.elemRest_of hpre hX b.facts b.tmpl hR b.bar1 (Base.numPreRead hpre hX) hbw hnw
        (Base.boxInBounds hpre hX) (Tmem1.no_cp hX) (no_shift hX) G (fun _ => rfl) hms ht hmd
        (Interface.Lk.decAgree_every hpre hX b.facts hI)
        (fun hg hσ hs he => Qy.oLoadSrcF hpre hX b.facts hR hbw hnw (Tmem1.no_cp hX) (no_shift hX)
          G (fun _ => rfl) hms ht (Vx.tmemLife_of hpre hX b.facts)
          (Rs.smBaseZero hpre hX b.facts hbw)
          (Interface.Lk.decAgree_every hpre hX b.facts hI) (Base.mmaBcast hpre hX b)
          hg hσ hs he)
        (Base.mmaBcast hpre hX b) (ProtocolRest.smReal hpre hX b hI))⟩

/-- **Every result cell of a completed MMA has an `f32` value** (`Qx.result_of`). -/
theorem ProtocolRest.resultF32 (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) :
    Qx.ResultF32 L X := by
  obtain ⟨hw, hch, hnext, E⟩ := ProtocolRest.mmaFacts hpre hX b hI
  exact Qx.result_of hpre hX b.facts hw hch hnext E

/-- **Every completed MMA's unmasked results have derived values** (`TcMma.CompletedValues`),
from `ProtocolRest.resultF32`. -/
theorem ProtocolRest.values (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) :
    ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
      X.MmaIssue i d s acc mask → CompletedValues L asms X i := by
  rintro ⟨g, k⟩ d s acc mask - hd cell ⟨d', s', acc', mask', row, col, ⟨pc, he⟩, hwc⟩
  obtain ⟨x, hx⟩ := ProtocolRest.resultF32 hpre hX b hI k (event_thread_lt hX he) he hd hwc
  exact ⟨_, hx⟩

/-- **The last PV MMA is the source of the epilogue's load of every row**
(`Rs.oSourceAll_of`). -/
theorem ProtocolRest.oSourceAll (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) :
    Rs.OSourceAll Q L X := by
  have hR := Base.roleReads hpre hX
  have hbw : BaseWordRead L X := Interface.baseWordRead_of hpre hX
  have hnw : NumWordRead Q L X := Base.numWordRead hpre hX
  let G := ProtocolRest.srPkg hpre hX b hI
  have hms : Pr.MmaStates Q L G :=
    Hs.mmaStates_pkg hpre hX b.facts hR hbw hnw hI
      (Vx.pkgRest_of hpre hX b.facts hR (Base.mmaBcast hpre hX b))
  have ht := Proof2.tmem1Facts hpre hX
  have hO : Rs.OSrcPrem Q L kernel Assumptions.all mem0 X G :=
    { commit_once := fun c hc i pc sp he hm => by
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
      epiTm := Interface.epiTm_of hpre hX b.facts hbw
      ostBound := Rr.ostBound_of hpre hX b.facts G }
  intro g k k0 pc d d0 vals
  exact Rs.oSourceAll_of hpre hX b.facts (Base.mmaBcast hpre hX b) hbw hnw (Tmem1.no_cp hX)
    (no_shift hX) G hms hO ht
    (Vx.tmemLife_of hpre hX b.facts)

/-- **The epilogue's load check** (`Interface.Lk.EpiLoadOk`, `Qx.epiLoad_of`). -/
theorem ProtocolRest.epiLoad (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) :
    Interface.Lk.EpiLoadOk Q L X := by
  intro g k d e
  exact Qx.epiLoad_of hpre hX b.facts (ProtocolRest.smReal hpre hX b hI)
    (ProtocolRest.oSourceAll hpre hX b hI)
    (ProtocolRest.resultF32 hpre hX b hI)

/-- **The rescale load's check** (`Interface.Lk.SmOLoadOk`, `Qy.smOLoad_of`). -/
theorem ProtocolRest.smOLoad (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) :
    Interface.Lk.SmOLoadOk Q L X := by
  have hR := Base.roleReads hpre hX
  have hbw : BaseWordRead L X := Interface.baseWordRead_of hpre hX
  have hnw : NumWordRead Q L X := Base.numWordRead hpre hX
  let G := ProtocolRest.srPkg hpre hX b hI
  have hms : Pr.MmaStates Q L G :=
    Hs.mmaStates_pkg hpre hX b.facts hR hbw hnw hI
      (Vx.pkgRest_of hpre hX b.facts hR (Base.mmaBcast hpre hX b))
  intro g k d
  exact Qy.smOLoad_of hpre hX b.facts hR hbw hnw (Tmem1.no_cp hX) (no_shift hX) G (fun _ => rfl)
    hms (Proof2.tmem1Facts hpre hX) (Vx.tmemLife_of hpre hX b.facts)
    (Rs.smBaseZero hpre hX b.facts hbw) (Interface.Lk.decAgree_every hpre hX b.facts hI)
    (Base.mmaBcast hpre hX b) (ProtocolRest.resultF32 hpre hX b hI)

/-- **The S load's check** (`Interface.Lk.SmSLoadOk`, `Qy.smSLoad_of`). -/
theorem ProtocolRest.smSLoad (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) :
    Interface.Lk.SmSLoadOk Q L X := by
  have hR := Base.roleReads hpre hX
  have hbw : BaseWordRead L X := Interface.baseWordRead_of hpre hX
  have hnw : NumWordRead Q L X := Base.numWordRead hpre hX
  let G := ProtocolRest.srPkg hpre hX b hI
  have hms : Pr.MmaStates Q L G :=
    Hs.mmaStates_pkg hpre hX b.facts hR hbw hnw hI
      (Vx.pkgRest_of hpre hX b.facts hR (Base.mmaBcast hpre hX b))
  intro g k pc a d vals sh
  exact Qy.smSLoad_of hpre hX b.facts hR hbw hnw (Tmem1.no_cp hX) (no_shift hX) G (fun _ => rfl)
    hms (Proof2.tmem1Facts hpre hX) (Vx.tmemLife_of hpre hX b.facts)
    (Rs.smBaseZero hpre hX b.facts hbw) (Interface.Lk.decAgree_every hpre hX b.facts hI)
    (Base.mmaBcast hpre hX b) (ProtocolRest.resultF32 hpre hX b hI)

/-- **The score stage's check** (`Interface.Lk.SmScoreOk`, `Qy.smScore_of`). -/
theorem ProtocolRest.smScore (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) :
    Interface.Lk.SmScoreOk Q L X := by
  have hR := Base.roleReads hpre hX
  have hbw : BaseWordRead L X := Interface.baseWordRead_of hpre hX
  have hnw : NumWordRead Q L X := Base.numWordRead hpre hX
  let G := ProtocolRest.srPkg hpre hX b hI
  have hms : Pr.MmaStates Q L G :=
    Hs.mmaStates_pkg hpre hX b.facts hR hbw hnw hI
      (Vx.pkgRest_of hpre hX b.facts hR (Base.mmaBcast hpre hX b))
  intro g k d
  exact Qy.smScore_of hpre hX b.facts hR hbw hnw (Tmem1.no_cp hX) (no_shift hX) G (fun _ => rfl)
    hms (Proof2.tmem1Facts hpre hX) (Vx.tmemLife_of hpre hX b.facts)
    (Rs.smBaseZero hpre hX b.facts hbw) (Interface.Lk.decAgree_every hpre hX b.facts hI)
    (Base.mmaBcast hpre hX b) (ProtocolRest.resultF32 hpre hX b hI)

/-- **No required Tensor Memory read lacks a source** (`Qx.tcSource_of`, with `Qy.sourceRest_of`
and `Qy.ldSm_of`). -/
theorem ProtocolRest.tcSource (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) :
    ¬ TcMma.SourceUnsafe L asms X := by
  obtain ⟨hw, hch, hnext, E⟩ := ProtocolRest.mmaFacts hpre hX b hI
  have hR := Base.roleReads hpre hX
  have hbw : BaseWordRead L X := Interface.baseWordRead_of hpre hX
  have hnw : NumWordRead Q L X := Base.numWordRead hpre hX
  let G := ProtocolRest.srPkg hpre hX b hI
  have hms : Pr.MmaStates Q L G :=
    Hs.mmaStates_pkg hpre hX b.facts hR hbw hnw hI
      (Vx.pkgRest_of hpre hX b.facts hR (Base.mmaBcast hpre hX b))
  have ht := Proof2.tmem1Facts hpre hX
  have hmd : Tmem1.MmaDoneDealloc L X :=
    Tmem1.mmaDoneDealloc_of hX (Vx.tmemLife_of hpre hX b.facts) (ProtocolRest.oFinal hpre hX b hI)
      (IpMma.dealloc_poll hpre hX b.facts)
  exact Qx.tcSource_of hpre hX b.facts hw hch hnext E (ProtocolRest.resultF32 hpre hX b hI)
    (ProtocolRest.oSourceAll hpre hX b hI)
    (Qy.sourceRest_of hpre hX b.facts hbw hnw (Tmem1.no_cp hX) (no_shift hX) G (fun _ => rfl) hms ht
      hmd (Interface.Lk.decAgree_every hpre hX b.facts hI)
      (Qy.ldSm_of hpre hX b.facts hR hbw hnw (Tmem1.no_cp hX) (no_shift hX) G (fun _ => rfl) hms
        ht (Vx.tmemLife_of hpre hX b.facts) (Rs.smBaseZero hpre hX b.facts hbw)
        (Interface.Lk.decAgree_every hpre hX b.facts hI) (Base.mmaBcast hpre hX b)
        (ProtocolRest.resultF32 hpre hX b hI)))

/-- **`Safety.Protocol`** from the thread-layer base, the proved protocol theorems and the
remaining premises. -/
theorem protocol_of (hsm : Interface.Lk.LaneAgreeSm Q L X) (halpha : Bar.AlphaAgree L X)
    (hI : ∀ i, Interface.Lk.ScratchIt Q L X i) : Safety.Protocol Q L X where
  faultFree := faultFree_of hpre hX b.facts (Interface.baseWordRead_of hpre hX)
    (Base.numWordRead hpre hX) (Base.roleReads hpre hX) (Base.numPreRead hpre hX)
    (Base.mmaBcast hpre hX b) (Interface.Lk.faultRest_of hpre hX b.facts (Base.roleReads hpre hX)
      (Rs.smBaseZero hpre hX b.facts (Interface.baseWordRead_of hpre hX)) hI
      (ProtocolRest.smOLoad hpre hX b hI) (ProtocolRest.smSLoad hpre hX b hI)
      (ProtocolRest.smScore hpre hX b hI) (ProtocolRest.smMaxOk hpre hX b hI)
      (ProtocolRest.epiLoad hpre hX b hI))
  sharedPlaced := Proof2.sharedPlaced hpre hX
  globalPlaced := Proof2.global_placed hpre hX
  globalReads := Proof2.global_reads hpre hX
  odoneWait := Base.odoneWait hpre hX b
  boxInBounds := Base.boxInBounds hpre hX
  order := Sx.order_of hpre hX b.facts b.tmpl (Base.roleReads hpre hX) b.bar1
    (Interface.baseWordRead_of hpre hX) hI
  recordsOk := Mbar.recordsOk_of_ctas hX (mbarPlaced_of hpre hX b.facts (Base.odoneWait hpre hX b))
    (ProtocolRest.records hpre hX b hI)
  objectsPublished := Proof2.objects_published hpre hX
  mbarInit := Proof2.mbar_init hpre hX
  barLanes := Base.barLanes hpre hX b hsm
  ctaBar := Bar.ctaBar_of_roleReads hpre hX b.facts.sound b.facts.tracked
    (Base.roleReads hpre hX) halpha
  tcAligned := Base.tcAligned hpre hX b hsm
  barAligned := Base.barAligned hpre hX b hsm
  regAligned := Proof2.reg_aligned hpre hX
  warpUniform := Wq.warpUniform_of hpre (Proof2.poll_synced hpre hX)
  lifetime := Life.lifetime hpre hX b.facts (Base.odoneWait hpre hX b) b.tmpl
    (ProtocolRest.oFinal hpre hX b hI) (ProtocolRest.copyObserved hpre hX b hI)
    (Rr.sObserved_of hpre hX b.facts (Base.mmaBcast hpre hX b) (Interface.baseWordRead_of hpre hX)
    (Base.numWordRead hpre hX)
      (Base.roleReads hpre hX) (ProtocolRest.srPkg hpre hX b hI))
    (IpMma.nextCommit hpre hX b.facts)
  regAgree := Proof2.reg_agree hpre hX
  regSync := Proof2.reg_sync hpre hX
  tcSource := ProtocolRest.tcSource hpre hX b hI
  tmemAccess := Tmem1.no_access_unsafe hX
    (Proof2.tmem1Facts hpre hX)
    ⟨Tmem1.access_shape_of hpre hX b.facts
      (Rs.smBaseZero hpre hX b.facts (Interface.baseWordRead_of hpre hX)) (no_shift hX)
      (Tmem1.no_cp hX), Tmem1.no_cp hX, no_shift hX⟩ (Vx.tmemLife_of hpre hX b.facts)
    (Tmem1.mmaDoneDealloc_of hX
      (Vx.tmemLife_of hpre hX b.facts) (ProtocolRest.oFinal hpre hX b hI)
      (IpMma.dealloc_poll hpre hX b.facts))
  tcWrites := by
    let G := ProtocolRest.srPkg hpre hX b hI
    exact Sr.no_writes_unsafe hX (Tmem1.no_cp hX) (no_shift hX) G.cm G.p0 G.tm G.Soft G.Mma
      G.ctx G.lane
  tcInstr := Tmem1.tcInstr_of hpre hX b.facts (Interface.baseWordRead_of hpre hX)
    (Base.numWordRead hpre hX) (ProtocolRest.values hpre hX b hI)
  tcReads := by
    let G := ProtocolRest.srPkg hpre hX b hI
    exact Sr.no_reads_unsafe hX (Tmem1.no_cp hX) (no_shift hX) G.cm G.p0 G.tm G.Soft G.Mma
      G.ctx G.lane

end
end PTX.Kernels.InklingRelDecode.Proof.Assemble
