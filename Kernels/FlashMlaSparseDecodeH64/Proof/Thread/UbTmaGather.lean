-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbTma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GemmRawGather
import Kernels.FlashMlaSparseDecodeH64.Proof.Geometry.Maps
import Lemmas.Protocol.NamedBarSources

public section

/-! # Defined templates for the producer's gather4 issues -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbTma

open PTX PTX.Proof PTX.Flow Wg1Tma

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private theorem gather_map (hpre : Pre P L mem0) {d : D} {k : Fin 16}
    (hi : Inv P L g d) (hsite : d.site = .issue k) :
    ∃ desc : TensorDescriptor.Descriptor 1,
      L.tensorMaps (P.param1Base + Wg1Tma.kvOff d) = some ⟨1, desc⟩ ∧
        TensorDescriptor.Valid desc ∧ desc.box.size 1 = 1 := by
  by_cases hmain : d.block < numOrigBlocks d.len0
  · rw [Wg1Tma.kvOff, ite_eq_left hmain]
    exact ⟨_, hpre.mapKVBind, Geometry.mapKv_valid_of_pre hpre, rfl⟩
  · have he := Wg1Tma.extra_active hpre hi (by simp [hsite]) (by simp [hsite]) hmain
    rw [Wg1Tma.kvOff, ite_eq_right hmain]
    exact ⟨_, hpre.mapExtraKvBind.resolve_left he, Geometry.mapExtraKv_valid_of_pre hpre he, rfl⟩

private theorem operand_live {d : D} {k : Fin 16} (hd : d.site = .issue k) :
    let regs := (Flow.live d.site.pc).filter tracked.contains
    3049 ∈ regs ∧ 3050 ∈ regs ∧ 696 ∈ regs ∧ issueRegs.getD k.val 0 ∈ regs := by
  rw [hd]
  fin_cases k <;> decide +kernel

/-- The actual gather instruction has its defined TMA issue template. -/
theorem gather_template (hpre : Pre P L mem0) (hGrid : L.clusterGridValid)
    (hg : g < L.threads) {d : D} {k : Fin 16} {t : TState}
    (hd : d.site = .issue k) (ha : (Wg1Tma.code P L g).AtD d t)
    (hi : Inv P L g d) (hw : GemmRawGather.Words P L g d k) :
    ∃ addr spec, eventTmpl Assumptions.all L g t (issueInstr k).op =
      .tensorIssue addr spec (PTX.next t) := by
  let addr := P.param1Base + Wg1Tma.kvOff d
  let dst := issueRegs.getD k.val 0
  let cs := Opnd.reg 691 :: ((coordRegs.drop (4 * k.val)).take 4).map Opnd.reg
  let dLoc : Loc := ⟨.shared, ctaOf L g, L.sharedBase + issueDst d.buf k.val⟩
  let mLoc : Loc := ⟨.shared, ctaOf L g, L.sharedBase + rawReadyOff d.buf⟩
  let b (j : Fin 4) :=
    BitVec.ofNat 64 (coordAt P L g d.block (coordPos k.val j.val) % 2 ^ 32)
  let vs : List (BitVec 64) := 0 :: [b 0, b 1, b 2, b 3]
  let origin (axis : Fin 2) := (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt
  let rows (j : Fin 4) := (BitVec.ofNat 32 (vs.getD (j.val + 1) 0).toNat).toInt
  obtain ⟨desc, hMap, hValid, hRow⟩ := gather_map hpre hi hd
  obtain ⟨hMapLive, hPolLive, hMLive, hDLive⟩ := operand_live hd
  have hAddr : addr < 2 ^ 64 := by
    have hkv : Wg1Tma.kvOff d < 1024 := by unfold Wg1Tma.kvOff; split <;> decide
    have := hpre.param1Range
    dsimp [addr]
    omega
  have hMapAlign : addr % 64 = 0 := by
    have hp := hpre.param1Align
    dsimp [addr, Wg1Tma.kvOff]
    split <;> omega
  have hMapReg : t.regs 3049 = some (b64 addr) := by
    have h := atD_reg ha hMapLive
    have hv : (P.param1Base + Wg1Tma.kvOff d) % 2 ^ 64 = addr :=
      Nat.mod_eq_of_lt hAddr
    simpa only [Wg1Tma.valueOf, Wg1Tma.table, PTX.Flow.lookupLit, Option.getD_some, hv] using h
  have hMapAddr : tensorMapAddress L g t (.reg 3049) = .ok addr := by
    simp [tensorMapAddress, readValue, readReg, hMapReg, readBits_b64 hMapReg hAddr,
      b64, toNat_ofNat_lt hAddr, bind, Except.bind, pure, Except.pure]
  have hLen : cs.length = 5 := by fin_cases k <;> rfl
  have hMap' : L.tensorMaps addr = some ⟨1, desc⟩ := hMap
  have hTensorMap : tensorMap L g t (.reg 3049) cs .fourRows = .ok (addr, ⟨1, desc⟩) := by
    simp only [tensorMap, hMapAddr, hMapAlign, hMap', hLen, TensorMode.coordinates, hValid, hRow,
      bind, Except.bind, pure, Except.pure, ↓reduceIte,
      and_self, or_true]
  have hPol : cachePolicyRead L g t (some (.reg 3050)) = .ok () := by
    have hReg : t.regs 3050 = some (b64 1364590687093260288) := atD_reg ha hPolLive
    simp [cachePolicyRead, readBits_b64 hReg (by decide), bind, Except.bind, pure, Except.pure]
  have hBase := sharedBase_lt hpre
  have hBuf := hi.buf_lt
  have hDReg : t.regs dst = some (sb L (issueDst d.buf k.val)) := by
    rw [atD_reg ha hDLive]
    fin_cases k <;> rfl
  have hDFit : L.sharedBase + issueDst d.buf k.val < 2 ^ 32 := by
    have hk := k.isLt
    unfold issueDst rawBase
    omega
  have hDLoc : sharedEffAddr L g t false dst 0 = .ok dLoc :=
    effAddr_b32 hDReg hDFit
  have hDAlign : dLoc.addr % 128 = 0 := by
    apply issueDst_aligned
    rw [hpre.sharedBase]
    have := hpre.sharedAlignment
    omega
  have hMReg : t.regs 696 = some (sb L (rawReadyOff d.buf)) := atD_reg ha hMLive
  have hMFit : L.sharedBase + rawReadyOff d.buf < 2 ^ 32 := by
    unfold rawReadyOff
    omega
  have hMLoc : mbarLoc L g t 696 0 = .ok mLoc :=
    mbarLoc_b32 hMReg hMFit (sharedAddr_align hpre (by unfold rawReadyOff; omega))
  have hCoords : cs.mapM (readBits L g t 32) = .ok vs := GemmRawGather.read_coordinates k hd ha hw
  have hBox : requireBoxAligned desc.fourRows
      (fun axis : Fin 2 => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt) = .ok () :=
    (requireBoxAligned_eq_ok _ _).mpr (by simp [TensorDescriptor.BoxAligned, vs])
  let s : TensorCopy.Spec := ⟨⟨1, desc.fourRows, origin, dLoc, some rows⟩, mLoc, false, .one⟩
  have hCopy : tensorLoadCopy L g t false false dst 0 (.reg 3049) cs 696 0 .fourRows =
      .ok (addr, s) := by
    simp only [tensorLoadCopy, hTensorMap, hDLoc, hDAlign, hMLoc, hCoords, TensorMode.transfer,
      TensorMode.rowCoordinates, hBox, bind, Except.bind, pure, Except.pure,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  have hcta : ctaOf L g < L.grid := PTX.NamedBar.cta_lt hg
  have hself : CtaInCluster L (ctaOf L g) (ctaOf L g) := ⟨hcta, hcta, rfl⟩
  have hRoute : TensorRoute L (g / L.block) false .one dLoc mLoc :=
    ⟨hGrid, rfl, rfl, hself, hself, fun _ => ⟨rfl, rfl⟩, (sameCtaGroup_iff ..).mpr ⟨hself, rfl⟩⟩
  refine ⟨addr, s, ?_⟩
  change tensorTmpl L g t (.cpTensor false false dst 0 (.reg 3049) cs 696 0 none .fourRows
    (some (.reg 3050))) = .tensorIssue addr s (PTX.next t)
  have hRoute' : TensorRoute L (g / L.block) s.clusterAddress s.group s.sharedBase s.mbar := hRoute
  simp only [tensorTmpl, ofExec, hPol, hCopy, hRoute', bind, Except.bind, pure, Except.pure,
    ↓reduceIte]

/-- Every represented event of the KV producer has a defined template, when its gather issues
read the index warp's words. -/
theorem tmpl_ok (hpre : Pre P L mem0) (hGrid : L.clusterGridValid) (hg : g < L.threads)
    {d : D} {t : TState} {ins : Instr} (ha : (Machine.code P L g).AtD (.tma d) t)
    (hi : Inv P L g d) (hc : kernel.code[(Machine.code P L g).pc (.tma d)]? = some ins)
    (hw : ∀ k, d.site = .issue k → GemmRawGather.Words P L g d k)
    (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  by_cases h : ∃ k, d.site = .issue k
  · obtain ⟨k, hd⟩ := h
    have hcode : kernel.code[d.site.pc]? = some ins := hc
    rw [hd] at hcode
    obtain rfl := Option.some.inj (hcode.symm.trans (issueInstr_code k))
    obtain ⟨_, _, hTmpl⟩ := gather_template hpre hGrid hg hd ha hi (hw k hd)
    rw [hTmpl]
    intro h
    cases h
  · exact control_tmpl_ok hpre ha hi hc (fun k hk => h ⟨k, hk⟩) f

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbTma
