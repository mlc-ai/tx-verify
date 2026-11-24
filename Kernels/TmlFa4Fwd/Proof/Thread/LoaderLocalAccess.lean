-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLocalScalar
public import Lemmas.Flow.LocalStoreSpace
import Lemmas.Step.CtaBar

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader (RingShape loaderVector)
open LocalAccessCode

noncomputable section

private def ordinaryLocalOp : Op → Bool
  | .mem ma => ma.space == some .local
  | _ => false

private theorem localSitesAudit : OpPcsFast kernel.code ordinaryLocalOp
    (scalarSites.map ScalarSite.accessPc ++ pointerLoads.map PointerLoad.pc) = true := by
  decide +kernel

private theorem noDirectLocalRead : kernel.code.all (fun i => loadSpace i.op != some .local) =
    true := by
  decide +kernel

private theorem noDirectLocalWrite : kernel.code.all (fun i => storeSpace i.op != some .local) =
    true := by
  decide +kernel

private theorem dynamicLocalRead : kernel.code.all
    (fun i => !readOp i.op || !dynamicAccess i.op || ordinaryLocalOp i.op) = true := by
  decide +kernel

private theorem dynamicLocalWrite : kernel.code.all
    (fun i => !writeOp i.op || !dynamicAccess i.op || ordinaryLocalOp i.op) = true := by
  decide +kernel

theorem scalarLocation {site : ScalarSite} (hs : site ∈ scalarSites) :
    506 ≤ site.accessPc ∧ site.accessPc < 1901 ∧
      ∃ ins ma, kernel.code[site.accessPc]? = some ins ∧ ins.op = .mem ma ∧
        ma.space = some .local ∧ ma.addr.base = .reg site.addressReg 64 ∧ ma.addr.off = 0 ∧
        ma.sem = .weak ∧ ma.vec = 1 ∧ ma.elem.width / 8 = site.word ∧
        loaderVector ins.op = false ∧ (ma.kind = .load ∨ ma.kind = .store) := by
  let check := fun s : ScalarSite =>
    decide (506 ≤ s.accessPc ∧ s.accessPc < 1901) &&
      match kernel.code[s.accessPc]? with
      | some i => match i.op with
        | .mem ma =>
          decide (ma.space = some .local ∧ ma.addr.base = .reg s.addressReg 64 ∧ ma.addr.off = 0 ∧
            ma.sem = .weak ∧ ma.vec = 1 ∧ ma.elem.width / 8 = s.word) &&
            (!loaderVector i.op && (ma.kind == .load || ma.kind == .store))
        | _ => false
      | none => false
  have hAudit : scalarSites.all check = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAudit site hs
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hLo, hHi⟩, h⟩ := h
  cases hi : kernel.code[site.accessPc]? with
  | none => simp [hi] at h
  | some ins =>
    cases ho : ins.op with
    | mem ma =>
      obtain ⟨hShape, hVector, hKind⟩ : _ ∧ loaderVector ins.op = false ∧
          (ma.kind = .load ∨ ma.kind = .store) := by
        simpa only [hi, ho, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
          decide_eq_true_eq, Bool.not_eq_true'] using h
      exact ⟨hLo, hHi, ins, ma, rfl, ho, hShape.1, hShape.2.1, hShape.2.2.1,
        hShape.2.2.2.1, hShape.2.2.2.2.1, hShape.2.2.2.2.2, hVector, hKind⟩
    | _ => simp [hi, ho] at h

theorem scalarFootprint {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {t : TState} {site : ScalarSite}
    {ma : MemAccess} {a : Acc} (entry : Fin 2)
    (hReg : t.regs site.addressReg = some (b64 (l.localBase + kvLocalOffset site.array entry)))
    (hSub : t.sub = 0) (hSpace : ma.space = some .local)
    (hBase : ma.addr.base = .reg site.addressReg 64) (hOff : ma.addr.off = 0)
    (hSem : ma.sem = .weak) (hVec : ma.vec = 1) (hWidth : ma.elem.width / 8 = site.word)
    (hAcc : accessAcc l g t ma = .ok a) :
    a = { loc := ⟨.local, g, l.localBase + kvLocalOffset site.array entry⟩
          size := site.word } := by
  have hOffBound := kvLocalOffset_bound site.array entry (byte := 0)
    (by split <;> decide)
  have hBound : l.localBase + kvLocalOffset site.array entry < 2 ^ 64 := by
    have := hp.localMemory.2.1
    omega
  have hAlign : (l.localBase + kvLocalOffset site.array entry) % site.word = 0 :=
    kvLocalOffset_aligned site.array entry hp.localMemory.1
  have hAddr : wrapAddr 64 (BitVec.ofNat 64 (l.localBase + kvLocalOffset site.array entry)) 0 =
      l.localBase + kvLocalOffset site.array entry := by
    simp only [wrapAddr, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      truncBits_ofNat hBound (by decide), toNat_ofNat_lt hBound]
  rw [accessAcc_of_weak hSem, accessLoc_local_reg hSpace hBase (readBits_b64 hReg hBound),
    hOff, hAddr] at hAcc
  simp only [bind, Except.bind, hVec, hWidth] at hAcc
  split at hAcc
  · contradiction
  · have hPos : site.word ≠ 0 := by unfold ScalarSite.word; split <;> decide
    simp [elemAcc, hPos, hAlign, hSub, Loc.at, pure, Except.pure] at hAcc
    exact hAcc.symm

private theorem scalarAccess {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} (hg : g < l.threads) {t : TState} {site : ScalarSite}
    {ma : MemAccess} {a : Acc} (entry : Fin 2)
    (hReg : t.regs site.addressReg = some (b64 (l.localBase + kvLocalOffset site.array entry)))
    (hSub : t.sub = 0) (hSpace : ma.space = some .local)
    (hBase : ma.addr.base = .reg site.addressReg 64) (hOff : ma.addr.off = 0)
    (hSem : ma.sem = .weak) (hVec : ma.vec = 1) (hWidth : ma.elem.width / 8 = site.word)
    (hAcc : accessAcc l g t ma = .ok a) :
    StackAccess l m g a ∧ a.loc.addr % a.size = 0 := by
  have hAddr := scalarFootprint hp entry hReg hSub hSpace hBase hOff hSem hVec hWidth hAcc
  subst a
  have hStack := stackCell hp (off := 0) (size := site.word) hg site.array entry
    (by simp [ScalarSite.word])
  exact ⟨by simpa only [Nat.add_zero] using hStack,
    kvLocalOffset_aligned site.array entry hp.localMemory.1⟩

private theorem indexedEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {e : Event} (he : X.get i = some e) {site : ScalarSite}
    (hs : site ∈ scalarSites) (hSite : e.pc = site.accessPc) {a : Acc}
    (hKind : (∃ bs, e.kind = .rd a bs) ∨ ∃ data, e.kind = .wr a data) :
    StackAccess l m i.1 a ∧ a.loc.addr % a.size = 0 := by
  obtain ⟨hLo, hHi, ins, ma, hCode, hOp, hSpace, hBase, hOff,
    hSem, hVec, hWidth, hVector, hMemKind⟩ := scalarLocation hs
  obtain ⟨t, o, entry, ht, hShape, hReg, hStep⟩ :=
    eventScalarAddress hp hX he (hSite.symm ▸ hLo) (hSite.symm ▸ hHi) site hs hSite
  have hNotEnd : ¬ Ends e := by
    rcases hKind with ⟨bs, hKind⟩ | ⟨data, hKind⟩ <;> simp [Ends, hKind]
  obtain ⟨u, rfl⟩ : ∃ u, o = some u := by
    cases o with
    | none =>
      obtain ⟨_, _, hFire⟩ := hStep
      exact (hNotEnd (fires_none_ends hFire)).elim
    | some u => exact ⟨u, rfl⟩
  have hPc : t.pc = site.accessPc := ht.trans hSite
  obtain ⟨actual, hActual, _, hFires⟩ := estep_event_source hStep
  rw [hPc, hCode] at hActual
  obtain rfl := Option.some.inj hActual
  have hSub : t.sub = 0 := by
    by_contra! hn
    have hOne : t.sub = 1 := by have := hShape.1.1; omega
    obtain ⟨op, hc, hv, _⟩ := hShape.1.2 hOne
    rw [hPc, hCode] at hc
    rw [congrArg Instr.op (Option.some.inj hc), hv] at hVector
    cases hVector
  rw [hOp] at hFires
  obtain ⟨pos, ek⟩ := e
  change t.pc = pos at ht
  rw [ht] at hFires
  rcases hKind with ⟨bs, hk⟩ | ⟨data, hk⟩
  · change ek = .rd a bs at hk
    subst ek
    have hc : ma.kind = .load := by
      rcases hMemKind with hLoad | hStore
      · exact hLoad
      · have hRead := fires_read_op hFires rfl
        simp [readOp, hStore] at hRead
    have hAcc := fires_localLoadAccess hSpace hc hBase hFires
    exact scalarAccess hp (Step.CtaBar.thread_lt_of_get hX he) entry hReg hSub hSpace
      hBase hOff hSem hVec hWidth hAcc
  · change ek = .wr a data at hk
    subst ek
    have hc : ma.kind = .store := by
      rcases hMemKind with hLoad | hStore
      · have hWrite := fires_write_op hFires rfl
        simp [writeOp, hLoad] at hWrite
      · exact hStore
    have hAcc := fires_localStoreAccess hSpace hc hBase hFires
    exact scalarAccess hp (Step.CtaBar.thread_lt_of_get hX he) entry hReg hSub hSpace
      hBase hOff hSem hVec hWidth hAcc

variable {l : Launch} {m : Mem0} {X : Execution}

/-- Classify actual lane-local reads through the exhaustive instruction audit. -/
theorem LocalAccessCode.localReadSite (hX : Consistent l kernel Assumptions.all m X) {i : EvId}
    {a : Acc} {bs : List (Option Byte)} (hr : X.Reads i a bs) (hLocal : a.loc.space = .local) :
    PointerReload X i ∨ ∃ site ∈ scalarSites, ∃ pc,
      X.get i = some ⟨pc, .rd a bs⟩ ∧ pc = site.accessPc ∧
      ∃ ins, kernel.code[pc]? = some ins ∧ readOp ins.op = true := by
  obtain ⟨pc, he⟩ := hr
  rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hf
  have hm := List.mem_of_getElem? hc
  rcases fires_read_loc hf rfl with ⟨hs, _⟩ | hd
  · have checked := List.all_eq_true.mp noDirectLocalRead ins hm
    simp [hs, hLocal] at checked
  have hop : ordinaryLocalOp ins.op = true := by
    simpa only [fires_read_op hf rfl, hd, Bool.not_true, Bool.false_or]
      using List.all_eq_true.mp dynamicLocalRead ins hm
  rcases List.mem_append.mp (OpPcsFast.mem localSitesAudit hc hop) with hm | hm
  · obtain ⟨site, hs, hPc⟩ := List.mem_map.mp hm
    exact .inr ⟨site, hs, pc, he, hPc.symm, ins, hc, fires_read_op hf rfl⟩
  · exact .inl ⟨_, he, hm⟩

/-- Every actual ordinary local load lies in its issuing thread's aligned, allocated stack. -/
theorem localReadStack {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {a : Acc} {bs : List (Option Byte)} (hr : X.Reads i a bs)
    (hLocal : a.loc.space = .local) :
    StackAccess l m i.1 a ∧ a.loc.addr % a.size = 0 := by
  rcases localReadSite hX hr hLocal with hPointer | ⟨site, hs, _, he, hPc, _⟩
  · obtain ⟨hStack, hAlign, hWidth⟩ := pointerReloadStackAccess hp hX hr hPointer
    exact ⟨hStack, by simpa only [hWidth] using hAlign⟩
  · exact indexedEvent hp hX he hs hPc (.inl ⟨bs, rfl⟩)

private theorem pointerSitesReadOnly {s : PointerLoad} (hs : s ∈ pointerLoads) :
    ∃ ins, kernel.code[s.pc]? = some ins ∧ writeOp ins.op = false := by
  refine ⟨_, (pointerLoadDecoded s hs).2.2, ?_⟩
  rfl

/-- An actual local store comes from the audited scalar stack sites. -/
theorem localWriteSite (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {a : Acc}
    {data : List Byte} (hw : X.Writes i a data) (hLocal : a.loc.space = .local) :
    ∃ site, site ∈ scalarSites ∧ X.get i = some ⟨site.accessPc, .wr a data⟩ := by
  obtain ⟨pc, he⟩ := hw
  rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hf
  have hm := List.mem_of_getElem? hc
  rcases fires_write_space hf rfl with hs | hd
  · have checked := List.all_eq_true.mp noDirectLocalWrite ins hm
    simp [hs, hLocal] at checked
  have hop : ordinaryLocalOp ins.op = true := by
    simpa only [fires_write_op hf rfl, hd, Bool.not_true, Bool.false_or]
      using List.all_eq_true.mp dynamicLocalWrite ins hm
  rcases List.mem_append.mp (OpPcsFast.mem localSitesAudit hc hop) with hm | hm
  · obtain ⟨site, hs, hPc⟩ := List.mem_map.mp hm
    exact ⟨site, hs, hPc ▸ he⟩
  · obtain ⟨site, hs, hPc⟩ := List.mem_map.mp hm
    obtain ⟨ins', hc', hRead⟩ := pointerSitesReadOnly hs
    change site.pc = pc at hPc
    rw [hPc, hc] at hc'
    obtain rfl := Option.some.inj hc'
    rw [fires_write_op hf rfl] at hRead
    cases hRead

/-- Every actual ordinary local store lies in its issuing thread's aligned, allocated stack. -/
theorem localWriteStack {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {a : Acc} {data : List Byte} (hw : X.Writes i a data)
    (hLocal : a.loc.space = .local) :
    StackAccess l m i.1 a ∧ a.loc.addr % a.size = 0 := by
  obtain ⟨site, hs, he⟩ := localWriteSite hX hw hLocal
  exact indexedEvent hp hX he hs rfl (.inr ⟨data, rfl⟩)

/-- Separate thread owners keep their stack accesses disjoint at any numerical address. -/
theorem StackAccess.apart {l : Launch} {m : Mem0} {g h : Nat} {a b : Acc}
    (ha : StackAccess l m g a) (hb : StackAccess l m h b) (hOwner : g ≠ h) :
    ¬ a.Overlap b :=
  local_access_apart_of_owner (by simpa only [ha.2.1, hb.2.1] using hOwner)

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
