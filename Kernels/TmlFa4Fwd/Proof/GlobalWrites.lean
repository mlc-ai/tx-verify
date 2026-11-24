-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.NoCancellation
public import Lemmas.Flow.AccessLocal
public import Lemmas.Flow.NotRmw
public import Lemmas.Flow.NotTensor
public import Lemmas.Order.Order
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.LocalStoreSpace
public import Lemmas.Flow.Fire
public import Lemmas.Protocol.Region

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow

noncomputable section

/-- The two scalar global stores are the stage-wise LSE outputs. -/
def lseStoreSites : List Nat := [9073, 9082]

/-- The four boxes of each of the two output stages are the only tensor stores. -/
def outputStoreSites : List Nat := [2963, 2965, 2967, 2969, 2976, 2977, 2978, 2979]

private def localStoreOp : Op → Bool
  | .mem ma =>
    ma.space == some .local && ma.kind == .store &&
      match ma.addr.base with
      | .reg .. => true
      | _ => false
  | _ => false

private def globalStoreOp (op : Op) : Bool :=
  storeSpace op == some .global || (writeOp op && dynamicAccess op && !localStoreOp op)

private theorem localStoreShape {op : Op} (h : localStoreOp op = true) :
    ∃ ma base width, op = .mem ma ∧ ma.space = some .local ∧ ma.kind = .store ∧
      ma.addr.base = .reg base width := by
  cases op <;> simp only [localStoreOp, Bool.false_eq_true] at h
  rename_i ma
  cases hb : ma.addr.base <;> simp [hb] at h
  exact ⟨_, _, _, rfl, h.1, h.2, hb⟩

private def ordinaryCopyOp : Op → Bool
  | .cpAsync _ _ _ _ width _ _ => width == 16
  | _ => false

private theorem globalStoreCode :
    OpPcsFast Decoded.kernel.code globalStoreOp lseStoreSites = true := by
  decide +kernel

private theorem outputStoreCode :
    OpPcsFast Decoded.kernel.code tensorStoreOp outputStoreSites = true := by
  decide +kernel

private theorem noAtomCode :
    Decoded.kernel.code.all (fun i => !atomicOp i.op) = true := by
  decide +kernel

private theorem ordinaryCopyCode :
    Decoded.kernel.code.all (fun i => !bulkOp i.op || ordinaryCopyOp i.op) = true := by
  decide +kernel

private theorem cpAsyncSourceSize_le {l : Launch} {g width n : Nat} {t : TState}
    {source : CpAsyncSource} (h : cpAsyncSourceSize l g t width source = .ok n) : n ≤ width := by
  cases source with
  | full => cases h; exact Nat.le_refl _
  | ignore p =>
    unfold cpAsyncSourceSize at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · cases h
      split <;> omega
  | size op =>
    unfold cpAsyncSourceSize at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
        omega
      · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A whole ordinary async copy has its regular LSU source and no embedded data. -/
structure OrdinaryCopyShape (s : AsyncCopy.Spec) (width : Nat) : Prop where
  srcGlobal : s.src.loc.space = .global
  dstShared : s.dst.loc.space = .shared
  whole : s.writes = .whole
  completion : s.completion = .asyncGroup
  noData : s.data = none
  widthEq : s.dst.size = width
  srcSize : s.src.size ≤ s.dst.size

/-- The model's ordinary asynchronous copy is a whole write to shared memory. -/
private theorem cpAsyncShape {l : Launch} {g pc dst src size : Nat}
    {t : TState} {dstOff srcOff : Int} {source : CpAsyncSource} {policy : Option Opnd}
    {s : AsyncCopy.Spec} {o : Option TState}
    (h : Fires pc (cpAsyncTmpl l g t (.cpAsync dst dstOff src srcOff size source policy))
      ⟨pc, .copy s⟩ o) :
    OrdinaryCopyShape s size ∧ s.dst.loc.cta = g / l.block := by
  unfold cpAsyncTmpl at h
  cases hD : effAddr l g t .shared dst dstOff with
  | error f => simp [hD, bind, Except.bind, ofExec, Fires] at h
  | ok d =>
    cases hS : effAddr l g t .global src srcOff with
    | error f => simp [hD, hS, bind, Except.bind, ofExec, Fires] at h
    | ok a =>
      by_cases hA : 0 < size ∧ d.addr % size = 0 ∧ a.addr % size = 0
      · cases hN : cpAsyncSourceSize l g t size source with
        | error f => simp [hD, hS, hA, hN, bind, Except.bind, ofExec, Fires] at h
        | ok n =>
          cases hP : bulkPolicy l g t policy with
          | error f => simp [hD, hS, hA, hN, hP, bind, Except.bind, ofExec, Fires] at h
          | ok _ =>
            simp [hD, hS, hA, hN, hP, bind, Except.bind, ofExec, Fires, pure, Except.pure] at h
            obtain ⟨rfl, _⟩ := h
            refine ⟨?_, (effAddr_shared hD).2⟩
            exact ⟨effAddr_space hS, effAddr_space hD, rfl, rfl, rfl, rfl, cpAsyncSourceSize_le hN⟩
      · simp [hD, hS, hA, bind, Except.bind, ofExec, Fires, throw, throwThe,
          MonadExceptOf.throw] at h

variable {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}

/-- Every ordinary async copy writes one 16-byte KV vector into its CTA. -/
theorem actualCopyFrame (hX : Consistent l Decoded.kernel A m X) {i : EvId} {s : AsyncCopy.Spec}
    (hCopy : X.Copy i s) : OrdinaryCopyShape s 16 ∧ s.dst.loc.cta = i.1 / l.block := by
  obtain ⟨pc, hEvent⟩ := hCopy
  rcases get_source hX hEvent with ⟨_, hf⟩ | ⟨t, ins, o, _, hc, hf⟩
  · cases hf
  have hIsCopy := fires_bulk_op hf rfl
  have ha := List.all_eq_true.mp ordinaryCopyCode ins (List.mem_of_getElem? hc)
  have hOrd : ordinaryCopyOp ins.op = true := by simpa only [hIsCopy, Bool.not_true,
    Bool.false_or] using ha
  cases ho : ins.op <;> simp only [ho, ordinaryCopyOp, Bool.false_eq_true] at hOrd
  rename_i dst doff src soff size source policy
  rw [ho] at hf
  simpa only [beq_iff_eq.mp hOrd] using cpAsyncShape hf

/-- Every ordinary async copy writes a whole 16-byte vector. -/
theorem actualCopyShape (hX : Consistent l Decoded.kernel A m X) {i : EvId} {s : AsyncCopy.Spec}
    (hCopy : X.Copy i s) : OrdinaryCopyShape s 16 :=
  (actualCopyFrame hX hCopy).1

private def multicastInputOp : Op → Bool
  | .cpTensor _ _ _ _ _ _ _ _ (some _) _ _ => true
  | _ => false

private theorem noMulticastInputCode :
    Decoded.kernel.code.all (fun i => !multicastInputOp i.op) = true := by
  decide +kernel

private theorem unicastRoute {A : List Assumption} {l : Launch}
    {g pc dst mb addr : Nat} {t : TState} {ca group : Bool} {off mbarOff : Int}
    {map : Opnd} {coord : List Opnd} {mode : TensorMode} {policy : Option Opnd}
    {sp : TensorCopy.Spec} {o : Option TState}
    (hf : Fires pc (eventTmpl A l g t
        (.cpTensor ca group dst off map coord mb mbarOff none mode policy))
      ⟨pc, .tensorIssue addr sp⟩ o) : TensorCopy.RoutingOk l (g / l.block) sp := by
  change Fires pc (tensorTmpl l g t
    (.cpTensor ca group dst off map coord mb mbarOff none mode policy)) _ _ at hf
  simp only [tensorTmpl, ofExec, bind, Except.bind, pure, Except.pure] at hf
  rcases hp : cachePolicyRead l g t policy with fault | success
  · simp [hp, Fires] at hf
  rcases hc : tensorLoadCopy l g t ca group dst off map coord mb mbarOff mode with fault | ⟨a, s⟩
  · simp [hp, hc, Fires] at hf
  by_cases hr : TensorRoute l (g / l.block) s.clusterAddress s.group s.sharedBase s.mbar
  · simp [hp, hc, hr, Fires] at hf
    obtain ⟨⟨_, hSpec⟩, _⟩ := hf
    rw [hSpec]
    exact hr
  · simp [hp, hc, hr, Fires, throw, throwThe, MonadExceptOf.throw] at hf

/-- Every tensor load is unicast and satisfies the checked route of its actual issue. -/
theorem actualTensorRoute {A : List Assumption} {l : Launch} {m : Mem0}
    {X : Execution} (hX : Consistent l Decoded.kernel A m X)
    {i : EvId} {addr : Nat} {s : TensorCopy.Spec} (hTensor : X.TensorIssue i addr s) :
    TensorCopy.RoutingOk l (i.1 / l.block) s := by
  obtain ⟨pc, he⟩ := hTensor
  rcases get_source hX he with ⟨_, hu⟩ | ⟨_, ins, _, _, hCode, hf⟩
  · cases hu
  have hClass : tensorOp ins.op = true := by
    cases h : tensorOp ins.op
    · exact (fires_notTensor (eventTmpl_notTensor h) hf addr s rfl).elim
    · rfl
  have hn := List.all_eq_true.mp noMulticastInputCode ins (List.mem_of_getElem? hCode)
  cases hOp : ins.op <;> simp only [hOp, tensorOp, Bool.false_eq_true] at hClass
  rename_i ca group dst off map coord mb moff mask mode policy
  cases mask with
  | none => rw [hOp] at hf; exact unicastRoute hf
  | some mask => simp [hOp, multicastInputOp] at hn

/-- Every issued tensor store is one of the output stage's eight decoded sites. -/
theorem tensorStoreSite (hX : Consistent l Decoded.kernel A m X) {i : EvId} {pc addr : Nat}
    {s : TensorStore.Spec} (he : X.get i = some ⟨pc, .tensorStore addr s⟩)
    : pc ∈ outputStoreSites := by
  rcases get_source hX he with ⟨_, hf⟩ | ⟨_, _, _, _, hc, hf⟩
  · cases hf
  exact OpPcsFast.mem outputStoreCode hc (fires_tensorStore_op hf rfl)

/-- Every global write footprint, including an uncompleted tensor store, is issued
by an LSE store or by a checked output tensor-store site. -/
theorem globalWriteIntentSources (hX : Consistent l Decoded.kernel A m X) {w : AsyncCopy.Ref}
    {a : Acc} (hWrite : X.Intent w a true) (hGlobal : a.loc.space = .global) :
    (∃ i pc bs, w = .thread i ∧ pc ∈ lseStoreSites ∧ X.get i = some ⟨pc, .wr a bs⟩) ∨
    (∃ i x y k pc addr spec, w = .async i (.write (.store x y k)) ∧
      pc ∈ outputStoreSites ∧ X.get i = some ⟨pc, .tensorStore addr spec⟩ ∧
      TensorStore.writeLoc spec x y k = some a.loc ∧ a.size = 1) := by
  rcases w with e | ⟨i, part⟩
  · rcases hWrite with ⟨_, _, hBad⟩ | ⟨bs, ⟨pc, he⟩, _⟩ | ⟨old, new, pc, he⟩
    · cases hBad
    · rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hc, hf⟩
      · cases hf
      have hOp : globalStoreOp ins.op = true := by
        rcases fires_write_space hf rfl with hs | hd
        · simp [globalStoreOp, hs, hGlobal]
        · cases hLocal : localStoreOp ins.op
          · simp [globalStoreOp, fires_write_op hf rfl, hd, hLocal]
          · obtain ⟨ma, base, width, hMa, hs, hk, hb⟩ := localStoreShape hLocal
            rw [hMa] at hf
            have hSpace := (fires_localStore hs hk hb hf).1
            exact Space.noConfusion (hSpace.symm.trans hGlobal)
      exact .inl ⟨e, pc, bs, rfl, OpPcsFast.mem globalStoreCode hc hOp, he⟩
    · exact False.elim (no_kind_of_code hX atomicOp (fun k => ∃ a old new, k = .rmw a old new)
        (fun _ ⟨_, _, _, hf⟩ => by cases hf)
        (fun hf ⟨_, _, _, hk⟩ => fires_rmw_op hf hk) noAtomCode he ⟨_, _, _, rfl⟩)
  · obtain ⟨hw, hfp⟩ := hWrite
    cases part <;> try cases hw
    case async.writeStore.refl x y k =>
      obtain ⟨s, addr, ⟨pc, he⟩, hLoc, hSize⟩ := hfp
      exact .inr ⟨i, x, y, k, pc, addr, s, rfl, tensorStoreSite hX he, he, hLoc, hSize⟩
    case async.writeLoad.refl x y k =>
      obtain ⟨s, addr, hIssue, hLoc, _⟩ := hfp
      have hs := (actualTensorRoute hX hIssue).2.1
      simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at hLoc
      obtain ⟨_, _, hLoc⟩ := hLoc
      rw [← hLoc] at hGlobal
      simp only [TensorBox.sharedLoc, hs] at hGlobal
      cases hGlobal
    case async.writeCta.refl c =>
      obtain ⟨s, targets, hi, _, _⟩ := hfp
      exact (noClcIssue hX hi).elim
    case async.writeCopy.refl =>
      obtain ⟨s, hCopy, _, rfl⟩ := hfp
      exact False.elim (Space.noConfusion ((actualCopyShape hX hCopy).dstShared.symm.trans hGlobal))
    case async.writePrefetch.refl => exact False.elim hfp
    case async.writeElem.refl j =>
      obtain ⟨s, hCopy, hElem⟩ := hfp
      simp [AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets, (actualCopyShape hX hCopy).whole]
        at hElem

private theorem localDynamicStores :
    Decoded.kernel.code.all (fun i => !writeOp i.op || !dynamicAccess i.op || localStoreOp i.op) =
      true := by
  decide +kernel

private theorem noDirectLocalStores :
    Decoded.kernel.code.all (fun i => storeSpace i.op != some .local) = true := by
  decide +kernel

/-- The frozen kernel never performs an atomic read-modify-write. -/
theorem noActualRmw (hX : Consistent l Decoded.kernel A m X) {i : EvId} {a : Acc}
    {old : List (Option Byte)} {new : Option (List Byte)} (he : X.Rmw i a old new) : False := by
  obtain ⟨_, he⟩ := he
  exact no_kind_of_code hX atomicOp (fun k => ∃ a old new, k = .rmw a old new)
    (fun _ ⟨_, _, _, hf⟩ => by cases hf) (fun hf ⟨_, _, _, hk⟩ => fires_rmw_op hf hk)
    noAtomCode he ⟨_, _, _, rfl⟩

/-- Ordinary shared writes originate at an instruction with a statically decoded shared
destination and address the issuing CTA. -/
theorem sharedWriteInstruction (hX : Consistent l Decoded.kernel A m X) {i : EvId} {a : Acc}
    {bs : List Byte} (he : X.Writes i a bs) (hShared : a.loc.space = .shared) :
    ∃ pc ins, X.get i = some ⟨pc, .wr a bs⟩ ∧ Decoded.kernel.code[pc]? = some ins ∧
      storeSpace ins.op = some .shared ∧ a.loc.cta = i.1 / l.block := by
  obtain ⟨pc, he⟩ := he
  rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hf
  rcases fires_write_loc hf rfl with ⟨hSpace, hOwner⟩ | hd
  · exact ⟨pc, ins, he, hc, hShared ▸ hSpace, hOwner hShared⟩
  · have hChecked := List.all_eq_true.mp localDynamicStores ins (List.mem_of_getElem? hc)
    have hop : localStoreOp ins.op = true := by
      simpa only [fires_write_op hf rfl, hd, Bool.not_true, Bool.false_or] using hChecked
    obtain ⟨ma, base, width, hMa, hSpace, hKind, hBase⟩ := localStoreShape hop
    rw [hMa] at hf
    rw [(fires_localStore hSpace hKind hBase hf).1] at hShared
    cases hShared

/-- Ordinary shared stores address the issuing CTA. The only dynamic stores are local. -/
theorem sharedWriteOwned (hX : Consistent l Decoded.kernel A m X) {i : EvId} {a : Acc}
    {bs : List Byte} (he : X.Writes i a bs) (hShared : a.loc.space = .shared) :
    a.loc.cta = i.1 / l.block := by
  obtain ⟨_, _, _, _, _, hOwner⟩ := sharedWriteInstruction hX he hShared
  exact hOwner

/-- All dynamic stores address the loader stack, and no static store addresses constant memory. -/
theorem noConstantWrite (hX : Consistent l Decoded.kernel A m X) {i : EvId} {a : Acc}
    {bytes : List Byte} (hWrite : X.Writes i a bytes) : a.loc.space ≠ .const := by
  intro hConst
  obtain ⟨_, he⟩ := hWrite
  rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hf
  rcases fires_write_loc hf rfl with ⟨hSpace, _⟩ | hDynamic
  · have hClosed : Decoded.kernel.code.all (fun j => storeSpace j.op != some .const) = true := by
      decide +kernel
    have hNo := List.all_eq_true.mp hClosed ins (List.mem_of_getElem? hc)
    simp [hSpace, hConst] at hNo
  · have hChecked := List.all_eq_true.mp localDynamicStores ins (List.mem_of_getElem? hc)
    obtain ⟨ma, base, width, hOp, hs, hk, hb⟩ := localStoreShape (by
      simpa only [fires_write_op hf rfl, hDynamic, Bool.not_true, Bool.false_or] using hChecked)
    rw [hOp] at hf
    rw [(fires_localStore hs hk hb hf).1] at hConst
    cases hConst

/-- Every write covering a local byte is a normal store by the thread that owns that byte.
The decoded kernel's asynchronous operations have shared or global destinations. -/
theorem localWriteOwner (hX : Consistent l Decoded.kernel A m X) {w : AsyncCopy.Ref} {a : Acc}
    {bs : List Byte} (hWrite : X.MemWrites w a bs) {loc : Loc} (hLocal : loc.space = .local)
    (hCover : a.Covers loc) :
    ∃ j, w = .thread (loc.cta, j) ∧ X.Access (loc.cta, j) a true := by
  have hsLoc : a.loc.space = .local := hCover.1.symm.trans hLocal
  have hIntent := hWrite.intent
  rcases w with e | ⟨i, part⟩
  · rcases hIntent with ⟨_, _, hBad⟩ | ⟨data, ⟨pc, he⟩, _⟩ | ⟨old, new, pc, he⟩
    · cases hBad
    · rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hc, hf⟩
      · cases hf
      have hm := List.mem_of_getElem? hc
      rcases fires_write_space hf rfl with hs | hd
      · have hm' := List.all_eq_true.mp noDirectLocalStores ins hm
        simp [hs, hsLoc] at hm'
      · have hm' := List.all_eq_true.mp localDynamicStores ins hm
        have hOp : localStoreOp ins.op = true := by
          simpa only [fires_write_op hf rfl, hd, Bool.not_true, Bool.false_or] using hm'
        obtain ⟨ma, base, width, hMa, hs, hk, hb⟩ := localStoreShape hOp
        rw [hMa] at hf
        have hOwn := (fires_localStore hs hk hb hf).2
        have hEq : e.1 = loc.cta := hOwn.symm.trans hCover.2.1.symm
        have he' : X.get (loc.cta, e.2) = some ⟨pc, .wr a data⟩ := by
          rw [← hEq]
          exact he
        refine ⟨e.2, ?_, .inr (.inl ⟨data, ⟨pc, he'⟩, rfl⟩)⟩
        obtain ⟨g, j⟩ := e
        change g = loc.cta at hEq
        rw [hEq]
    · exact False.elim (no_kind_of_code hX atomicOp (fun k => ∃ a old new, k = .rmw a old new)
        (fun _ ⟨_, _, _, hf⟩ => by cases hf)
        (fun hf ⟨_, _, _, hk⟩ => fires_rmw_op hf hk) noAtomCode he ⟨_, _, _, rfl⟩)
  · obtain ⟨hw, hfp⟩ := hIntent
    cases part <;> try cases hw
    case async.writeStore.refl x y k =>
      obtain ⟨s, addr, _, hLoc, _⟩ := hfp
      exact False.elim (Space.noConfusion ((Execution.store_writeLoc_global hLoc).symm.trans hsLoc))
    case async.writeLoad.refl x y k =>
      obtain ⟨s, addr, hIssue, hLoc, _⟩ := hfp
      have hs := (actualTensorRoute hX hIssue).2.1
      simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at hLoc
      obtain ⟨_, _, hLoc⟩ := hLoc
      rw [← hLoc] at hsLoc
      simp only [TensorBox.sharedLoc, hs] at hsLoc
      cases hsLoc
    case async.writeCta.refl c =>
      obtain ⟨s, targets, hi, _, _⟩ := hfp
      exact (noClcIssue hX hi).elim
    case async.writeCopy.refl =>
      obtain ⟨s, hCopy, _, rfl⟩ := hfp
      exact False.elim (Space.noConfusion ((actualCopyShape hX hCopy).dstShared.symm.trans hsLoc))
    case async.writePrefetch.refl => exact False.elim hfp
    case async.writeElem.refl j =>
      obtain ⟨s, hCopy, hElem⟩ := hfp
      simp [AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets, (actualCopyShape hX hCopy).whole]
        at hElem

/-- A recorded global write keeps the same issue classification and its actual bytes. -/
theorem globalWriteSources (hX : Consistent l Decoded.kernel A m X) {w : AsyncCopy.Ref} {a : Acc}
    {bs : List Byte} (hWrite : X.MemWrites w a bs) (hGlobal : a.loc.space = .global) :
    (∃ i pc, w = .thread i ∧ pc ∈ lseStoreSites ∧ X.get i = some ⟨pc, .wr a bs⟩) ∨
    (∃ i x y k pc addr spec, w = .async i (.write (.store x y k)) ∧
      pc ∈ outputStoreSites ∧ X.get i = some ⟨pc, .tensorStore addr spec⟩ ∧
      TensorStore.writeLoc spec x y k = some a.loc ∧ a.size = 1) := by
  rcases globalWriteIntentSources hX hWrite.intent hGlobal with ⟨i, pc, written, rfl, hSite, he⟩ | h
  · rcases hWrite with ⟨pc', h'⟩ | ⟨_, pc', h'⟩
    · rw [he] at h'
      have heq := Option.some.inj h'
      cases heq
      exact .inl ⟨i, pc, rfl, hSite, he⟩
    · rw [he] at h'
      cases h'
  · exact .inr h

end
end PTX.Kernels.TmlFa4Fwd
