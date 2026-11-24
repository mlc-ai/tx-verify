-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.MbarRingRound
public import Lemmas.Async.AsyncExecution
public import Lemmas.Order.Order
public import Lemmas.Protocol.ObjectSource

@[expose] public section

/-! # A poll observes a bulk copy's completion, and a later read sees its bytes

A proof tool for a protocol whose consumer waits on the mbarrier a bulk copy completes on, read
from the object's own history. A successful poll whose observed phase is the phase in which the
copy's complete-tx is recorded observes the copy's completion (`Consistent.copy_observed_of_phase`;
the complete-tx record names an issued, notified copy on that object: `Consistent.copy_record`).
A read that the observing poll happens before, of a byte the copy writes and no other write
covers, returns the copy's byte (`Consistent.read_copy_byte`): the copy's write is visible to the
read there, so it is the read's source. -/

namespace PTX

open AsyncCopy MBarrier

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- A complete-tx record of copy `i` in the history of `m` names an issued copy completed on `m`
whose notification occurred. -/
theorem Consistent.copy_record (hX : Consistent L K A mem0 X) {m : Loc} {d : Record Ref}
    (hd : d ∈ X.objects m) {i : EvId} (hid : d.id = .async i (.notify .copy)) :
    ∃ s, issuedBy X i = some s ∧ (X.async.copies i).notified = true ∧
      s.completion = .mbarrier m ∧ d.action = .completeTx s.dst.size := by
  cases record_source hX.tma.2.2.1 hd with
  | bulk hid' he hc hn ha =>
    rw [hid] at hid'
    cases hid'
    exact ⟨_, by simp [issuedBy, he], hn, hc, ha⟩
  | init hid' _ _ | inval hid' _ _ | arrive hid' _ _ | wait hid' _ _ | increment hid' _ _
  | tensor hid' _ _ _ | arriveOn hid' _ _ _ _ | commit hid' _ _ _ | clc hid' _ _ _ _ =>
    rw [hid] at hid'; cases hid'

/-- **A poll that observes the phase of a copy's complete-tx observes the copy's completion.** -/
theorem Consistent.copy_observed_of_phase (hX : Consistent L K A mem0 X) {m : Loc}
    (hni : NoInval (X.objects m)) {i k : EvId} {n j q : Nat} {d w : Record Ref}
    (hd : (X.objects m)[n]? = some d) (hdid : d.id = .async i (.notify .copy))
    (hdf : d.fault = none) (hw : (X.objects m)[j]? = some w) (hwk : w.id = .thread k)
    (hwf : w.fault = none) (hwait : w.reply.waited = some true)
    (hp : phaseAt (X.objects m) n = some q) (ho : observedAt (X.objects m) j = some q)
    {pc parity : Nat} {acq : Bool} {ws : MbarScope}
    (hget : X.get k = some ⟨pc, .wait m parity true acq ws⟩) :
    AsyncObserved X i (.notify .copy) k acq ws := by
  obtain ⟨s, hs, hn, hm, -⟩ := hX.copy_record (List.mem_of_getElem? hd) hdid
  have hu := MbarRing.Slot.updateBeforeWait_of_phase (X.objects_checked hX m) hni hd hdf hw hwf
    hwait hp ho
  rw [hdid, hwk] at hu
  exact ⟨_, m, ⟨rfl, s.dst.size, s, hs, hn, hm, rfl⟩, ⟨pc, parity, hget⟩, hu⟩

/-- **A read after a poll that observed a copy's completion returns the copy's byte** at a byte
the copy's write covers and no other write covers. -/
theorem Consistent.read_copy_byte (hX : Consistent L K A mem0 X) {i w e : EvId}
    {ws : MbarScope} (ho : AsyncObserved X i (.notify .copy) w true ws)
    (hs : ScopesMeet L .cluster i.1 ws w.1) (hhb : baseCausality L X w e)
    {a : Acc} {bs : List (Option Byte)} (hr : X.Reads e a bs) {k : Nat} (hk : k < a.size)
    {dst : Acc} {raw : List Byte} (hwrite : X.MemWrites (.async i (.write .copy)) dst raw)
    (hcov : dst.Covers (a.loc.at k))
    (huniq : ∀ w' a' bs', X.MemWrites w' a' bs' → a'.Covers (a.loc.at k) →
      w' = .async i (.write .copy)) :
    bs[k]? = some (wbyte dst raw (a.loc.at k)) := by
  obtain ⟨s, hc, hwh, hd, -⟩ := id hwrite
  have hr' : X.MemReads (.thread e) a bs := .inl hr
  have ho' : AsyncObserved X i (.write .copy) w true ws := by
    obtain ⟨n, m, hn, hwo⟩ := ho
    exact ⟨n, m, .inl hn, hwo⟩
  have hv : modelCausality L X (a.loc.at k) (.async i (.write .copy)) (.thread e) :=
    ⟨⟨_, true, ⟨rfl, s, hc, hwh, hd⟩, hcov⟩, w, .inr ⟨ws, ho', hs⟩, .inl hhb⟩
  have hidden := hX.hidden (.thread e) _ bs k (.async i (.write .copy)) _ raw hr' hk hwrite hcov
    (.direct hv)
  have hs := (hX.rf (.thread e) _ _ hr').2 k hk
  cases hrf : X.rf (.thread e) k with
  | none => simp [hrf] at hidden
  | some writer =>
    rw [hrf] at hs
    obtain ⟨a', written, hw', hwcov, hval⟩ := hs
    obtain rfl := huniq _ _ _ hw' hwcov
    obtain ⟨s', hc', -, hd', hb'⟩ := hw'
    obtain ⟨-, -, -, -, hb⟩ := hwrite
    cases Execution.Copy.unique hc hc'
    rw [hb] at hb'
    cases hb'
    rw [← hd', hd] at hval
    exact hval

end

end PTX
