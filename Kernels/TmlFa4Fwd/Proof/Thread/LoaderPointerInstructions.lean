-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPointerHistory
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Flow.Code.Part008
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Kernels.TmlFa4Fwd.Flow.Code.Part015
import Kernels.TmlFa4Fwd.Flow.Code.Part019
import Kernels.TmlFa4Fwd.Flow.Code.Part022
import Kernels.TmlFa4Fwd.Flow.Code.Part025

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader.LocalAccessCode
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader (RingShape loaderRingWrites)

noncomputable section

/-- The packet save writes exactly the array entry named by the current loop index. -/
theorem pointerSaveStep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (i : Fin 6) {g : Nat} {s u : TState} {ev : Option Event}
    (hPc : s.pc = (pointerPacket i).store) (hShape : RingShape s)
    (hAddress : addressInvariant l s) (slot : Fin 2)
    (hIndex : s.regs (pointerPacket i).save.loop.reg = some (b64 slot.val))
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    ∃ data, ev = some ((pointerPacket i).write l g slot data) ∧ u.pc = s.pc + 1 := by
  let b := pointerPacket i
  have hArray : b.save.array.val < 2 := (packetBounds i).2.2.2.2.2.1
  have hWide : b.save.loop.wide = true := (packetBounds i).2.2.2.2.2.2.1
  have hSite : b.save ∈ scalarSites := (packetBounds i).2.2.2.2.2.2.2
  obtain ⟨_, _, ins, ma, hCode, hOp, hSpace, hBase, hOff, hSem, hVec, hWidth, hVector, _⟩ :=
    scalarLocation hSite
  have hStoreCode : ∃ a, kernel.code[b.store]? = some ⟨none, .mem a⟩ ∧
      a.kind = .store ∧ a.rule = some .threadAccess ∧ a.srcs.length = 1 ∧
      (Op.mem a).isLocal = false := by
    fin_cases i
    · exact ⟨_, Flow.code_534, rfl, rfl, rfl, rfl⟩
    · exact ⟨_, Flow.code_799, rfl, rfl, rfl, rfl⟩
    · exact ⟨_, Flow.code_977, rfl, rfl, rfl, rfl⟩
    · exact ⟨_, Flow.code_1223, rfl, rfl, rfl, rfl⟩
    · exact ⟨_, Flow.code_1447, rfl, rfl, rfl, rfl⟩
    · exact ⟨_, Flow.code_1628, rfl, rfl, rfl, rfl⟩
  obtain ⟨mem, hm, hStore, hRule, hSrc, hNonlocal⟩ := hStoreCode
  obtain rfl := Option.some.inj (hCode.symm.trans hm)
  have hMem : mem = ma := Op.mem.inj hOp
  subst mem
  have hCode' : kernel.code[s.pc]? = some ⟨none, .mem ma⟩ := by rw [hPc]; exact hm
  have hSub : s.sub = 0 := by
    by_contra! h
    have h1 : s.sub = 1 := by have := hShape.1.1; omega
    obtain ⟨op, hOpCode, hIsVector, _⟩ := hShape.1.2 h1
    rw [hCode'] at hOpCode
    rw [congrArg Instr.op (Option.some.inj hOpCode), hIsVector] at hVector
    cases hVector
  have hLive : b.save.active .address s.pc := hPc.symm ▸ packetStoreActive i
  obtain ⟨entry, hEntry, hAddr⟩ := hAddress b.save hSite .address hLive
  have hEntryEq : entry = slot := by
    change s.regs b.save.loop.reg = some (b64 slot.val) at hIndex
    have hEntry' : s.regs b.save.loop.reg = some (b64 entry.val) := by
      simpa only [TwoEntryLoop.value, hWide, ↓reduceIte] using hEntry
    have hEq := (Value.bits.inj (Option.some.inj (hEntry'.symm.trans hIndex))).2
    apply Fin.ext
    have ha : entry.val < 2 ^ 64 := by have := entry.isLt; omega
    have hb : slot.val < 2 ^ 64 := by have := slot.isLt; omega
    simpa only [toNat_ofNat_lt ha, toNat_ofNat_lt hb] using congrArg BitVec.toNat hEq
  subst entry
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · have hb := packetBounds i
    dsimp only at hb
    have hHead : (pointerPacket i).head = (pointerPacket i).first + 2 := rfl
    have hBack : (pointerPacket i).back = (pointerPacket i).store + 3 := rfl
    have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← Loader.loaderOutCore (by omega) (by omega)]
    exact (tau_core_not_event hCode' hNonlocal ht').elim
  · obtain ⟨ins', hC, _, hf⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hCode'.symm.trans hC)
    have hFires : Fires s.pc (accessTmpl Assumptions.all l g s ma) e (some u) := by
      have hDirect : ma.locSpace? = none := by simp [MemAccess.locSpace?, hSpace]
      simpa [eventTmpl, memTmpl, hRule, hDirect] using hf
    rcases accessTmpl_store (A := Assumptions.all) (L := l) (g := g) (t := s) hStore with
      ⟨fault, hTmp⟩ | ⟨access, data, _, hTmp⟩
    · rw [hTmp] at hFires
      cases hFires.2
    rw [hTmp] at hFires
    obtain ⟨rfl, hAfter⟩ := hFires
    obtain rfl := Option.some.inj hAfter.symm
    have ha := fires_localStoreAccess hSpace hStore hBase hf
    have hAcc := scalarFootprint hp slot hAddr hSub hSpace hBase hOff hSem hVec hWidth ha
    have hCell : access = b.cell l g slot := by
      simpa only [PointerPacket.cell, ScalarSite.word, hArray, ite_true] using hAcc
    exact ⟨data, by simp [PointerPacket.write, hPc, hCell, b], by simp [afterStore, hSrc]⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader.LocalAccessCode
