-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
public import Kernels.TmlFa4Fwd.Assumptions
public import Lemmas.Kernel.Progress.Async
public import Lemmas.Protocol.UnitHandoff
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Count
import Kernels.TmlFa4Fwd.Proof.Correction.Export.FinalStores
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.MemStore
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.StoreReady
import Kernels.TmlFa4Fwd.Proof.Lib.StoreForm
import Kernels.TmlFa4Fwd.Proof.Protocol.Operands
import Kernels.TmlFa4Fwd.Proof.Protocol.Free.Obj
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.StoreWarp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output stores' bytes have visible sources (`storeSources`)

A tensor store of stage `st` follows a poll of the stage's ready barrier, which synchronizes with
the arrival of each of the CTA's 128 correction lanes (`readyHandoff`). The lane of the byte's row
stored the byte's word and fenced before its arrival. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.MbarRing

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The ready hand-off.** -/
theorem readyHandoff (g : Nat) (st : Fin 2) :
    UnitHandoff L X (Epilogue.readyLoc L g st)
      (fun y => ∃ a, y = corrLane L (g / L.block) a)
      (fun h => h < L.threads ∧ h / L.block = g / L.block) 0 := by
  refine (readyObj hp hX hFw g st).handoff hX (fun h _ x hx j hj => ?_)
    (fun {h j pc par acq sc} hh he => ?_) (fun {a h i j pc pc' par acq sc sc'} hh ha he => ?_)
  · exfalso
    obtain ⟨-, ⟨pc, sc, hget⟩, harr⟩ := (readyObj hp hX hFw g st).S_rec hx
    obtain ⟨-, hc, ⟨_, hk, -⟩ | ⟨-, hw8, hw11⟩⟩ :=
      ready_use' hp hX hFw (h := corrLane L (g / L.block) x.1) hget rfl (fun _ h => by cases h)
    · cases hk
    have hloc : Epilogue.readyLoc L g st =
        obj L (corrLane L (g / L.block) x.1) (208 + 8 * st.val) := by
      rw [obj_cta hc]; rfl
    rw [hloc] at hget harr
    have h0 := corr_ready_arr hp hX hFw hw8 hw11 st hget
    have h1 := harr.symm.trans h0
    omega
  · obtain ⟨-, -, ⟨_, hk, -⟩ | ⟨hk, -⟩⟩ := ready_use' hp hX hFw he rfl (fun _ h => by cases h)
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨-, -, -, ho, -⟩ := hk
      exact ho
    · cases hk
  · obtain ⟨hya, hcy, ⟨_, hk, -⟩ | ⟨hk, -⟩⟩ := ready_use' hp hX hFw ha rfl (fun _ h => by cases h)
    · cases hk
    obtain ⟨-, -, ⟨_, hk', -⟩ | ⟨hk', -⟩⟩ := ready_use' hp hX hFw he rfl (fun _ h => by cases h)
    swap; · cases hk'
    simp only [Kind.arrive.injEq] at hk
    simp only [Kind.wait.injEq] at hk'
    obtain ⟨-, -, -, -, rfl⟩ := hk
    obtain ⟨-, -, -, -, rfl⟩ := hk'
    exact ⟨⟨hya, hh.1, hcy.trans hh.2.symm⟩, hh.1, hya, hh.2.trans hcy.symm⟩

/-- **The output stores' bytes have visible sources.** -/
theorem storeSources : Sched.StoreSources L X := by
  intro i addr s hi
  obtain ⟨hv, -, hred⟩ := actualTensorStoreForm hX hi
  refine ⟨hv, hred, fun slot loc hd => ⟨?_, fun w a bs hw hc _ => wbyte_of_write hp hX hFw hw hc⟩⟩
  obtain ⟨st, bx, ⟨j, hj, hwe⟩, hbox⟩ := store_read_ready hp hX (store_warp hp hX hFw hi) hi
  have hslot : TensorTransfer.slotAt s.descriptor slot.1.val slot.2.1.val slot.2.2.val =
      some slot := by
    unfold TensorTransfer.slotAt
    rw [dite_eq_left slot.1.isLt, dite_eq_left slot.2.1.isLt, dite_eq_left slot.2.2.isLt]
  have hread : TensorStore.readLoc s slot.1.val slot.2.1.val slot.2.2.val =
      some (s.sharedLoc slot) := by
    unfold TensorStore.readLoc
    rw [hslot, Option.map_some]
  obtain ⟨hsp, hcta, hlo, hhi⟩ := hbox _ _ _ _ hread
  obtain ⟨g, k⟩ := i
  obtain ⟨pcs, hse⟩ := id hi
  have hg := Frame.lt_of_get hX hse
  simp only at hwe hj hcta
  generalize hl : s.sharedLoc slot = l at hsp hcta hlo hhi hread ⊢
  have hb := hp.block
  have hbx := bx.isLt
  have hst := st.isLt
  -- the byte's lane
  set off := l.addr - (L.sharedBase + 3072 + 65536 * st.val + 16384 * bx.val) with hoff
  have ho : off < 16384 := by omega
  have hrow : off / 128 < 128 := by omega
  obtain ⟨y, hy⟩ : ∃ y, y = corrLane L (g / L.block) ⟨off / 128, hrow⟩ := ⟨_, rfl⟩
  have hyc : y / L.block = g / L.block := by rw [hy]; simp only [corrLane, hb]; omega
  have hyr : Correction.rowN L y = off / 128 := by
    rw [hy]; simp only [Correction.rowN, corrLane, hb]; omega
  have hyw : 8 ≤ Prologue.warpIndex L y ∧ Prologue.warpIndex L y ≤ 11 := by
    rw [hy]
    simp only [Prologue.warpIndex, corrLane, hb]
    omega
  -- its arrival, its fence and its store
  have hpoll0 : okPolls (Epilogue.readyLoc L g st) ((X.tr g).take j) = 0 + 0 := by
    obtain ⟨-, -, ⟨_, hk, -, h0⟩ | ⟨hk, -⟩⟩ := ready_use' hp hX hFw hwe rfl (fun _ h => by cases h)
    · exact h0
    · cases hk
  have hH := readyHandoff hp hX hFw g st
  obtain ⟨ia, hia, hsy⟩ := hH g j _ _ _ _ 0 ⟨hg, rfl⟩ hwe hpoll0 y ⟨_, hy⟩
  obtain ⟨ev, hev, harr⟩ := hsy.arrives
  obtain ⟨pca, kda⟩ := ev
  cases kda <;> simp [arrivesOn, sourceArrive] at harr
  subst harr
  have hloc : Epilogue.readyLoc L g st = obj L y (208 + 8 * st.val) := by
    rw [obj_cta hyc]; rfl
  rw [hloc] at hev
  obtain ⟨f, js, pcf, pcj, a, bs, hjf, hfi, hfe, hwr, hz, hal⟩ :=
    corr_fst_before hp hX hFw hyw.1 hyw.2 hev (q := bx.val) (t := off % 128 / 4) hbx (by omega)
  have hcov : a.Covers l := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hal]; exact hsp
    · rw [hal]; exact hcta.trans hyc.symm
    · rw [hal, hyr]; simp only; omega
    · rw [hal, hz, hyr]; simp only; omega
  have hmw : X.MemWrites (.thread (y, js)) a bs := .inl ⟨pcj, hwr⟩
  refine ⟨_, a, bs, hmw, hcov, .direct ⟨?_, .inl ?_⟩⟩
  · refine ⟨{ loc := l, size := 1 }, false, ⟨rfl, s, addr, hi, ?_, rfl⟩, ?_⟩
    · exact hread
    · exact ⟨rfl, rfl, le_refl _, Nat.lt_succ_self _⟩
  · have hyl : y < L.threads := Frame.lt_of_get hX hwr
    have hfl : f < (X.tr y).length := by have := len_of_get hfe; simpa using this
    have hkl : k < (X.tr g).length := by have := len_of_get hse; simpa using this
    refine ⟨(y, f), some (.shared .cta), none, ⟨pcf, hfe⟩, hyl, ⟨hsp, hcta.trans hyc.symm⟩,
      ⟨hyl, hg, by rw [hyc]⟩, .single (.inl ⟨rfl, hjf, hfl, fun hsa => ?_⟩), ?_⟩
    · have h1 := hsa.2 (f - js) le_rfl
      rw [show js + (f - js) = f by omega, hfe, hwr] at h1
      simp [Event.acc] at h1
    · refine hH.hb ⟨hg, rfl⟩ hwe hpoll0 ⟨_, hy⟩ ?_ hj hkl
      rw [← hia]
      exact countP_take_mono _ (X.tr y) hfi.le

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
