-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.CopyOrder
public import Kernels.TmlFa4Fwd.Proof.Protocol.Staging.Final
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Fence
import Kernels.TmlFa4Fwd.Proof.Correction.Export.FstPoll
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.MemStore
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Ordered
import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Done
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Observed
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Ordered
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Stores
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Lifetime
import Kernels.TmlFa4Fwd.Proof.Protocol.Staging.KvFinal
import Kernels.TmlFa4Fwd.Proof.Protocol.Staging.QFinal
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Issue
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.StoreWarp
import Lemmas.Async.AsyncChain
import Lemmas.Order.OrderWaits
import Lemmas.Protocol.PairTmaRing.Order
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The staging writes before the tensor stores' reads

A tensor store follows the output lane's poll of the ready barrier of the stage it reads, which
observes the arrival of every correction lane of the CTA. So a final store of the stage, with the
lane's proxy fence after it, is before the store's reads (`fst_store`); and an operand read that a
correction lane's final O poll observes is before them (`mma_store`), so the Q and K/V copies are
(`q_copy_store`, `kv_copy_store`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h k i : Nat}

theorem readyLoc_eq (L : Launch) (g : Nat) (st : Fin 2) :
    Epilogue.readyLoc L g st = obj L g (208 + 8 * st.val) := rfl

theorem store_covers {e : EvId} {addr : Nat} {s : TensorStore.Spec}
    (hi : X.TensorStoreIssue e addr s) {x y z : Nat} {l : Loc}
    (hl : TensorStore.readLoc s x y z = some l) : AsyncCovers X e (.read (.store x y z)) l :=
  ⟨{ loc := l, size := 1 }, false, ⟨rfl, s, addr, hi, hl, rfl⟩, ⟨rfl, rfl, le_rfl, by simp⟩⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **A tensor store's ready poll**: for every correction lane of the CTA, its ready arrival, and
the lane's events up to it precede the store. -/
theorem store_after {o kt addr : Nat} {s : TensorStore.Spec}
    (hi : X.TensorStoreIssue (o, kt) addr s) : ∃ st : Fin 2,
      (∀ x y z l, TensorStore.readLoc s x y z = some l → l.space = .shared ∧ l.cta = o / L.block ∧
        L.sharedBase + 3072 + 65536 * st.val ≤ l.addr ∧
        l.addr < L.sharedBase + 3072 + 65536 * st.val + 65536) ∧
      ∀ y, y / L.block = o / L.block → 8 ≤ Prologue.warpIndex L y → Prologue.warpIndex L y ≤ 11 →
        (∃ ka pc tx c rel sc, X.get (y, ka) =
          some ⟨pc, .arrive (obj L y (208 + 8 * st.val)) tx c rel sc⟩) ∧
        ∀ e, arrivals (obj L y (208 + 8 * st.val)) ((X.tr y).take e) = 0 →
          baseCausality L X (y, e) (o, kt) := by
  obtain ⟨st, bx, ⟨j, hj, he⟩, hb⟩ := store_read_ready hp hX (store_warp hp hX hFw hi) hi
  obtain ⟨pct, het⟩ := hi
  have hol := Frame.lt_of_get hX het
  have hoIn : o < L.threads ∧ o / L.block = o / L.block := ⟨hol, rfl⟩
  have hktl : kt < (X.tr o).length := (List.getElem?_eq_some_iff.mp het).1
  have hq : okPolls (Epilogue.readyLoc L o st) ((X.tr o).take j) = 0 + 0 := by
    obtain ⟨-, -, ⟨_, _, _, h0⟩ | ⟨hk, -⟩⟩ := ready_use' (g := o) (st := st) hp hX hFw he rfl
      (fun _ h => by cases h)
    · exact h0
    · cases hk
  refine ⟨st, fun x y z l hl => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hb x y z l hl
    have := bx.isLt
    exact ⟨h1, h2, by omega, by omega⟩
  intro y hc hw hw1
  obtain ⟨a, ha⟩ := corrLane_of hp (c := o / L.block) hc ⟨hw, hw1⟩
  have hloc : Epilogue.readyLoc L o st = obj L y (208 + 8 * st.val) := by
    rw [readyLoc_eq, obj_cta hc]
  constructor
  · obtain ⟨i, -, hs⟩ := readyHandoff hp hX hFw o st o j _ 0 true .cta 0 hoIn he hq y ⟨a, ha⟩
    obtain ⟨rs, ⟨tx, cnt, pca, hka⟩, -⟩ := hs
    rw [hloc] at hka
    exact ⟨i, pca, tx, cnt, true, rs, hka⟩
  · intro e hz
    exact (readyHandoff hp hX hFw o st).hb hoIn he hq ⟨a, ha⟩ (e := e)
      (by rw [hloc]; exact hz.le) hj hktl

/-- **A final store is before the tensor stores' reads of its bytes.** -/
theorem fst_store (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    {pc : Nat} {a : Acc} {bs : List Byte} (he : X.get (h, i) = some ⟨pc, .wr a bs⟩) {l : Loc}
    (hc : a.Covers l) {o kt addr : Nat} {s : TensorStore.Spec}
    (hi : X.TensorStoreIssue (o, kt) addr s) {x y z : Nat}
    (hr : TensorStore.readLoc s x y z = some l) :
    modelCausality L X l (.thread (h, i)) (.async (o, kt) (.read (.store x y z))) := by
  obtain ⟨st, hbox, hall⟩ := store_after hp hX hFw hi
  obtain ⟨hl, hcta, h1, h2⟩ := hbox x y z l hr
  obtain ⟨stf, ⟨hz, q, hq, w, hw4, hloc⟩, -, harr⟩ :=
    corr_fst hp hX hFw hw hw1 he (hc.1.symm.trans hl)
  have hch : h / L.block = o / L.block := by rw [← hcta, hc.2.1, hloc]
  have hstf : stf = st := by
    obtain ⟨-, -, c3, c4⟩ := hc
    rw [hz] at c4
    rw [hloc] at c3 c4
    simp only at c3 c4
    have hrow : Correction.rowN L h < 128 := Nat.mod_lt _ (by decide)
    have h3 := st.isLt
    have h4 := stf.isLt
    exact Fin.ext (by omega)
  subst hstf
  obtain ⟨⟨ka, pca, tx, c, rel, sc, hka⟩, hbase⟩ := hall h hch hw hw1
  obtain ⟨kf, hkf, ⟨pcf, hf⟩, hbef⟩ := corr_fst_fence hp hX hFw hw hw1 stf hka
  have hik := hbef he harr
  have hkz := corr_ready_arr hp hX hFw hw hw1 stf hka
  have hfz : arrivals (obj L h (208 + 8 * stf.val)) ((X.tr h).take kf) = 0 := by
    have : arrivals (obj L h (208 + 8 * stf.val)) ((X.tr h).take kf) ≤
        arrivals (obj L h (208 + 8 * stf.val)) ((X.tr h).take ka) :=
      (List.take_sublist_take_left hkf.le).countP_le
    omega
  obtain ⟨pct, het⟩ := id hi
  have hhl := Frame.lt_of_get hX he
  have hfl : kf < (X.tr h).length := (List.getElem?_eq_some_iff.mp hf).1
  refine ⟨store_covers hi hr, .inl ⟨(h, kf), some (.shared .cta), none, ⟨pcf, hf⟩, hhl,
    ⟨hl, hcta.trans hch.symm⟩, ⟨hhl, Frame.lt_of_get hX het, by simp only [hch]⟩, ?_,
    hbase kf hfz⟩⟩
  refine .single (.inl ⟨rfl, hik, hfl, fun hsa => ?_⟩)
  have := hsa.1
  rw [hf] at this
  simp [Event.acc] at this

/-- **The final O poll of a correction lane before a tensor store**, with the commit it observes. -/
theorem store_o_poll {o kt addr : Nat} {s : TensorStore.Spec}
    (hi : X.TensorStoreIssue (o, kt) addr s) : ∃ y j, ∃ st : Fin 2, ∃ z c pcz, ∃ sc : TcCommit.Spec,
      y < L.threads ∧ y / L.block = o / L.block ∧
      (∃ pc, X.get (y, j) = some ⟨pc, .wait (obj L y (144 + 8 * st.val)) 0 true true .cta⟩) ∧
      baseCausality L X (y, j) (o, kt) ∧ z / L.block = o / L.block ∧ Prologue.warpIndex L z = 12 ∧
      X.get (z, c) = some ⟨pcz, .tc (.commit sc)⟩ ∧
      sc.mbar = Tm.bar L (z / L.block) (144 + 8 * st.val) := by
  obtain ⟨st, -, hall⟩ := store_after hp hX hFw hi
  obtain ⟨hcy, hwy⟩ := corrLane_facts (L := L) hp (o / L.block) ⟨0, by decide⟩
  set y := corrLane L (o / L.block) ⟨0, by decide⟩ with hy
  have hw8 : Prologue.warpIndex L y = 8 := by rw [hwy]; rfl
  obtain ⟨⟨ka, pca, tx, c, rel, sc, hka⟩, hbase⟩ := hall y hcy (by omega) (by omega)
  have hO := corr_ready_o hp hX hFw (by omega) (by omega) st hka
  obtain ⟨j, hj, pcj, hje⟩ := corr_o_poll hp hX hFw (by omega) (by omega) st hO.ge
  have hz : arrivals (obj L y (208 + 8 * st.val)) ((X.tr y).take j) = 0 := by
    have h0 := corr_ready_arr hp hX hFw (by omega) (by omega) st hka
    have : arrivals (obj L y (208 + 8 * st.val)) ((X.tr y).take j) ≤
        arrivals (obj L y (208 + 8 * st.val)) ((X.tr y).take ka) :=
      (List.take_sublist_take_left hj.le).countP_le
    omega
  obtain ⟨z, cc, pcc, s', rank, hc, -, hzc, hz12, hmb, -⟩ := o_handoff hp hX hFw st (g := y) hje
  refine ⟨y, j, st, z, cc, pcc, s', Frame.lt_of_get hX hje, hcy, ⟨pcj, hje⟩, hbase j hz,
    hzc.trans hcy, hz12, hc, ?_⟩
  rw [hmb, ← obj_cta hzc]

/-- **A write before an operand read of a byte is before the tensor stores' reads of it**, for an
operand read of the CTA. -/
theorem through_mma_store {o kt addr : Nat} {s : TensorStore.Spec}
    (hi : X.TensorStoreIssue (o, kt) addr s) {x y z : Nat} {l : Loc}
    (hr : TensorStore.readLoc s x y z = some l) {g' k' d idx : Nat} {sp : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} {isB : Bool} (hm : X.MmaIssue (g', k') d sp acc mask)
    (hbl : sp.byteLoc (if isB then .b else .a) idx = some l) (hidx : idx < 4096)
    (hcta : g' / L.block = o / L.block) {w : EvId} {q : Part}
    (hwl : w.1 < L.threads) (hwc : w.1 / L.block = o / L.block)
    (hW : modelCausality L X l (.async w q) (.async (g', k') (.mmaRead isB idx))) :
    modelCausality L X l (.async w q) (.async (o, kt) (.read (.store x y z))) := by
  obtain ⟨yc, j, st, -, -, -, -, hyl, hyc, ⟨pcj, hje⟩, hbase, -⟩ := store_o_poll hp hX hFw hi
  have hgl : g' < L.threads := by obtain ⟨pc, he⟩ := hm; exact Frame.lt_of_get hX (k := k') he
  have hob : AsyncObserved X (g', k') .mmaDone (yc, j) true .cta := by
    have ho : obj L yc (144 + 8 * st.val) = obj L g' (144 + 8 * st.val) :=
      obj_cta (hyc.trans hcta.symm) _
    rw [ho] at hje
    exact mma_observed hp hX hFw (i := (g', k')) ⟨_, _, _, _, hm⟩ hje
  have hspec : ∃ c', Tm.Spec128 sp c' := by
    obtain ⟨-, st, u, jj, -, h | h⟩ := Tm.mma_qkpv hp hX hFw ⟨_, _, _, _, hm⟩
    · obtain ⟨-, -, -, rfl⟩ := h.spec_eq hm
      exact ⟨_, .inl rfl, rfl, rfl⟩
    · obtain ⟨-, -, -, rfl⟩ := h.spec_eq hm
      exact ⟨_, .inr rfl, rfl, rfl⟩
  obtain ⟨c', hc'⟩ := hspec
  have hpres := PairTmaRing.mmaRead_present hX hob hm hbl
    (lt_of_lt_of_eq hidx (Tm.opBytes hc' _).symm)
  obtain ⟨pct, het⟩ := id hi
  refine ⟨.inl ⟨hwl, Frame.lt_of_get hX het, hwc⟩, hW.2.trans hpres (.direct ⟨mma_covers hm hbl,
    store_covers hi hr, .inl ⟨(yc, j), .inr ⟨.cta, hob, ?_⟩, hbase⟩⟩)⟩
  exact ScopesMeet.of_sameCta ⟨hgl, hyl, hcta.trans hyc.symm⟩

/-- **A copy into a Q stage is before the tensor stores' reads of its bytes.** -/
theorem q_copy_store {e : EvId} {pce al : Nat} {sc : TensorCopy.Spec}
    (hce : X.get e = some ⟨pce, .tensorIssue al sc⟩) {x' y' z' : Nat} {l : Loc}
    (hwl : TensorCopy.writeLoc sc x' y' z' = some l) (h1 : L.sharedBase + 3072 ≤ l.addr)
    (h2 : l.addr < L.sharedBase + 68608) {o kt addr : Nat} {s : TensorStore.Spec}
    (hi : X.TensorStoreIssue (o, kt) addr s) {x y z : Nat}
    (hr : TensorStore.readLoc s x y z = some l) (hec : e.1 / L.block = o / L.block) :
    modelCausality L X l (.async e (.write (.load x' y' z')))
      (.async (o, kt) (.read (.store x y z))) := by
  obtain ⟨st0, hbox, -⟩ := store_after hp hX hFw hi
  obtain ⟨hl, hcta, -, -⟩ := hbox x y z l hr
  obtain ⟨_, _, sto, zz, c, pcz, scc, -, -, -, -, hzc, hz12, hcz, hmb⟩ := store_o_poll hp hX hFw hi
  obtain ⟨st, hst, off, ho, hadd⟩ : ∃ st < 2, ∃ off < 32768,
      l.addr = L.sharedBase + 3072 + 32768 * st + off :=
    ⟨(l.addr - L.sharedBase - 3072) / 32768, by omega,
      (l.addr - L.sharedBase - 3072) % 32768, Nat.mod_lt _ (by decide), by omega⟩
  have hleq : l = ⟨.shared, o / L.block, L.sharedBase + 3072 + 32768 * st + off⟩ := by
    obtain ⟨s1, c1, a1⟩ := l
    simp only at hl hcta hadd
    subst hl hcta hadd
    rfl
  obtain ⟨k', u, idx, j, d, sp, acc, mask, hq, hm, hidx, hbl⟩ :=
    q_read_before hp hX hFw (h := o) hzc hz12 hcz hmb hst ho hleq
  have hcr : AsyncCovers X (zz, k') (.mmaRead false idx) l := mma_covers hm hbl
  have hW := q_copy_read hp hX hFw hce hwl hq hst hcr (hcta.trans hzc.symm) (by omega) (by omega)
  exact through_mma_store hp hX hFw hi hr hm (isB := false) hbl hidx hzc
    (Frame.lt_of_get hX (k := e.2) hce) hec hW

/-- **A row copy is before the tensor stores' reads of its bytes.** -/
theorem kv_copy_store {y' jc pcc : Nat} {sp : AsyncCopy.Spec}
    (hcp : X.get (y', jc) = some ⟨pcc, .copy sp⟩) {l : Loc} (hcl : sp.dst.Covers l)
    (hca : AsyncCovers X (y', jc) (.write .copy) l) {o kt addr : Nat} {s : TensorStore.Spec}
    (hi : X.TensorStoreIssue (o, kt) addr s) {x y z : Nat}
    (hr : TensorStore.readLoc s x y z = some l) (hec : y' / L.block = o / L.block) :
    modelCausality L X l (.async (y', jc) (.write .copy))
      (.async (o, kt) (.read (.store x y z))) := by
  obtain ⟨_, _, sto, zz, c, pcz, scc, -, -, -, -, hzc, hz12, hcz, hmb⟩ := store_o_poll hp hX hFw hi
  obtain ⟨hy, hC⟩ := copy_row hp hX hFw (i := (y', jc)) ⟨_, hcp⟩
  simp only at hy hC
  obtain ⟨k', idx, d, sp1, acc, mask, hR, hmma, hidx, hbl⟩ :=
    kv_read_before hp hX hFw hcp hcl (hzc.trans hec.symm) hz12 hcz hmb
  have hcr : AsyncCovers X (zz, k') (.mmaRead true idx) l := mma_covers hmma hbl
  have hW := kv_copy_read hp hX hFw hcp hy hC hR (hec.trans hzc.symm) rfl le_rfl hca hcr
  exact through_mma_store hp hX hFw hi hr hmma (isB := true) hbl hidx hzc
    (Frame.lt_of_get hX hcp) hec hW

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
