-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.TmemAccess
public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.ShFrame
public import Core.Memory.CommitOperandOrder
import Kernels.TmlFa4Fwd.Proof.Correction.Export.FstPoll
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.CopyOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Done
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Issue
import Lemmas.Protocol.PairTmaRing.Order
import Lemmas.Order.Order
import Lemmas.Order.OrderWaits
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The final O stores against the MMA operands and each other

A final O store of a correction lane follows the lane's poll of the stage's final O barrier, which
observes the completion of every MMA of the CTA (`mma_observed`); so the store is after every
operand read of its byte (`mma_fst`, the reuse of a completed operand). Two final stores of one byte
are of one lane (`fst_fst`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h k i : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The final O poll before a final store** observes every MMA of the CTA. -/
theorem fst_observes (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    {pc : Nat} {a : Acc} {bs : List Byte} (he : X.get (h, i) = some ⟨pc, .wr a bs⟩)
    (hs : a.loc.space = .shared) : ∃ j < i, ∀ e : EvId, Tmem1.IsMma X e →
      e.1 / L.block = h / L.block → po X (h, j) (h, i) ∧
        ∃ ws, AsyncObserved X e .mmaDone (h, j) true ws ∧ ScopesMeet L .cluster e.1 ws h := by
  obtain ⟨st, -, hk, -⟩ := corr_fst hp hX hFw hw hw1 he hs
  obtain ⟨j, hji, pcj, hj⟩ := corr_o_poll hp hX hFw hw hw1 st hk.ge
  refine ⟨j, hji, fun e hm hc => ⟨po_of_source_not_access rfl hji
    (List.getElem?_eq_some_iff.mp (show (X.tr h)[i]? = _ from he)).1 (by simp [hj, Event.acc]),
    .cta, ?_, ?_⟩⟩
  · have ho : obj L h (144 + 8 * st.val) = obj L e.1 (144 + 8 * st.val) := (obj_cta hc _).symm
    rw [ho] at hj
    exact mma_observed hp hX hFw hm hj
  · obtain ⟨_, _, _, _, hi⟩ := hm
    obtain ⟨pce, hie⟩ := hi
    exact ScopesMeet.of_sameCta ⟨Frame.lt_of_get hX (k := e.2) hie, Frame.lt_of_get hX he, hc⟩

/-- **An operand read of a byte is before every final store of it.** -/
theorem mma_fst (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    {pc : Nat} {a : Acc} {bs : List Byte} (he : X.get (h, i) = some ⟨pc, .wr a bs⟩) {l : Loc}
    (hl : l.space = .shared) (hc : a.Covers l) {isB : Bool} {idx : Nat}
    (hm : Tmem1.IsMma X (g, k)) (hcta : g / L.block = h / L.block)
    (hr : AsyncCovers X (g, k) (.mmaRead isB idx) l) :
    modelCausality L X l (.async (g, k) (.mmaRead isB idx)) (.thread (h, i)) := by
  obtain ⟨j, hji, hall⟩ := fst_observes hp hX hFw hw hw1 he (hc.1.symm.trans hl)
  obtain ⟨hpo, ws, hob, hsc⟩ := hall (g, k) hm hcta
  exact ⟨hr, (h, j), .inr ⟨ws, hob, hsc⟩, .inr ⟨hl, .inr ⟨rfl, hji, hm⟩, .single (.inl hpo), a, bs,
    ⟨pc, he⟩, hc⟩⟩

/-- **A write that precedes an operand read of a byte is before every final store of it** (the
observed operand handoff). -/
theorem through_mma (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    {pc : Nat} {a : Acc} {bs : List Byte} (he : X.get (h, i) = some ⟨pc, .wr a bs⟩) {l : Loc}
    (hl : l.space = .shared) (hc : a.Covers l) {isB : Bool} {idx : Nat} {d : Nat}
    {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hm : X.MmaIssue (g, k) d sp acc mask)
    (hbl : sp.byteLoc (if isB then .b else .a) idx = some l) (hidx : idx < 4096)
    (hcta : g / L.block = h / L.block) {src : Ref} (hsrc : ∃ b, X.Intent src b true ∧ b.Covers l)
    (hp' : ByteCausality L X l src (.async (g, k) (.mmaRead isB idx))) :
    ByteCausality L X l src (.thread (h, i)) := by
  obtain ⟨j, hji, hall⟩ := fst_observes hp hX hFw hw hw1 he (hc.1.symm.trans hl)
  obtain ⟨hpo, ws, hob, hsc⟩ := hall (g, k) ⟨_, _, _, _, hm⟩ hcta
  have hspec : ∃ c', Tm.Spec128 sp c' := by
    obtain ⟨-, st, u, jj, -, h | h⟩ := Tm.mma_qkpv hp hX hFw ⟨_, _, _, _, hm⟩
    · obtain ⟨-, -, -, rfl⟩ := h.spec_eq hm
      exact ⟨_, .inl rfl, rfl, rfl⟩
    · obtain ⟨-, -, -, rfl⟩ := h.spec_eq hm
      exact ⟨_, .inr rfl, rfl, rfl⟩
  obtain ⟨c', hc'⟩ := hspec
  obtain ⟨l', b, ⟨hfp, ops, h1, h2⟩⟩ := PairTmaRing.mmaRead_present hX hob hm hbl
    (lt_of_lt_of_eq hidx (Tm.opBytes hc' _).symm)
  exact .commitOperand hl hsrc (.inl ⟨_, _, _, _, hm⟩) ⟨b, .inl ⟨_, _, _, _, hm, hbl⟩, ops, h1, h2⟩
    hp' ⟨ws, hob, hsc⟩ hpo ⟨a, .inl ⟨true, .inr (.inl ⟨bs, ⟨pc, he⟩, rfl⟩)⟩, hc⟩

/-- **Two final stores of one byte** are of one lane, in program order. -/
theorem fst_fst {h' i' pc pc' : Nat} {a a' : Acc} {bs bs' : List Byte}
    (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    (hw' : 8 ≤ Prologue.warpIndex L h') (hw1' : Prologue.warpIndex L h' ≤ 11)
    (he : X.get (h, i) = some ⟨pc, .wr a bs⟩) (he' : X.get (h', i') = some ⟨pc', .wr a' bs'⟩)
    {l : Loc} (hl : l.space = .shared) (hc : a.Covers l) (hc' : a'.Covers l)
    (hne : (h, i) ≠ (h', i')) :
    baseCausality L X (h, i) (h', i') ∨ baseCausality L X (h', i') (h, i) := by
  obtain ⟨st, ⟨hz, q, hq, w, hw4, hloc⟩, -⟩ := corr_fst hp hX hFw hw hw1 he (hc.1.symm.trans hl)
  obtain ⟨st', ⟨hz', q', hq', w', hw4', hloc'⟩, -⟩ :=
    corr_fst hp hX hFw hw' hw1' he' (hc'.1.symm.trans hl)
  have hb := hp.block
  have hhh : h = h' := by
    have hst := st.isLt
    have hst' := st'.isLt
    obtain ⟨-, c2, c3, c4⟩ := hc
    obtain ⟨-, d2, d3, d4⟩ := hc'
    rw [hz] at c4
    rw [hz'] at d4
    rw [hloc] at c2 c3 c4
    rw [hloc'] at d2 d3 d4
    simp only [Correction.rowN, hb] at c2 c3 c4 d2 d3 d4
    simp only [Prologue.warpIndex, hb] at hw hw1 hw' hw1'
    omega
  subst hhh
  have hil : i < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  have hil' : i' < (X.tr h).length := (List.getElem?_eq_some_iff.mp he').1
  have hac : (X.get (h, i)).bind Event.acc = some a := by rw [he]; rfl
  have hac' : (X.get (h, i')).bind Event.acc = some a' := by rw [he']; rfl
  rcases Nat.lt_trichotomy i i' with hlt | rfl | hlt
  · exact .inl (.single (.inl ⟨rfl, hlt, hil',
      fun hs => hs.not_overlap rfl hlt hac hac' ⟨l, hc, hc'⟩⟩))
  · exact (hne rfl).elim
  · exact .inr (.single (.inl ⟨rfl, hlt, hil,
      fun hs => hs.not_overlap rfl hlt hac' hac ⟨l, hc', hc⟩⟩))

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
