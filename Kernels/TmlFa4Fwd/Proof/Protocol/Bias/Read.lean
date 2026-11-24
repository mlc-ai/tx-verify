-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Order
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.BiasSrc
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Bytes
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StageRead
import Lemmas.Order.OrderBaseCausality
import Lemmas.Order.OrderWaits
import Lemmas.Protocol.CountNth
import Lemmas.Protocol.PollIndex
import Lemmas.Tensor.BoxWrite
import Lemmas.Tensor.TensorCompleteConsistentRead
import Lemmas.Tensor.TensorTransfer
import Std.Tactic.BVDecide.Normalize.Prop

import Kernels.TmlFa4Fwd.Proof.Common.DataState

@[expose] public section

/-! # The bias reads see their round's copy

A softmax lane's bias read of round `u` reads a byte of box `q` of its stage's window, which the
copy `2 u + q` of the stage's lane wrote: the lane's poll `u` observed it. Every other write of the
byte is a copy `2 u' + q`: for `u' < u` the lane's poll `u'` observed it, before the loader issued
the round's copy; for `u' > u` the lane's proxy fence and stage barrier put the read before it
(`biasReadHandoff`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.MbarRing

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- Two copies of one thread with the same count of earlier ones on a barrier are one. -/
private theorem copy_unique {y i i' pc pc' a a' : Nat} {s s' : TensorCopy.Spec} {b : Loc}
    (he : X.get (y, i) = some ⟨pc, .tensorIssue a s⟩) (hs : s.mbar = b)
    (he' : X.get (y, i') = some ⟨pc', .tensorIssue a' s'⟩) (hs' : s'.mbar = b)
    (hc : ((X.tr y).take i).countP (issuesTo b) = ((X.tr y).take i').countP (issuesTo b)) :
    i = i' := by
  have h1 := nthEv_eq (p := issuesTo b) he (by simp [issuesTo, hs])
  have h2 := nthEv_eq (p := issuesTo b) he' (by simp [issuesTo, hs'])
  rw [← h1, ← h2, hc]

/-- The box byte at an address of the box, with the element's byte the address's parity. -/
theorem input_box_byte {c : Nat} {j : Fin 14} {org : Fin 3 → Int} {mb l : Loc}
    (hsp : l.space = .shared) (hc : l.cta = c)
    (hlo : L.sharedBase + (Loader.inputSite j).sharedOffset ≤ l.addr)
    (hhi : l.addr < L.sharedBase + (Loader.inputSite j).sharedOffset + 16384) :
    ∃ x y, TensorCopy.writeLoc (inputSpec p L c j org mb) x y
      ((l.addr - (L.sharedBase + (Loader.inputSite j).sharedOffset)) % 2) = some l ∧
      x = TensorSwizzle.offset .b128 (L.sharedBase + (Loader.inputSite j).sharedOffset)
        (l.addr - (L.sharedBase + (Loader.inputSite j).sharedOffset)) % 128 / 2 ∧
      y = TensorSwizzle.offset .b128 (L.sharedBase + (Loader.inputSite j).sharedOffset)
        (l.addr - (L.sharedBase + (Loader.inputSite j).sharedOffset)) / 128 := by
  obtain ⟨m1, m2, m3, m4, -⟩ := input_map p j
  have hf2 : (Loader.inputMap p (Loader.inputSite j)).format.bytes = 2 := by rw [m3]; rfl
  set B := L.sharedBase + (Loader.inputSite j).sharedOffset with hB
  set v := l.addr - B with hv
  set o := TensorSwizzle.offset .b128 B v with ho
  have hr := TensorSwizzle.offset_row .b128 B v
  have hb := TensorSwizzle.offset_byte .b128 B v
  have hinv := TensorSwizzle.offset_involutive .b128 B v
  refine ⟨o % 128 / 2, o / 128, ?_, rfl, rfl⟩
  have hx : o % 128 / 2 < TensorTile.count (inputSpec p L c j org mb).descriptor.box 0 := by
    rw [show TensorTile.count (inputSpec p L c j org mb).descriptor.box 0 = 64 from m1]; omega
  have hy : o / 128 < TensorTile.rows (inputSpec p L c j org mb).descriptor.box := by
    rw [show TensorTile.rows (inputSpec p L c j org mb).descriptor.box = 128 from m2]; omega
  have hk : v % 2 < (inputSpec p L c j org mb).descriptor.format.bytes := by
    rw [show (inputSpec p L c j org mb).descriptor.format.bytes = 2 from hf2]; omega
  unfold TensorCopy.writeLoc TensorTransfer.slotAt
  rw [dite_eq_left hx, dite_eq_left hy, dite_eq_left hk, Option.map_some]
  congr 1
  simp only [TensorBox.sharedLoc, TensorTile.sharedByte, TensorTile.linearByte,
    TensorTile.rowBytes]
  rw [show TensorTile.count (inputSpec p L c j org mb).descriptor.box 0 = 64 from m1,
    show (inputSpec p L c j org mb).descriptor.format.bytes = 2 from hf2,
    show (inputSpec p L c j org mb).descriptor.swizzle = .b128 from m4]
  obtain ⟨sp, ct, ad⟩ := l
  simp only at hsp hc hlo hhi hv
  subst hsp hc
  simp only [TensorTile.swizzleWidth, inputSpec, Loc.mk.injEq, true_and]
  rw [show o / 128 * max (64 * 2) 128 + o % 128 / 2 * 2 + v % 2 = o by
    have : max (64 * 2) 128 = 128 := by decide
    rw [this]
    omega]
  have : TensorSwizzle.offset .b128 (L.sharedBase + (Loader.inputSite j).sharedOffset) o = v :=
    hinv
  rw [this]
  omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hIn : InputsUnwritten p X) (hBW : BiasWrites L X)
include hp hX hFw hIn hBW

/-- **One byte of a bias read**: its element `(x, y)` and the copy that wrote it. -/
theorem bias_byte {h k : Nat} {st q : Fin 2} (hh : SoftIn L h st.val h)
    (hpolls : okPolls (bF L h st) ((X.tr h).take k) = barOrd X h k (stageId st.val) + 1)
    {pcr : Nat} {ar : Acc} {bsr : List (Option Byte)}
    (hr : X.get (h, k) = some ⟨pcr, .rd ar bsr⟩) {l : Loc}
    (hsp : l.space = .shared) (hcta : l.cta = h / L.block) (hcov : ar.Covers l)
    (hlo : L.sharedBase + (166912 + 32768 * st.val + 16384 * q.val) ≤ l.addr)
    (hhi : l.addr < L.sharedBase + (166912 + 32768 * st.val + 16384 * q.val) + 16384) :
    ∃ j org, (Loader.inputSite j).bias = true ∧
      (Loader.inputSite j).sharedOffset = 166912 + 32768 * st.val + 16384 * q.val ∧
      (∃ i al pci mb, X.get (tmaLane L X h, i) =
          some ⟨pci, .tensorIssue al (inputSpec p L (h / L.block) j org mb)⟩ ∧ mb = bF L h st ∧
        ((X.tr (tmaLane L X h)).take i).countP (issuesTo (bF L h st)) =
          2 * barOrd X h k (stageId st.val) + q.val) ∧
      SmWarp.BiasByteHandoff L X (h, k) l
        ((biasValue (inputVal p true (boxCoord org
          (TensorSwizzle.offset .b128 (L.sharedBase + (Loader.inputSite j).sharedOffset)
            (l.addr - (L.sharedBase + (Loader.inputSite j).sharedOffset)) % 128 / 2)
          (TensorSwizzle.offset .b128 (L.sharedBase + (Loader.inputSite j).sharedOffset)
            (l.addr - (L.sharedBase + (Loader.inputSite j).sharedOffset)) / 128)))).byteAt
          ((l.addr - (L.sharedBase + (Loader.inputSite j).sharedOffset)) % 2)) := by
  have hB := tmaBytes hp hX hFw
  set u := barOrd X h k (stageId st.val) with hu
  have hkl : k < (X.tr h).length := by have := len_of_get hr; simpa using this
  have hhl := hh.1
  have hty := (tmaLane_in (X := X) hp h).1
  -- the poll of a round `u' ≤ u`, and the copy of the box it observes
  have hpoll : ∀ u' ≤ u, ∃ jw i al pci sp, jw < k ∧
      X.get (tmaLane L X h, i) = some ⟨pci, .tensorIssue al sp⟩ ∧ sp.mbar = bF L h st ∧
      ((X.tr (tmaLane L X h)).take i).countP (issuesTo (bF L h st)) = 2 * u' + q.val ∧
      u' + 1 ≤ okPolls (bE L h st) ((X.tr (tmaLane L X h)).take i) ∧
      okPolls (bF L h st) ((X.tr h).take jw) = u' ∧
      (X.get (h, jw)).bind Event.acc = none ∧
      ∃ sc, WaitObserves X (.async (tmaLane L X h, i) (.notify .load)) (h, jw) (bF L h st)
        true sc := by
    intro u' hu'
    obtain ⟨jw, pcw, par, acq, sc, hjk, hw, hwo⟩ := Poll.exists_nth
      (show u' + 1 ≤ okPolls (bF L h st) ((X.tr h).take k) by omega)
    have hacq : acq = true := by
      obtain ⟨-, hu2⟩ := bias_use hp hX hFw st hw rfl (fun _ h => by cases h)
      rcases hu2 with ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, _, _, hk, _⟩
      · simp only [Kind.wait.injEq] at hk
        obtain ⟨-, -, -, hacq, -⟩ := hk
        exact hacq
      · cases hk
      · cases hk
    subst hacq
    obtain ⟨i, pci, al, sp, h1, h2, h3, h4, h5⟩ := bias_observes hp hX hFw hB hh hw hwo q
    exact ⟨jw, i, al, pci, sp, hjk, h1, h2, h3, h4, hwo, by simp [hw, Event.acc], sc, h5⟩
  -- a notified copy's write of the byte is finished for its poll
  have hfin : ∀ {i jw sc al pci sp x y kk}, X.get (tmaLane L X h, i) =
      some ⟨pci, .tensorIssue al sp⟩ → sp.mbar = bF L h st →
      WaitObserves X (.async (tmaLane L X h, i) (.notify .load)) (h, jw) (bF L h st) true sc →
      AsyncFinished L X (tmaLane L X h, i) (.write (.load x y kk)) (h, jw) ∧
        ∃ o, X.tensor (tmaLane L X h, i) = some o ∧ o.effects.notified = true ∧ o.spec = sp := by
    intro i jw sc al pci sp x y kk he hm hW
    obtain ⟨-, hU⟩ := id hW
    obtain ⟨ii, jj, r, w, phase, hrec, hid, -⟩ := hU
    have hpres := object_record_present hX.tma (List.mem_of_getElem? hrec)
    rw [hid] at hpres
    obtain ⟨o, ho, hn⟩ := id hpres
    obtain ⟨⟨addr, pco, hio⟩, -⟩ := hX.tensor _ o ho
    have hos : o.spec = sp := by
      rw [he] at hio
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hio
      exact hio.2.2.symm
    refine ⟨.inr ⟨sc, ⟨_, _, ⟨rfl, o, addr, ho, ⟨pco, hio⟩, by rw [hos]; exact hm, hn⟩, hW⟩, ?_⟩,
      o, ho, hn, hos⟩
    exact ScopesMeet.of_sameCta ⟨Frame.lt_of_get hX he, hhl, hty⟩
  have hcovers : ∀ {i al pci sp x y kk}, X.get (tmaLane L X h, i) =
      some ⟨pci, .tensorIssue al sp⟩ → TensorCopy.writeLoc sp x y kk = some l →
      AsyncCovers X (tmaLane L X h, i) (.write (.load x y kk)) l := by
    intro i al pci sp x y kk he hl
    exact ⟨{ loc := l, size := 1 }, true, ⟨rfl, sp, al, ⟨pci, he⟩, hl, rfl⟩,
      ⟨rfl, rfl, le_rfl, by simp⟩⟩
  obtain ⟨jw, i, al, pci, sp, hjk, he, hm, hcnt, hpe, hwo, hna, sc, hW⟩ := hpoll u le_rfl
  obtain ⟨-, o, ho, hn, hos⟩ := hfin (x := 0) (y := 0) (kk := 0) he hm hW
  -- the copy's box is the stage's box `q`
  have hil : i < (X.tr (tmaLane L X h)).length := by have := len_of_get he; simpa using this
  obtain ⟨j, org, hspec, hbi, hoff⟩ : ∃ j org, sp = inputSpec p L (h / L.block) j org sp.mbar ∧
      (Loader.inputSite j).bias = true ∧
      (Loader.inputSite j).sharedOffset = 166912 + 32768 * st.val + 16384 * q.val := by
    obtain ⟨hw, -⟩ := input_box hp hX hFw he
    have hm' : sp.mbar = obj L (tmaLane L X h) (320 + 8 * st.val) := by rw [obj_cta hty]; exact hm
    obtain ⟨-, -, jv, pcv, maskv, instv, -, hjv⟩ := ld_tma_copy hp hX hFw hw (b_tmaOff st) he hm'
    obtain ⟨j', org', hs', hb', ho'⟩ := ld_bias_copy hp hX hFw hw
      (fun k pc mask inst ld hk => tmaLane_won hX hjv hk) st he hm'
    rw [show obj L (tmaLane L X h) (320 + 8 * st.val) = bF L h st by rw [obj_cta hty], hcnt] at ho'
    rw [hty] at hs'
    have hq := q.isLt
    exact ⟨j', org', hs', hb', by omega⟩
  obtain ⟨x, y, hl, hx, hy⟩ :=
    input_box_byte (p := p) (L := L) (org := org) (mb := sp.mbar) (j := j)
    (c := h / L.block) (l := l) hsp hcta (by omega) (by omega)
  rw [← hspec] at hl
  refine ⟨j, org, hbi, hoff, ⟨i, al, pci, sp.mbar, by rw [← hspec]; exact he, hm,
    hcnt⟩, ?_⟩
  rw [← hx, ← hy]
  set kk := (l.addr - (L.sharedBase + (Loader.inputSite j).sharedOffset)) % 2
  have hwr := input_written hp hX hIn ho hn (hos.trans hspec) (by rw [hos]; exact hl)
  rw [hbi] at hwr
  refine ⟨(tmaLane L X h, i), x, y, kk, { loc := l, size := 1 }, _, hwr,
    ⟨rfl, rfl, le_rfl, by simp⟩, by simp [wbyte], ?_, ?_⟩
  · -- the write before the read
    refine ⟨hcovers he hl, (h, jw), (hfin he hm hW).1, .inl ?_⟩
    exact .single (.inl (po_of_source_not_access rfl hjk hkl hna))
  · -- the other writes
    intro w' dst' data' hw' hc'
    obtain ⟨i', x', y', k', rfl⟩ := hBW w' dst' data' l hw' hc' hsp (by omega) (by
      have := st.isLt; have := q.isLt; omega)
    obtain ⟨o', addr', b', ho', ⟨pc', hi'⟩, hl', -, hsz, -⟩ := id hw'
    have hlocs : dst'.loc = l := by
      obtain ⟨⟨sp1, ct1, ad1⟩, n, e1, e2, e3, e4⟩ := dst'
      obtain ⟨sp2, ct2, ad2⟩ := l
      simp only at hsz
      subst hsz
      obtain ⟨d1, d2, d3, d4⟩ := hc'
      simp only at d1 d2 d3 d4
      simp only [Loc.mk.injEq]
      exact ⟨d1.symm, d2.symm, by omega⟩
    rw [hlocs] at hl'
    obtain ⟨hlane, hm', hpar, j', org', hspec', hbi', hoff'⟩ :=
      bias_writer hp hX hFw (g := h) (st := st) (q := q) hi' hl' hcta hlo hhi
    obtain ⟨y0, i'⟩ := i'
    simp only at hlane hpar
    subst hlane
    set N := ((X.tr (tmaLane L X h)).take i').countP (issuesTo (bF L h st)) with hN
    have hil' : i' < (X.tr (tmaLane L X h)).length := by
      have := len_of_get hi'; simpa using this
    have hsc : SameCta L (tmaLane L X h) (tmaLane L X h) :=
      ⟨Frame.lt_of_get hX he, Frame.lt_of_get hX he, rfl⟩
    rcases Nat.lt_trichotomy (N / 2) u with hlt | heq | hgt
    · -- an earlier round's copy
      right; left
      refine ⟨.inl hsc, .direct ⟨hcovers hi' hl', hcovers he hl, .inl ?_⟩⟩
      obtain ⟨jw1, i1, al1, pci1, sp1, hjk1, he1, hm1, hcnt1, hpe1, hwo1, hna1, sc1, hW1⟩ :=
        hpoll (N / 2) hlt.le
      have hii : i1 = i' := copy_unique he1 hm1 hi' hm' (by rw [hcnt1]; omega)
      subst hii
      refine ⟨(h, jw1), (hfin hi' hm' hW1).1, ?_⟩
      obtain ⟨ib, pcb, hib, hord, hcause⟩ := bias_cause hp hX hFw hB hh (j := N / 2) hil (by omega)
      refine hcause jw1 ?_
      have hpb := bias_poll_before hp hX hFw hh hib hord
      by_contra hge
      have := Poll.okPolls_mono (bF L h st) (X.tr h) (show ib ≤ jw1 by omega)
      omega
    · -- the same copy
      left
      have hii : i' = i := copy_unique hi' hm' he hm (by rw [hcnt]; omega)
      subst hii
      rw [he] at hi'
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hi'
      obtain ⟨-, -, hse⟩ := hi'
      rw [← hse] at hl'
      obtain ⟨s1, hs1, hl1⟩ := Option.map_eq_some_iff.mp hl
      obtain ⟨s2, hs2, hl2⟩ := Option.map_eq_some_iff.mp hl'
      have hadd := congrArg Loc.addr (hl1.trans hl2.symm)
      have hslot : s1 = s2 := TensorTransfer.sharedByte_injective _ _ hadd
      obtain ⟨a1, a2, a3⟩ := TensorCopy.slotAt_coordinates hs1
      obtain ⟨b1, b2, b3⟩ := TensorCopy.slotAt_coordinates hs2
      subst hslot
      rw [← a1, ← a2, ← a3, ← b1, ← b2, ← b3]
    · -- a later round's copy
      right; right
      refine ⟨hcovers hi' hl', .inl ?_⟩
      have hb' := (tma_copy hp hX hFw (g := h) (b_tmaOff st) hi' hm').2
      rw [bE_eq] at hb'
      obtain ⟨ib, pcb, hib, hord, hcause⟩ := bias_cause hp hX hFw hB hh (j := u) hil' (by
        change N + 1 ≤ 2 * okPolls (bE L h st) _ at hb'
        omega)
      have hkb : k < ib := by
        by_contra hge
        rcases Nat.lt_or_ge ib k with hlt2 | hge2
        · have h1 : ((X.tr h).take (ib + 1)).countP (Execution.isBarId (stageId st.val)) =
              ((X.tr h).take ib).countP (Execution.isBarId (stageId st.val)) + 1 := by
            rw [List.take_add_one, show (X.tr h)[ib]? = _ from hib, List.countP_append]
            simp [Execution.isBarId]
          have h2 := (List.take_sublist_take_left (l := X.tr h)
            (show ib + 1 ≤ k by omega)).countP_le (p := Execution.isBarId (stageId st.val))
          simp only [barOrd] at hord hu
          omega
        · have : ib = k := by omega
          subst this
          rw [hr] at hib
          cases hib
      obtain ⟨hw8, hws, -⟩ := stage_of_bar hp hX hFw st.isLt hib
      obtain ⟨fi, pcf, hfi, hf⟩ := soft_stage_fence hp hX hFw hw8
        (show stageId st.val = 11 ∨ stageId st.val = 12 by
          have := st.isLt; unfold stageId; omega) hib
      have hkf : k < fi := by
        rcases Nat.lt_or_ge k fi with h1 | h1
        · exact h1
        · have : k = fi := by omega
          subst this
          rw [hr] at hf
          cases hf
      have hfl : fi < (X.tr h).length := by have := len_of_get hf; simpa using this
      have hcl : SameCluster L h (tmaLane L X h) := by
        have := hty
        exact ⟨hhl, Frame.lt_of_get hX he, by rw [hty]⟩
      refine ⟨(h, fi), some (.shared .cta), none, ⟨pcf, hf⟩, hhl, ⟨hsp, hcta⟩, hcl, ?_,
        hcause fi (by omega)⟩
      refine .single (.inl ⟨rfl, hkf, hfl, fun hsa => ?_⟩)
      have := hsa.1
      rw [hf] at this
      simp [Event.acc] at this

end

/-- **The bias read hand-off**, from the launch, when the inputs are not written and the bias window
is written only by the tensor copies. -/
theorem biasReadHandoff (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hIn : InputsUnwritten p X) (hBW : BiasWrites L X) :
    SmWarp.BiasReadHandoff p L X := by
  intro g k d n c e b j a bs he hσ hJ hs hk
  obtain ⟨hgl, hw, hpolls, hsz, hsp, hcta, hal, q, hrow⟩ :=
    soft_bias_read hp hX hFw he (control_of_data hp hσ) hs hk
  obtain ⟨pcr, kd⟩ := e
  simp only at hk
  subst hk
  have hst : Prologue.warpIndex L g / 4 < 2 := by omega
  obtain ⟨st, hstv⟩ : ∃ st : Fin 2, st.val = Prologue.warpIndex L g / 4 := ⟨⟨_, hst⟩, rfl⟩
  have hh : SoftIn L g st.val g := ⟨hgl, rfl, hw, hstv.symm⟩
  have hso : sobj L g 320 = bF L g st := by
    rw [sobj]
    simp only [bF]
    congr 1
    omega
  rw [hso, ← hstv] at hpolls
  rw [← hstv] at hrow
  have hs0 := hp.shared.1
  have hrow' := Nat.mod_lt (g % L.block) (show 0 < 128 by decide)
  have hbyte := fun t : Fin 4 => bias_byte hp hX hFw hIn hBW (q := q) hh hpolls he
    (l := a.loc.at t.val) hsp hcta
    ⟨rfl, rfl, by simp [Loc.at], by simp only [Loc.at]; have := t.isLt; omega⟩
    (by simp only [Loc.at]; have := q.isLt; have := t.isLt; omega)
    (by simp only [Loc.at]; have := q.isLt; have := t.isLt; omega)
  -- the four bytes have one copy, hence one origin
  obtain ⟨j0, org0, hbi0, hoff0, ⟨i0, al0, pci0, mb0, he0, hm0, hc0⟩, -⟩ := hbyte 0
  have hone : ∀ t : Fin 4, SmWarp.BiasByteHandoff L X (g, k) (a.loc.at t.val)
      ((biasValue (inputVal p true (boxCoord org0
        (TensorSwizzle.offset .b128 (L.sharedBase + (Loader.inputSite j0).sharedOffset)
          (a.loc.addr + t.val - (L.sharedBase + (Loader.inputSite j0).sharedOffset)) % 128 / 2)
        (TensorSwizzle.offset .b128 (L.sharedBase + (Loader.inputSite j0).sharedOffset)
          (a.loc.addr + t.val - (L.sharedBase + (Loader.inputSite j0).sharedOffset)) /
          128)))).byteAt
        ((a.loc.addr + t.val - (L.sharedBase + (Loader.inputSite j0).sharedOffset)) % 2)) := by
    intro t
    obtain ⟨j1, org1, hbi1, hoff1, ⟨i1, al1, pci1, mb1, he1, hm1, hc1⟩, hbh⟩ := hbyte t
    have hii : i0 = i1 := copy_unique he0 hm0 he1 hm1 (hc0.trans hc1.symm)
    subst hii
    rw [he0] at he1
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at he1
    obtain ⟨-, -, hse⟩ := he1
    have hor : org0 = org1 := by
      simp only [inputSpec, TensorCopy.Spec.mk.injEq, TensorBox.mk.injEq, heq_eq_eq, true_and]
        at hse
      exact hse.1.2.1
    rw [hoff0.trans hoff1.symm, hor]
    exact hbh
  obtain ⟨B, hB⟩ : ∃ B, B = L.sharedBase + (Loader.inputSite j0).sharedOffset := ⟨_, rfl⟩
  rw [← hB] at hone
  have hB128 : B % 128 = 0 := by have := st.isLt; have := q.isLt; omega
  have hlo : B ≤ a.loc.addr := by have := q.isLt; omega
  obtain ⟨v, hv⟩ : ∃ v, a.loc.addr = B + v := ⟨a.loc.addr - B, by omega⟩
  have hv4 : v % 4 = 0 := by omega
  -- the bytes of one element
  have hel : ∀ t t' : Nat, t / 2 = t' / 2 → t < 4 → t' < 4 →
      TensorSwizzle.offset .b128 B (v + t) % 128 / 2 =
        TensorSwizzle.offset .b128 B (v + t') % 128 / 2 ∧
      TensorSwizzle.offset .b128 B (v + t) / 128 = TensorSwizzle.offset .b128 B (v + t') / 128 := by
    intro t t' htt ht ht'
    have e1 : (v + t) / 128 = (v + t') / 128 := by omega
    have e2 : (v + t) / 16 = (v + t') / 16 := by omega
    have e3 := TensorSwizzle.offset_row .b128 B (v + t)
    have e4 := TensorSwizzle.offset_row .b128 B (v + t')
    have e5 := TensorSwizzle.offset_byte .b128 B (v + t)
    have e6 := TensorSwizzle.offset_byte .b128 B (v + t')
    have e7 : TensorSwizzle.offset .b128 B (v + t) / 16 =
        TensorSwizzle.offset .b128 B (v + t') / 16 := by
      have hdef : ∀ b, TensorSwizzle.offset .b128 B b = 128 * (b / 128) +
          16 * (TensorSwizzle.chunk .b128 B (b / 128) (BitVec.ofNat 3 (b / 16))).toNat +
          b % 16 := fun _ => rfl
      rw [hdef, hdef, e1, e2]
      omega
    constructor <;> omega
  have hsub : ∀ t : Nat, a.loc.addr + t - B = v + t := fun t => by omega
  refine ⟨inputVal p true (boxCoord org0 (TensorSwizzle.offset .b128 B (v + 0) % 128 / 2)
      (TensorSwizzle.offset .b128 B (v + 0) / 128)),
    inputVal p true (boxCoord org0 (TensorSwizzle.offset .b128 B (v + 2) % 128 / 2)
      (TensorSwizzle.offset .b128 B (v + 2) / 128)), fun t => ?_⟩
  have h1 := hone t
  rw [hsub] at h1
  have ht := t.isLt
  by_cases h2 : t.val < 2
  · obtain ⟨x1, x2⟩ := hel t.val 0 (by omega) ht (by omega)
    rw [x1, x2, show (v + t.val) % 2 = t.val % 2 by omega] at h1
    simpa only [h2, ↓reduceIte] using h1
  · obtain ⟨x1, x2⟩ := hel t.val 2 (by omega) ht (by omega)
    rw [x1, x2, show (v + t.val) % 2 = t.val % 2 by omega] at h1
    simpa only [h2, ↓reduceIte] using h1

end
end PTX.Kernels.TmlFa4Fwd.Proof
