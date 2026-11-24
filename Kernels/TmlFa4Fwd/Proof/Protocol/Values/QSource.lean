-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InputBytes
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Operands
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.InputBar
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Tma
import Kernels.TmlFa4Fwd.Proof.Lib.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Order
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.CopyOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Input
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Bytes
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Ordered
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Issue
import Kernels.TmlFa4Fwd.Proof.Protocol.Staging.Final
import Lemmas.Async.ReadReuse
import Lemmas.Tcgen05.MmaOperandObservations
import Lemmas.Tensor.BoxWrite
import Lemmas.Tensor.TensorCompleteConsistentRead

@[expose] public section

/-! # The sources of the Q operand bytes

The QK MMAs of stage `st` read the two boxes the elected loader lane loaded: element `(row, d)` is
element `(d mod 64, row)` of box `d / 64` (`q_copy_exists`). No other copy writes the byte, and the
final stores of the output staging follow the read, so the operand byte is the copy's (`q_operand`).
-/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm AsyncCopy PTX.MbarRing

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- **The copy of box `q` of Q stage `st`** of CTA `c`, at box origin `org`. -/
def QCp (p : Params) (L : Launch) (X : Execution) (c : Nat) (st q : Fin 2) (org : Fin 3 → Int)
    (i : EvId) : Prop :=
  ∃ pc al j mb, X.get i = some ⟨pc, .tensorIssue al (inputSpec p L c j org mb)⟩ ∧
    i.1 / L.block = c ∧ mb = obj L (c * L.block) (8 * st.val) ∧
    (Loader.inputSite j).sharedOffset = 3072 + 32768 * st.val + 16384 * q.val ∧
    (Loader.inputSite j).bias = false ∧
    ((X.tr i.1).take i.2).countP (issuesTo mb) = q.val

private theorem site_q : ∀ (j : Fin 14) (st q : Fin 2),
    (Loader.inputSite j).sharedOffset = 3072 + 32768 * st.val + 16384 * q.val →
      (Loader.inputSite j).bias = false := by decide

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The copies of a Q stage before a QK MMA**, notified. -/
theorem q_copy_exists {st u : Nat} {j : Fin 8} (hst : st < 2) (hR : Qk L X g k st u j)
    (q : Fin 2) : ∃ org i o, QCp p L X (g / L.block) ⟨st, hst⟩ q org i ∧ X.tensor i = some o ∧
      o.effects.notified = true ∧ ∃ pc al, X.get i = some ⟨pc, .tensorIssue al o.spec⟩ := by
  obtain ⟨pcm, da, db, hme⟩ := hR.issue
  have hgm := Frame.lt_of_get hX hme
  have hmma : X.MmaIssue (g, k) (128 * st) _ _ _ := ⟨pcm, hme⟩
  have hwm := (Tm.mma_qkpv hp hX hFw ⟨_, _, _, _, hmma⟩).1
  obtain ⟨cm, hin, -, hcm, hfull, -⟩ := qHandoff hp hX hFw (tmaBytes hp hX hFw) g hgm ⟨st, hst⟩
  have hcme : g = cm := hcm hmma ⟨hgm, rfl, hwm⟩
  subst hcme
  have hq := hR.q
  have hpoll : 0 + 1 ≤ okPolls (qF L g ⟨st, hst⟩) ((X.tr g).take k) := by
    show 1 ≤ okPolls (obj L g (8 * st)) _
    rw [show obj L g (8 * st) = Tm.bar L (g / L.block) (8 * st) from rfl, hq]
  obtain ⟨jw, pcw, par, acq, sc, hjk, hwe, hwo⟩ := nth_poll hpoll
  obtain ⟨i, pci, al, sp, he, hm, hcnt, -, hW⟩ := hfull hwe hwo q
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
  have hty := (tmaLane_in (X := X) hp g).1
  obtain ⟨hw, -⟩ := input_box hp hX hFw he
  have hm' : sp.mbar = obj L (tmaLane L X g) (8 * st) := by rw [obj_cta hty]; exact hm
  obtain ⟨-, -, jv, pcv, maskv, instv, -, hjv⟩ :=
    ld_tma_copy hp hX hFw hw (q_tmaOff ⟨st, hst⟩) he hm'
  obtain ⟨j', org, hs', hoff⟩ := ld_q_copy hp hX hFw hw
    (fun k pc mask inst ld hk => tmaLane_won hX hjv hk) ⟨st, hst⟩ he hm'
  have hmb : obj L (g / L.block * L.block) (8 * st) = obj L g (8 * st) :=
    obj_cta (by rw [hp.block]; omega) _
  rw [show obj L (tmaLane L X g) (8 * st) = qF L g ⟨st, hst⟩ by rw [obj_cta hty], hcnt] at hoff
  have hq2 := q.isLt
  have hoff' : (Loader.inputSite j').sharedOffset = 3072 + 32768 * st + 16384 * q.val := by
    rw [hoff]
    simp only
    omega
  refine ⟨org, (tmaLane L X g, i), o, ⟨pci, al, j', sp.mbar, ?_, hty, ?_, hoff',
    site_q j' ⟨st, hst⟩ q hoff', ?_⟩, ho, hn, pci, al, by rw [hos]; exact he⟩
  · rw [← hty, ← hs']
    exact he
  · rw [hmb]
    exact hm
  · simp only
    rw [hm, hcnt]
    omega

omit hp hX hFw in
/-- **A box element's byte is the stage element's.** -/
theorem q_writeLoc {c st d row z : Nat} {jj : Fin 14} {org : Fin 3 → Int} {mb : Loc}
    (hoff : (Loader.inputSite jj).sharedOffset = 3072 + 32768 * st + 16384 * (d / 64))
    (hrow : row < 128) (hz : z < 2) :
    TensorCopy.writeLoc (inputSpec p L c jj org mb) (d % 64) row z =
      some (blockLoc c (qBase L st) row d z) := by
  obtain ⟨m1, m2, m3, m4, -⟩ := input_map p jj
  have hf2 : (Loader.inputMap p (Loader.inputSite jj)).format.bytes = 2 := by rw [m3]; rfl
  unfold TensorCopy.writeLoc TensorTransfer.slotAt
  have hx : d % 64 < TensorTile.count (inputSpec p L c jj org mb).descriptor.box 0 :=
    lt_of_lt_of_eq (Nat.mod_lt _ (by decide)) m1.symm
  have hy : row < TensorTile.rows (inputSpec p L c jj org mb).descriptor.box :=
    lt_of_lt_of_eq hrow m2.symm
  have hk : z < (inputSpec p L c jj org mb).descriptor.format.bytes :=
    lt_of_lt_of_eq hz hf2.symm
  rw [dite_eq_left hx, dite_eq_left hy, dite_eq_left hk, Option.map_some]
  simp only [TensorBox.sharedLoc, TensorTile.sharedByte, TensorTile.linearByte,
    TensorTile.rowBytes]
  rw [show TensorTile.count (inputSpec p L c jj org mb).descriptor.box 0 = 64 from m1,
    show (inputSpec p L c jj org mb).descriptor.format.bytes = 2 from hf2,
    show (inputSpec p L c jj org mb).descriptor.swizzle = .b128 from m4]
  simp only [TensorTile.swizzleWidth, inputSpec, blockLoc, blockAddr, hoff, qBase]
  congr 2
  have e : max (64 * 2) 128 = 128 := by decide
  rw [e]
  have e1 : L.sharedBase + 3072 + 32768 * st + 16384 * (d / 64) =
      L.sharedBase + (3072 + 32768 * st + 16384 * (d / 64)) := by omega
  have e2 : row * 128 + d % 64 * 2 + z = 128 * row + 2 * (d % 64) + z := by omega
  rw [e1, e2]

/-- **The copy of a box of a Q stage is one.** -/
theorem QCp.unique {c : Nat} {st q : Fin 2} {org org' : Fin 3 → Int} {i i' : EvId}
    (h : QCp p L X c st q org i) (h' : QCp p L X c st q org' i') : org = org' := by
  obtain ⟨pc, al, j, mb, he, -, -, hoff, -⟩ := h
  obtain ⟨pc', al', j', mb', he', -, -, hoff', -⟩ := h'
  have hq := q.isLt
  have hs := st.isLt
  have e : (64 * q.val) / 64 = q.val := by omega
  have w := q_writeLoc (p := p) (L := L) (c := c) (st := st.val) (jj := j) (org := org) (mb := mb)
    (d := 64 * q.val) (row := 0)
    (z := 0) (by rw [hoff, e]) (by decide) (by decide)
  have w' := q_writeLoc (p := p) (L := L) (c := c) (st := st.val) (jj := j') (org := org')
    (mb := mb') (d := 64 * q.val) (row := 0)
    (z := 0) (by rw [hoff', e]) (by decide) (by decide)
  have hb := TensorCopy.box_offset_lt (R := 128) (base := qBase L st + 16384 * q.val)
    (x := 64 * q.val % 64) (y := 0) (byte := 0) (by omega) (by decide) (by decide)
  have hu := q_copy_unique hp hX hFw (i := i) (i' := i') he he' w w'
    (by simp only [blockAddr, qBase, e]; omega)
    (by simp only [blockAddr, qBase, e] at hb ⊢; omega)
  simp only [Ref.async.injEq] at hu
  rw [hu.1, he'] at he
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at he
  obtain ⟨-, -, hs'⟩ := he
  simp only [inputSpec, TensorCopy.Spec.mk.injEq, TensorBox.mk.injEq] at hs'
  exact (eq_of_heq hs'.1.2.2.1).symm

/-- **A Q operand byte is the copy's element's.** -/
theorem q_operand (hIn : InputsUnwritten p X) {st u row d z idx dd : Nat} {j : Fin 8}
    {s : OperandSpec} {acc : Bool} {mask : List Nat} {ops : AsyncCopy.MmaOperands} (hst : st < 2)
    (hR : Qk L X g k st u j) (hi : X.MmaIssue (g, k) dd s acc mask)
    (hops : X.async.mmaOperands (g, k) = some ops) (hrow : row < 128) (hd : d < 128) (hz : z < 2)
    (hbl : s.byteLoc .a idx = some (blockLoc (g / L.block) (qBase L st) row d z))
    {org : Fin 3 → Int} {i : EvId} {o : TensorCopy.Observation}
    (hC : QCp p L X (g / L.block) ⟨st, hst⟩ ⟨d / 64, by omega⟩ org i) (ho : X.tensor i = some o)
    (hn : o.effects.notified = true) (he : ∃ pc al, X.get i = some ⟨pc, .tensorIssue al o.spec⟩) :
    ops.a[idx]? = some (some ((biasValue (inputVal p false (boxCoord org (d % 64) row))).byteAt
      z)) := by
  obtain ⟨pc, al, jj, mb, hget, hic, hmb, hoff, hbias, hcnt⟩ := hC
  obtain ⟨pc', al', hget'⟩ := he
  have hspec : o.spec = inputSpec p L (g / L.block) jj org mb := by
    rw [hget] at hget'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hget'
    exact hget'.2.2.symm
  set l := blockLoc (g / L.block) (qBase L st) row d z with hl
  have hwl : TensorCopy.writeLoc o.spec (d % 64) row z = some l := by
    rw [hspec]
    exact q_writeLoc hoff hrow hz
  have hlo : L.sharedBase + 3072 + 32768 * st ≤ l.addr ∧
      l.addr < L.sharedBase + 3072 + 32768 * st + 32768 := by
    have hb := TensorCopy.box_offset_lt (R := 128) (base := qBase L st + 16384 * (d / 64))
      (x := d % 64) (y := row) (byte := z) (by omega) hrow hz
    simp only [hl, blockLoc, blockAddr]
    unfold qBase at hb ⊢
    constructor <;> omega
  obtain ⟨obs, hrd, hob⟩ := hX.tma.2.1.mma_read_exists (isB := false) hi hops hbl
  simp only [Bool.false_eq_true, ↓reduceIte] at hob
  have hcov : AsyncCovers X (g, k) (.mmaRead false idx) l := mma_covers hi hbl
  have hwr := input_written hp hX hIn ho hn hspec hwl
  rw [hbias] at hwr
  have hv := q_copy_read hp hX hFw (i := i) (by rw [← Prod.mk.eta (p := i)]; exact hget') hwl hR hst
    hcov rfl hlo.1 hlo.2
  have horder : ∀ w a bs, X.MemWrites w a bs → a.Covers l →
      w = .async i (.write (.load (d % 64) row z)) ∨
      modelCausality L X l w (.async i (.write (.load (d % 64) row z))) ∨
      modelCausality L X l (.async (g, k) (.mmaRead false idx)) w := by
    intro w a bs hw hc
    have hsp : a.loc.space = .shared := hc.1.symm
    have hcta : a.loc.cta = g / L.block := hc.2.1.symm
    obtain ⟨c1, c2, c3, c4⟩ := hc
    cases sh_intent hp hX hFw hw.intent hsp with
    | allocWr hw' h =>
      exfalso
      obtain ⟨hz, hs⟩ := h
      rw [hs] at c3 c4
      simp only at c3 c4
      omega
    | @statWr gg _ _ hw' h =>
      exfalso
      obtain ⟨hz, n, hn, hs⟩ := h
      rw [hs] at c3 c4
      have hst' : ∀ g, Softmax.stN L g ≤ 1 := fun g => by unfold Softmax.stN; split <;> omega
      have := hst' gg
      simp only at c3 c4
      omega
    | @fstWr y j a hw' hw1 st h =>
      right; right
      obtain ⟨pc', he⟩ : ∃ pc', X.get (y, j) = some ⟨pc', .wr a bs⟩ := by
        rcases hw with h | ⟨old, pc', h⟩
        · exact h
        · exact (noActualRmw hX ⟨pc', h⟩).elim
      obtain ⟨hz, q, hq, ww, hww, hloc⟩ := h
      exact mma_fst hp hX hFw hw' hw1 he rfl ⟨c1, c2, c3, c4⟩ ⟨_, _, _, _, hi⟩ (by
        rw [hloc] at hcta; exact hcta.symm) hcov
    | @rowCp y j pc' sp' hy he h =>
      exfalso
      obtain ⟨off, ho, hlo'⟩ := copy_slot h (l := l) ⟨c1, c2, c3, c4⟩
      have hadd := congrArg Loc.addr hlo'
      simp only at hadd
      omega
    | @tmaWr y j pcj alj spj x' y' z' a hwj hej hzz hlj hcj jj' hlo' hhi' =>
      left
      have hla : a.loc = l := by
        have h1 : a.loc.addr = l.addr := by omega
        calc a.loc = ⟨a.loc.space, a.loc.cta, a.loc.addr⟩ := rfl
          _ = ⟨l.space, l.cta, l.addr⟩ := by rw [← c1, ← c2, h1]
          _ = l := rfl
      rw [hla] at hlj
      exact q_copy_unique hp hX hFw hej hget' hlj hwl (by omega) (by omega)
  have hval := read_byte_of_ordered_reuse hX hrd.memReads (k := 0) (by exact Nat.zero_lt_succ 0)
    hwr (by simp [Acc.Covers, Loc.InRange, Loc.at])
    (by simpa only [Loc.at, Nat.add_zero] using hv)
    (by simpa only [Loc.at, Nat.add_zero] using horder)
  simp only [Loc.at, Nat.add_zero, List.getElem?_cons_zero, Option.some.injEq] at hval
  rw [hob, hval]
  simp [wbyte]

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
